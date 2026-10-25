import Submission.Obl.k4_scalar_candidate_original_return.Core.Defs

/-!
# Diagonal choice of a slowly growing menu, and menu coverage of compact ranges
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

open Filter

set_option linter.unusedVariables false in
/-- If every fixed `J` eventually satisfies a property that is antitone in `J` and holds
for `J = 0`, then a sequence `J k → ∞` satisfies it at every stage.
(Monotonicity is not needed: the chosen index always meets its own threshold.) -/
theorem exists_diagonal {P : ℕ → ℕ → Prop} (h0 : ∀ k, P 0 k)
    (hmono : ∀ J J' k, J' ≤ J → P J k → P J' k)
    (hev : ∀ J, ∀ᶠ k in atTop, P J k) :
    ∃ Jk : ℕ → ℕ, Tendsto Jk atTop atTop ∧ ∀ k, P (Jk k) k := by
  classical
  choose N hN using fun J => Filter.eventually_atTop.mp (hev J)
  let M : ℕ → ℕ := fun J => ∑ J' ∈ Finset.range (J + 1), N J'
  have hNM : ∀ J, N J ≤ M J := fun J =>
    Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _) (Finset.self_mem_range_succ J)
  refine ⟨fun k => Nat.findGreatest (fun J => M J ≤ k) k, ?_, ?_⟩
  · rw [Filter.tendsto_atTop_atTop]
    intro J₀
    refine ⟨max J₀ (M J₀), fun k hk => ?_⟩
    exact Nat.le_findGreatest (le_of_max_le_left hk) (le_of_max_le_right hk)
  · intro k
    show P (Nat.findGreatest (fun J => M J ≤ k) k) k
    by_cases hz : Nat.findGreatest (fun J => M J ≤ k) k = 0
    · rw [hz]
      exact h0 k
    · have hspec : M (Nat.findGreatest (fun J => M J ≤ k) k) ≤ k :=
        Nat.findGreatest_of_ne_zero (P := fun J => M J ≤ k) rfl hz
      exact hN _ k ((hNM _).trans hspec)

private lemma pair_le_pair {a₁ a₂ b₁ b₂ : ℕ} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
    Nat.pair a₁ b₁ ≤ Nat.pair a₂ b₂ := by
  calc Nat.pair a₁ b₁ ≤ Nat.pair a₂ b₁ := by
        rcases ha.lt_or_eq with h | h
        · exact (Nat.pair_lt_pair_left b₁ h).le
        · rw [h]
    _ ≤ Nat.pair a₂ b₂ := by
        rcases hb.lt_or_eq with h | h
        · exact (Nat.pair_lt_pair_right a₂ h).le
        · rw [h]

private lemma menu_pair (m a b R : ℕ) :
    menu (Nat.pair m (Nat.pair a (Nat.pair b R))) =
      ⟨(a : ℝ) / ((m : ℝ) + 1), (b : ℝ) / ((m : ℝ) + 1), R⟩ := by
  simp only [menu, Nat.unpair_pair]

/-- Floor approximation from below at mesh `1/q`. -/
private lemma floor_div_bounds {s q : ℝ} (hs : 0 ≤ s) (hq : 0 < q) :
    ((⌊s * q⌋₊ : ℕ) : ℝ) / q ≤ s ∧ s - 1 / q < ((⌊s * q⌋₊ : ℕ) : ℝ) / q := by
  have h1 : ((⌊s * q⌋₊ : ℕ) : ℝ) ≤ s * q := Nat.floor_le (by positivity)
  have h2 : s * q < ((⌊s * q⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  constructor
  · rw [div_le_iff₀ hq]; exact h1
  · have h3 : s < (((⌊s * q⌋₊ : ℕ) : ℝ) + 1) / q := by rw [lt_div_iff₀ hq]; exact h2
    have heq : (((⌊s * q⌋₊ : ℕ) : ℝ) + 1) / q = ((⌊s * q⌋₊ : ℕ) : ℝ) / q + 1 / q := by ring
    linarith

/-- Every candidate depth and gain in a compact positive range is matched, with the
scenario slack `θ c₀`, by one of finitely many menu scenarios. -/
theorem menu_cover (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (R : ℝ) (hR : 1 < R) :
    ∃ J : ℕ, ∀ s c : ℝ, R⁻¹ ≤ s → s ≤ R → R⁻¹ ≤ c → c ≤ R →
      ∃ n < J, 0 < (menu n).s₀ ∧ 0 < (menu n).c₀ ∧
        |s - (menu n).s₀| ≤ θ * (menu n).c₀ / 4 ∧ |s - (menu n).s₀| ≤ (menu n).s₀ / 2 ∧
        |c - (menu n).c₀| ≤ θ * (menu n).c₀ / 4 ∧ R ≤ ((menu n).R : ℝ) ∧
        θ / (4 * R) ≤ θ * (menu n).c₀ / 2 := by
  classical
  have hRpos : 0 < R := by linarith
  set m : ℕ := ⌈8 * R / θ⌉₊ with hm
  set q : ℝ := (m : ℝ) + 1 with hq
  have hqpos : 0 < q := by positivity
  have hq_gt : 8 * R / θ < q := by
    have := Nat.le_ceil (8 * R / θ)
    rw [hq]; linarith
  -- the mesh `1/q` is below `θ w`, where `w = 1/(8R)`
  set w : ℝ := 1 / (8 * R) with hw
  have hwpos : 0 < w := by positivity
  have hRinv : R⁻¹ = 8 * w := by rw [hw]; field_simp
  have hu : 1 / q < θ * w := by
    rw [hw, mul_one_div, div_lt_div_iff₀ hqpos (by positivity)]
    have := (div_lt_iff₀ hθ).mp hq_gt
    linarith
  have hθw : θ * w ≤ w := by nlinarith
  set A : ℕ := ⌊R * q⌋₊
  set R' : ℕ := ⌈R⌉₊
  refine ⟨Nat.pair m (Nat.pair A (Nat.pair A R')) + 1, ?_⟩
  intro s c hs1 hs2 hc1 hc2
  have hs0 : 0 ≤ s := le_trans (by positivity) hs1
  have hc0 : 0 ≤ c := le_trans (by positivity) hc1
  obtain ⟨hsle, hsgt⟩ := floor_div_bounds hs0 hqpos
  obtain ⟨hcle, hcgt⟩ := floor_div_bounds hc0 hqpos
  refine ⟨Nat.pair m (Nat.pair ⌊s * q⌋₊ (Nat.pair ⌊c * q⌋₊ R')), ?_, ?_⟩
  · apply Nat.lt_succ_of_le
    have haA : ⌊s * q⌋₊ ≤ A := Nat.floor_le_floor (mul_le_mul_of_nonneg_right hs2 hqpos.le)
    have hbA : ⌊c * q⌋₊ ≤ A := Nat.floor_le_floor (mul_le_mul_of_nonneg_right hc2 hqpos.le)
    exact pair_le_pair le_rfl (pair_le_pair haA (pair_le_pair hbA le_rfl))
  · rw [menu_pair]
    simp only
    rw [← hq]
    set s₀ : ℝ := ((⌊s * q⌋₊ : ℕ) : ℝ) / q
    set c₀ : ℝ := ((⌊c * q⌋₊ : ℕ) : ℝ) / q
    rw [hRinv] at hs1 hc1
    have hs₀ : 7 * w < s₀ := by linarith
    have hc₀ : 7 * w < c₀ := by linarith
    have habs_s : |s - s₀| < θ * w := by
      rw [abs_of_nonneg (by linarith)]; linarith
    have habs_c : |c - c₀| < θ * w := by
      rw [abs_of_nonneg (by linarith)]; linarith
    have hθc : θ * w ≤ θ * c₀ / 4 := by nlinarith
    refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith,
      Nat.le_ceil R, ?_⟩
    have h4R : θ / (4 * R) = 2 * (θ * w) := by rw [hw]; field_simp; ring
    rw [h4R]
    nlinarith

end Submission.Obl.k4_scalar_candidate_original_return
