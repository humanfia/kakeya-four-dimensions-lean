-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.Profile.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

/-!
# Choosing the two scales of (B) from the cell-count profile

x0318's argument (o070 thread, 14:40Z), with one step made explicit. For a regularized aligned
family on the radii `ρ_k = δ^(k/N)`, let `G k = log_{1/δ} #(occupied cells at level k) - 2k/N`.
Then `G 0 = 0`, `G k ≥ -ζ` (global Frostman) and the steps are at most `2/N`. Either the profile
never drops by more than `ξ` (sticky) or there are levels `i₀ < j₂` such that

* `G l ≥ G j₂` for every `l ≥ i₀` (Katz–Tao between `ρ_{i₀}` and `ρ_{j₂}`, Frostman below),
* `G j₂ ≥ G i₀ - ζ₂` (the `τ`-tubes fill the `ρ`-tubes), and
* `(j₂ - i₀)/N ≥ ξ/4` (separated scales, `ζ₁ = ξ/4`).

The explicit step: the chosen `i₀` is the last level before the drop with `G i₀ ≤ v + ζ₂/2`
(`v` the minimum after the drop). Its successor lies above `v + ζ₂/2`, and the steps are at most
`2/N ≤ ζ₂/2`, so `G i₀ ≥ v`.
-/

namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy

theorem profile_dichotomy {N : ℕ} (hN : 0 < N) {G : ℕ → ℝ} {ζ ζ₂ ξ : ℝ}
    (h0 : G 0 = 0) (hlow : ∀ k ≤ N, -ζ ≤ G k)
    (hstep : ∀ k < N, |G (k + 1) - G k| ≤ 2 / N)
    (hζ : ζ ≤ ζ₂ / 2) (hζ₂ξ : ζ₂ ≤ ξ) (hNζ₂ : 2 / (N : ℝ) ≤ ζ₂ / 2) :
    (∀ i j, i ≤ j → j ≤ N → G i - ξ ≤ G j) ∨
      ∃ i₀ j₂, i₀ < j₂ ∧ j₂ ≤ N ∧ (∀ l, i₀ ≤ l → l ≤ N → G j₂ ≤ G l) ∧
        G i₀ - ζ₂ ≤ G j₂ ∧ ξ / 4 ≤ ((j₂ : ℝ) - i₀) / N := by
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h2N : (0 : ℝ) < 2 / N := by positivity
  have hζ₂pos : 0 < ζ₂ := by linarith
  by_cases hst : ∀ i j, i ≤ j → j ≤ N → G i - ξ ≤ G j
  · exact Or.inl hst
  right
  push Not at hst
  obtain ⟨i₁, j₁, hij, hjN, hdrop⟩ := hst
  -- the minimum of `G` on `[i₁, N]`
  have hne : (Finset.Icc i₁ N).Nonempty := ⟨i₁, Finset.mem_Icc.2 ⟨le_rfl, hij.trans hjN⟩⟩
  obtain ⟨j₂, hj₂mem, hj₂min⟩ := Finset.exists_min_image (Finset.Icc i₁ N) G hne
  obtain ⟨hi₁j₂, hj₂N⟩ := Finset.mem_Icc.1 hj₂mem
  set v := G j₂ with hvdef
  have hvmin : ∀ l, i₁ ≤ l → l ≤ N → v ≤ G l := fun l h1 h2 =>
    hj₂min l (Finset.mem_Icc.2 ⟨h1, h2⟩)
  have hvj₁ : v ≤ G j₁ := hvmin j₁ hij hjN
  have hGi₁ : v + ξ < G i₁ := by linarith
  have hi₁N : i₁ ≤ N := hij.trans hjN
  have hv_low : -ζ ≤ v := hlow j₂ hj₂N
  -- `i₀`: the last level `≤ i₁` with `G i₀ ≤ v + ζ₂/2`
  have hP0 : G 0 ≤ v + ζ₂ / 2 := by rw [h0]; linarith
  set i₀ := Nat.findGreatest (fun l => G l ≤ v + ζ₂ / 2) i₁ with hi₀def
  have hi₀le : i₀ ≤ i₁ := Nat.findGreatest_le i₁
  have hPi₀ : G i₀ ≤ v + ζ₂ / 2 :=
    Nat.findGreatest_spec (P := fun l => G l ≤ v + ζ₂ / 2) (Nat.zero_le i₁) hP0
  have hafter : ∀ l, i₀ < l → l ≤ i₁ → v + ζ₂ / 2 < G l := by
    intro l hl1 hl2
    by_contra h
    push Not at h
    have := Nat.le_findGreatest (P := fun l => G l ≤ v + ζ₂ / 2) hl2 h
    omega
  have hi₀lt : i₀ < i₁ := by
    rcases Nat.lt_or_eq_of_le hi₀le with h | h
    · exact h
    · exfalso
      rw [h] at hPi₀
      linarith
  -- the explicit step: `G i₀ ≥ v`
  have hsucc : v + ζ₂ / 2 < G (i₀ + 1) := hafter (i₀ + 1) (by omega) (by omega)
  have hstep₀ := hstep i₀ (by omega)
  have hGi₀ : v ≤ G i₀ := by
    have := (abs_le.1 hstep₀).2
    linarith
  -- the separation of the scales
  have hsep : ξ - ζ₂ / 2 ≤ ((i₁ : ℝ) - i₀) * (2 / N) := by
    -- telescoping: `G i₁ - G i₀ ≤ (i₁ - i₀) * (2/N)`
    have htel : ∀ d, i₀ + d ≤ N → G (i₀ + d) - G i₀ ≤ (d : ℝ) * (2 / N) := by
      intro d
      induction d with
      | zero => intro _; simp
      | succ d ih =>
        intro hd
        have h1 := ih (by omega)
        have h2 := (abs_le.1 (hstep (i₀ + d) (by omega))).2
        push_cast
        have e : i₀ + (d + 1) = i₀ + d + 1 := by ring
        rw [e]
        linarith
    have := htel (i₁ - i₀) (by omega)
    rw [show i₀ + (i₁ - i₀) = i₁ by omega, Nat.cast_sub hi₀le] at this
    linarith
  refine ⟨i₀, j₂, by omega, hj₂N, fun l hl1 hl2 => ?_, by linarith, ?_⟩
  · rcases le_or_gt l i₁ with h | h
    · rcases Nat.lt_or_eq_of_le hl1 with h' | h'
      · have := hafter l h' h; linarith
      · rw [← h']; exact hGi₀
    · exact hvmin l h.le hl2
  · have hj₂i₀ : ((i₁ : ℝ) - i₀) ≤ (j₂ : ℝ) - i₀ := by
      have : (i₁ : ℝ) ≤ j₂ := by exact_mod_cast hi₁j₂
      linarith
    rw [le_div_iff₀ hNpos]
    have h2 : ((i₁ : ℝ) - i₀) * (2 / N) = 2 * ((i₁ : ℝ) - i₀) / N := by ring
    rw [h2, le_div_iff₀ hNpos] at hsep
    nlinarith

/-- `profile_dichotomy` with an arbitrary UPWARD step bound `s` (only `G (k+1) - G k ≤ s` is
used; x0338 observed that 6-coordinate cells give `s ≈ 4/N + o(1)` rather than `2/N`). Needs
`s ≤ ζ₂/2`; the separation becomes `ξ/2 ≤ (j₂ - i₀) s`. -/
theorem profile_dichotomy_step {N : ℕ} {G : ℕ → ℝ} {ζ ζ₂ ξ s : ℝ}
    (h0 : G 0 = 0) (hlow : ∀ k ≤ N, -ζ ≤ G k) (hstep : ∀ k < N, G (k + 1) - G k ≤ s)
    (hζ : ζ ≤ ζ₂ / 2) (hζ₂ξ : ζ₂ ≤ ξ) (hsζ₂ : s ≤ ζ₂ / 2) (hs : 0 < s) :
    (∀ i j, i ≤ j → j ≤ N → G i - ξ ≤ G j) ∨
      ∃ i₀ j₂, i₀ < j₂ ∧ j₂ ≤ N ∧ (∀ l, i₀ ≤ l → l ≤ N → G j₂ ≤ G l) ∧
        G i₀ - ζ₂ ≤ G j₂ ∧ ξ / 2 ≤ ((j₂ : ℝ) - i₀) * s := by
  classical
  have hζ₂pos : 0 < ζ₂ := by linarith
  by_cases hst : ∀ i j, i ≤ j → j ≤ N → G i - ξ ≤ G j
  · exact Or.inl hst
  right
  push Not at hst
  obtain ⟨i₁, j₁, hij, hjN, hdrop⟩ := hst
  have hne : (Finset.Icc i₁ N).Nonempty := ⟨i₁, Finset.mem_Icc.2 ⟨le_rfl, hij.trans hjN⟩⟩
  obtain ⟨j₂, hj₂mem, hj₂min⟩ := Finset.exists_min_image (Finset.Icc i₁ N) G hne
  obtain ⟨hi₁j₂, hj₂N⟩ := Finset.mem_Icc.1 hj₂mem
  set v := G j₂ with hvdef
  have hvmin : ∀ l, i₁ ≤ l → l ≤ N → v ≤ G l := fun l h1 h2 =>
    hj₂min l (Finset.mem_Icc.2 ⟨h1, h2⟩)
  have hvj₁ : v ≤ G j₁ := hvmin j₁ hij hjN
  have hGi₁ : v + ξ < G i₁ := by linarith
  have hv_low : -ζ ≤ v := hlow j₂ hj₂N
  have hP0 : G 0 ≤ v + ζ₂ / 2 := by rw [h0]; linarith
  set i₀ := Nat.findGreatest (fun l => G l ≤ v + ζ₂ / 2) i₁ with hi₀def
  have hi₀le : i₀ ≤ i₁ := Nat.findGreatest_le i₁
  have hPi₀ : G i₀ ≤ v + ζ₂ / 2 :=
    Nat.findGreatest_spec (P := fun l => G l ≤ v + ζ₂ / 2) (Nat.zero_le i₁) hP0
  have hafter : ∀ l, i₀ < l → l ≤ i₁ → v + ζ₂ / 2 < G l := by
    intro l hl1 hl2
    by_contra h
    push Not at h
    have := Nat.le_findGreatest (P := fun l => G l ≤ v + ζ₂ / 2) hl2 h
    omega
  have hi₀lt : i₀ < i₁ := by
    rcases Nat.lt_or_eq_of_le hi₀le with h | h
    · exact h
    · exfalso
      rw [h] at hPi₀
      linarith
  have hsucc : v + ζ₂ / 2 < G (i₀ + 1) := hafter (i₀ + 1) (by omega) (by omega)
  have hGi₀ : v ≤ G i₀ := by
    have := hstep i₀ (by omega)
    linarith
  have htel : ∀ d, i₀ + d ≤ N → G (i₀ + d) - G i₀ ≤ (d : ℝ) * s := by
    intro d
    induction d with
    | zero => intro _; simp
    | succ d ih =>
      intro hd
      have h1 := ih (by omega)
      have h2 := hstep (i₀ + d) (by omega)
      push_cast
      have e : i₀ + (d + 1) = i₀ + d + 1 := by ring
      rw [e]
      linarith
  have hsep : ξ - ζ₂ / 2 ≤ ((i₁ : ℝ) - i₀) * s := by
    have := htel (i₁ - i₀) (by omega)
    rw [show i₀ + (i₁ - i₀) = i₁ by omega, Nat.cast_sub hi₀le] at this
    linarith
  refine ⟨i₀, j₂, by omega, hj₂N, fun l hl1 hl2 => ?_, by linarith, ?_⟩
  · rcases le_or_gt l i₁ with h | h
    · rcases Nat.lt_or_eq_of_le hl1 with h' | h'
      · have := hafter l h' h; linarith
      · rw [← h']; exact hGi₀
    · exact hvmin l h.le hl2
  · have hj₂i₀ : ((i₁ : ℝ) - i₀) ≤ (j₂ : ℝ) - i₀ := by
      have : (i₁ : ℝ) ≤ j₂ := by exact_mod_cast hi₁j₂
      linarith
    have : ((i₁ : ℝ) - i₀) * s ≤ ((j₂ : ℝ) - i₀) * s :=
      mul_le_mul_of_nonneg_right hj₂i₀ hs.le
    linarith

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy
