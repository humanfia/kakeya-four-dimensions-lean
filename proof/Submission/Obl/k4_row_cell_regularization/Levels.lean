import Mathlib

/-!
# Weight levels of the direction bins

The direction bins of the incidence table carry palette weights `w d`.  Grouping the bins into
levels of ratio `lam` (`lam ^ (-(k+1)) < w d ≤ lam ^ (-k)`), one level carries a fixed
proportion of the incidence mass, as soon as the bins of weight at most `lam ^ (-J)` carry at
most half of it (`exists_weight_level`).  On one level the weights are comparable, which gives
the per-cell mass bound against the number of selected bins and the interval cap of the uniform
counting law on them (`level_caps`); the near-direction cap is the interval cap at the radius
`2 / R` (`near_cap_of_interval_cap`).
-/

open scoped BigOperators

namespace Submission.Obl.k4_row_cell_regularization

/-- One level of ratio `lam` carries a `1 / (2 J)` part of the mass, when the bins of weight at
most `lam ^ (-J)` carry at most half of it. -/
theorem exists_weight_level {ι X : Type*} (B : Finset ι) (P : Finset X)
    (m : X → ι → ℝ) (w : ι → ℝ) {A lam M : ℝ} (J : ℕ) (hJ : 0 < J)
    (hA : 0 ≤ A) (hlam : 1 < lam) (hw1 : ∀ d ∈ B, w d ≤ 1)
    (hmw : ∀ p ∈ P, ∀ d ∈ B, m p d ≤ A * w d)
    (htot : M ≤ ∑ p ∈ P, ∑ d ∈ B, m p d)
    (hlow : (B.card : ℝ) * (P.card : ℝ) * A * (lam ^ J)⁻¹ ≤ M / 2) :
    ∃ D ⊆ B, ∃ θ : ℝ, 0 < θ ∧ (∀ d ∈ D, θ < w d ∧ w d ≤ lam * θ) ∧
      M / (2 * J) ≤ ∑ p ∈ P, ∑ d ∈ D, m p d := by
  classical
  set f : ι → ℝ := fun d => ∑ p ∈ P, m p d with hf
  have hswap : ∀ D : Finset ι, ∑ p ∈ P, ∑ d ∈ D, m p d = ∑ d ∈ D, f d :=
    fun D => Finset.sum_comm
  have hlam0 : 0 < lam := lt_trans zero_lt_one hlam
  let lev : ι → ℕ := fun d => Nat.findGreatest (fun k => w d ≤ (lam ^ k)⁻¹) J
  have hlevJ : ∀ d, lev d ≤ J := fun d => Nat.findGreatest_le J
  have hlev_spec : ∀ d ∈ B, w d ≤ (lam ^ lev d)⁻¹ := by
    intro d hd
    exact Nat.findGreatest_spec (P := fun k => w d ≤ (lam ^ k)⁻¹) (Nat.zero_le J)
      (by simpa using hw1 d hd)
  have hlev_gt : ∀ d, lev d < J → (lam ^ (lev d + 1))⁻¹ < w d := by
    intro d hd
    exact lt_of_not_ge (Nat.findGreatest_is_greatest (Nat.lt_succ_self _) hd)
  -- the mass of one bin is at most `|P| A w d`
  have hfw : ∀ d ∈ B, f d ≤ (P.card : ℝ) * A * w d := by
    intro d hd
    calc f d = ∑ p ∈ P, m p d := rfl
      _ ≤ ∑ _p ∈ P, A * w d := Finset.sum_le_sum fun p hp => hmw p hp d hd
      _ = (P.card : ℝ) * A * w d := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  -- split the bins by level
  have hmaps : ∀ d ∈ B, lev d ∈ Finset.range (J + 1) :=
    fun d _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (hlevJ d))
  have hsplit := Finset.sum_fiberwise_of_maps_to hmaps f
  rw [Finset.sum_range_succ] at hsplit
  -- the lowest level is small
  have hlowJ : ∑ d ∈ B with lev d = J, f d ≤ M / 2 := by
    calc ∑ d ∈ B with lev d = J, f d
        ≤ ∑ d ∈ B with lev d = J, (P.card : ℝ) * A * (lam ^ J)⁻¹ := by
          apply Finset.sum_le_sum
          intro d hd
          obtain ⟨hdB, hdJ⟩ := Finset.mem_filter.mp hd
          have hw := hlev_spec d hdB
          rw [hdJ] at hw
          exact (hfw d hdB).trans
            (mul_le_mul_of_nonneg_left hw (mul_nonneg (Nat.cast_nonneg _) hA))
      _ = ((B.filter (fun d => lev d = J)).card : ℝ) * ((P.card : ℝ) * A * (lam ^ J)⁻¹) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (B.card : ℝ) * ((P.card : ℝ) * A * (lam ^ J)⁻¹) := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast Finset.card_filter_le _ _
          · have : 0 ≤ (lam ^ J)⁻¹ := inv_nonneg.mpr (pow_nonneg hlam0.le J)
            positivity
      _ = (B.card : ℝ) * (P.card : ℝ) * A * (lam ^ J)⁻¹ := by ring
      _ ≤ M / 2 := hlow
  have hupper : M / 2 ≤ ∑ k ∈ Finset.range J, ∑ d ∈ B with lev d = k, f d := by
    have := htot
    rw [hswap B, ← hsplit] at this
    linarith
  -- pigeonhole among the remaining levels
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
  have hconst : ∑ _k ∈ Finset.range J, M / (2 * J) ≤
      ∑ k ∈ Finset.range J, ∑ d ∈ B with lev d = k, f d := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc (J : ℝ) * (M / (2 * J)) = M / 2 := by field_simp
      _ ≤ _ := hupper
  obtain ⟨k, hk, hkmass⟩ := Finset.exists_le_of_sum_le
    (Finset.nonempty_range_iff.mpr (Nat.pos_iff_ne_zero.mp hJ)) hconst
  have hkJ : k < J := Finset.mem_range.mp hk
  refine ⟨B.filter (fun d => lev d = k), Finset.filter_subset _ _, (lam ^ (k + 1))⁻¹,
    inv_pos.mpr (pow_pos hlam0 _), ?_, ?_⟩
  · intro d hd
    obtain ⟨hdB, hdk⟩ := Finset.mem_filter.mp hd
    constructor
    · have := hlev_gt d (hdk ▸ hkJ)
      rwa [hdk] at this
    · have hw := hlev_spec d hdB
      rw [hdk] at hw
      calc w d ≤ (lam ^ k)⁻¹ := hw
        _ = lam * (lam ^ (k + 1))⁻¹ := by
          rw [pow_succ]
          field_simp
  · rw [hswap]
    exact hkmass

/-- On one level the masses are bounded against the number of bins, and the uniform counting
law on the bins inherits the interval cap of the weights. -/
theorem level_caps {ι X : Type*} (D : Finset ι) (P : Finset X) (m : X → ι → ℝ)
    (w : ι → ℝ) (u : ι → ℝ) {A lam θ Pi M Lam S h : ℝ}
    (hθ : 0 < θ) (hlev : ∀ d ∈ D, θ < w d ∧ w d ≤ lam * θ)
    (hsum : ∑ d ∈ D, w d ≤ 1)
    (hcap : ∀ x r : ℝ, h ≤ r → r ≤ 1 →
      ∑ d ∈ D with u d ∈ Set.Icc x (x + r), w d ≤ Lam * r ^ S)
    (hmw : ∀ p ∈ P, ∀ d ∈ D, m p d ≤ A * w d) (hA : 0 ≤ A)
    (hP : (P.card : ℝ) ≤ Pi)
    (hM : 0 < M) (htot : M ≤ ∑ p ∈ P, ∑ d ∈ D, m p d) :
    (∀ p ∈ P, ∀ d ∈ D, m p d ≤ A * lam / (D.card : ℝ)) ∧
    (∀ x r : ℝ, h ≤ r → r ≤ 1 →
      ((D.filter (fun d => u d ∈ Set.Icc x (x + r))).card : ℝ) ≤
        (Lam * Pi * A * lam / M) * r ^ S * (D.card : ℝ)) := by
  classical
  -- `D` is nonempty
  have hDne : D.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty.mp hne] at htot
    simp only [Finset.sum_empty, Finset.sum_const_zero] at htot
    linarith
  obtain ⟨d₀, hd₀⟩ := hDne
  have hlam : 0 ≤ lam := by
    have h1 := hlev d₀ hd₀
    have : θ < lam * θ := lt_of_lt_of_le h1.1 h1.2
    by_contra hneg
    have hneg' : lam < 0 := lt_of_not_ge hneg
    nlinarith
  have hDpos : (0 : ℝ) < D.card := by exact_mod_cast Finset.card_pos.mpr ⟨d₀, hd₀⟩
  -- `|D| θ ≤ 1`
  have hθD : (D.card : ℝ) * θ ≤ 1 := by
    have := Finset.card_nsmul_le_sum D w θ fun d hd => (hlev d hd).1.le
    rw [nsmul_eq_mul] at this
    linarith
  have hPi : 0 ≤ Pi := (Nat.cast_nonneg _).trans hP
  refine ⟨?_, ?_⟩
  · intro p hp d hd
    calc m p d ≤ A * w d := hmw p hp d hd
      _ ≤ A * (lam * θ) := mul_le_mul_of_nonneg_left (hlev d hd).2 hA
      _ ≤ A * lam / (D.card : ℝ) := by
        rw [le_div_iff₀ hDpos]
        have := mul_le_mul_of_nonneg_left hθD (mul_nonneg hA hlam)
        nlinarith
  · intro x r hr hr1
    set Dx := D.filter (fun d => u d ∈ Set.Icc x (x + r))
    -- `|Dx| θ ≤ Lam r^S`
    have hDx : (Dx.card : ℝ) * θ ≤ Lam * r ^ S := by
      have := Finset.card_nsmul_le_sum Dx w θ fun d hd => (hlev d (Finset.mem_filter.mp hd).1).1.le
      rw [nsmul_eq_mul] at this
      exact this.trans (hcap x r hr hr1)
    -- `M ≤ |P| |D| A lam θ`
    have hMθ : M ≤ Pi * (D.card : ℝ) * A * lam * θ := by
      calc M ≤ ∑ p ∈ P, ∑ d ∈ D, m p d := htot
        _ ≤ ∑ _p ∈ P, ∑ _d ∈ D, A * (lam * θ) := by
          apply Finset.sum_le_sum
          intro p hp
          apply Finset.sum_le_sum
          intro d hd
          exact (hmw p hp d hd).trans (mul_le_mul_of_nonneg_left (hlev d hd).2 hA)
        _ = (P.card : ℝ) * (D.card : ℝ) * A * lam * θ := by
          simp only [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ Pi * (D.card : ℝ) * A * lam * θ := by
          have : 0 ≤ (D.card : ℝ) * A * lam * θ := by positivity
          nlinarith
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hM]
    have hDx0 : (0 : ℝ) ≤ Dx.card := Nat.cast_nonneg _
    calc (Dx.card : ℝ) * M ≤ (Dx.card : ℝ) * (Pi * (D.card : ℝ) * A * lam * θ) :=
          mul_le_mul_of_nonneg_left hMθ hDx0
      _ = ((Dx.card : ℝ) * θ) * (Pi * (D.card : ℝ) * A * lam) := by ring
      _ ≤ (Lam * r ^ S) * (Pi * (D.card : ℝ) * A * lam) := by
          apply mul_le_mul_of_nonneg_right hDx
          positivity
      _ = Lam * Pi * A * lam * r ^ S * (D.card : ℝ) := by ring

/-- The near-direction cap is the interval cap at the radius `2 / R`. -/
theorem near_cap_of_interval_cap {ι : Type*} (D : Finset ι) (u : ι → ℝ) {K S h R : ℝ}
    (hcap : ∀ x r : ℝ, h ≤ r → r ≤ 1 →
      ((D.filter (fun d => u d ∈ Set.Icc x (x + r))).card : ℝ) ≤ K * r ^ S * (D.card : ℝ))
    (hR : 2 ≤ R) (hRh : h ≤ 2 / R) :
    ∀ d₀ ∈ D, ((D.filter (fun d => |u d - u d₀| < 1 / R)).card : ℝ) ≤
      K * (2 / R) ^ S * (D.card : ℝ) := by
  classical
  intro d₀ _
  have hRpos : 0 < R := by linarith
  have hsub : D.filter (fun d => |u d - u d₀| < 1 / R) ⊆
      D.filter (fun d => u d ∈ Set.Icc (u d₀ - 1 / R) (u d₀ - 1 / R + 2 / R)) := by
    intro d hd
    obtain ⟨hdD, hd⟩ := Finset.mem_filter.mp hd
    refine Finset.mem_filter.mpr ⟨hdD, ?_⟩
    rw [abs_lt] at hd
    constructor
    · linarith
    · have : u d₀ - 1 / R + 2 / R = u d₀ + 1 / R := by ring
      rw [this]
      linarith
  have h21 : 2 / R ≤ 1 := by rw [div_le_one hRpos]; exact hR
  calc ((D.filter (fun d => |u d - u d₀| < 1 / R)).card : ℝ)
      ≤ ((D.filter (fun d => u d ∈ Set.Icc (u d₀ - 1 / R) (u d₀ - 1 / R + 2 / R))).card : ℝ) :=
        by exact_mod_cast Finset.card_le_card hsub
    _ ≤ K * (2 / R) ^ S * (D.card : ℝ) := hcap _ _ hRh h21

end Submission.Obl.k4_row_cell_regularization
