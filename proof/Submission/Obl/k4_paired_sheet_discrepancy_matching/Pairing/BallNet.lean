/- Adapted from this LOT tree, o114/x0680 commit133cc8c, Submission/Obl/k4_terminal_representative_atlas/Pairing/BallNet.lean.
Existing attribution to o156/x0531,x0524,x0575 and accepted imports is retained below. -/

/- Adapted from this LOT tree, o156, session x0524 branch c7cfd90,
Submission/Obl/k4_terminal_local_sheet_pairing/BallNet.lean. Original authorship/provenance is preserved below.
Namespace and imports adjusted for o114. -/

import Mathlib

/-! A measurable grid net for base points: each point is assigned the nearest grid point
of spacing `h`, at distance at most `h`; points of norm at most `R` use finitely many
labels. -/

namespace Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

open MeasureTheory Set

/-- The grid label of a base point at spacing `h`. -/
noncomputable def gridLabel (h : ℝ) (z : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℤ :=
  fun i => round (z i / h)

/-- The grid center of a label. -/
noncomputable def gridCenter (h : ℝ) (n : Fin 3 → ℤ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (fun i => h * (n i : ℝ))

lemma measurable_gridLabel (h : ℝ) : Measurable (gridLabel h) := by
  apply measurable_pi_iff.mpr
  intro i
  simp only [gridLabel, round_eq]
  apply Int.measurable_floor.comp
  have hc : Measurable (fun z : EuclideanSpace ℝ (Fin 3) => z i) :=
    (continuous_apply i).measurable.comp (PiLp.continuous_ofLp 2 _).measurable
  exact (hc.div_const h).add_const _

lemma abs_sub_gridCenter_le {h : ℝ} (hh : 0 < h) (z : EuclideanSpace ℝ (Fin 3)) (i : Fin 3) :
    |z i - h * (gridLabel h z i : ℝ)| ≤ h / 2 := by
  have := abs_sub_round (z i / h)
  simp only [gridLabel]
  have hz : z i - h * (round (z i / h) : ℝ) = h * (z i / h - round (z i / h)) := by
    field_simp
  rw [hz, abs_mul, abs_of_pos hh]
  nlinarith

lemma norm_sub_gridCenter_le {h : ℝ} (hh : 0 < h) (z : EuclideanSpace ℝ (Fin 3)) :
    ‖z - gridCenter h (gridLabel h z)‖ ≤ h := by
  rw [EuclideanSpace.norm_eq]
  have hcoord : ∀ i : Fin 3, ‖(z - gridCenter h (gridLabel h z)) i‖ ^ 2 ≤ (h / 2) ^ 2 := by
    intro i
    have h1 := abs_sub_gridCenter_le hh z i
    simp only [gridCenter, PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
    have h2 : |z i - h * (gridLabel h z i : ℝ)| ^ 2 ≤ (h / 2) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) h1 2
    simpa [sq_abs] using h2
  calc Real.sqrt (∑ i, ‖(z - gridCenter h (gridLabel h z)) i‖ ^ 2)
      ≤ Real.sqrt (∑ _i : Fin 3, (h / 2) ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_le_sum (fun i _ => hcoord i))
    _ = Real.sqrt (3 * (h / 2) ^ 2) := by simp
    _ ≤ Real.sqrt (h ^ 2) := by
        apply Real.sqrt_le_sqrt
        nlinarith
    _ = h := Real.sqrt_sq hh.le

/-- The finite box of labels used by points of norm at most `R`. -/
noncomputable def gridBox (h R : ℝ) : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Icc (-(⌈R / h⌉ + 1)) (⌈R / h⌉ + 1))

lemma gridLabel_mem_gridBox {h R : ℝ} (hh : 0 < h) {z : EuclideanSpace ℝ (Fin 3)}
    (hz : ‖z‖ ≤ R) : gridLabel h z ∈ gridBox h R := by
  simp only [gridBox, Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  have hzi : |z i| ≤ R := by
    have := PiLp.norm_apply_le z i
    simp only [Real.norm_eq_abs] at this
    linarith
  have h1 : |z i / h| ≤ R / h := by
    rw [abs_div, abs_of_pos hh]
    exact div_le_div_of_nonneg_right hzi hh.le
  have hr := abs_sub_round (z i / h)
  have hc : R / h ≤ (⌈R / h⌉ : ℝ) := Int.le_ceil _
  have habs := abs_le.mp h1
  have hr' := abs_le.mp hr
  constructor
  · have : (-(⌈R / h⌉ + 1) : ℝ) ≤ (gridLabel h z i : ℝ) := by
      simp only [gridLabel]; linarith
    exact_mod_cast this
  · have : (gridLabel h z i : ℝ) ≤ (⌈R / h⌉ + 1 : ℝ) := by
      simp only [gridLabel]; linarith
    exact_mod_cast this

lemma card_gridBox (h R : ℝ) (hR : 0 ≤ R) (hh : 0 < h) :
    ((gridBox h R).card : ℝ) ≤ (2 * R / h + 5) ^ 3 := by
  have hceil : (0 : ℤ) ≤ ⌈R / h⌉ := Int.ceil_nonneg (div_nonneg hR hh.le)
  simp only [gridBox, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  push_cast
  have h1 : (((⌈R / h⌉ + 1 + 1 - -(⌈R / h⌉ + 1)).toNat : ℕ) : ℝ) = 2 * (⌈R / h⌉ : ℝ) + 3 := by
    rw [show ⌈R / h⌉ + 1 + 1 - -(⌈R / h⌉ + 1) = 2 * ⌈R / h⌉ + 3 by ring]
    rw [show ((2 * ⌈R / h⌉ + 3).toNat : ℝ) = ((2 * ⌈R / h⌉ + 3 : ℤ) : ℝ) by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]]
    push_cast; ring
  rw [h1]
  have h2 : (⌈R / h⌉ : ℝ) ≤ R / h + 1 := (Int.ceil_lt_add_one _).le
  have h3 : 0 ≤ 2 * (⌈R / h⌉ : ℝ) + 3 := by
    have : (0 : ℝ) ≤ (⌈R / h⌉ : ℝ) := by exact_mod_cast hceil
    linarith
  apply pow_le_pow_left₀ h3
  have : 2 * R / h = 2 * (R / h) := by ring
  linarith

end Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing
