/- Adapted from this LOT tree oai_074_kakeya_four_dimensions, obligation o231,
session x0798, branch x0798, commit fbdba9e7,
Submission/Obl/k4_scalar_capped_heavy_potential/PairBreadth.lean.
Earlier source credits are retained below. -/

import Mathlib
import Submission.Lib.K4ScalarActualSwitching.StarSelection

namespace Submission.Obl.k4_scalar_heavy_intercept_selection

open Set MeasureTheory
open Submission.Lib.K4ScalarActualSwitching

noncomputable section

/-- A relative pencil cap controls bad pairs in the product of the
original finite law. No group is normalized after selection. -/
theorem relative_pencil_pair_mass {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (v : Ω → ℝ) (hv : Measurable v)
    (r : ℝ) (K : ENNReal)
    (hthin : ∀ w, μ {p | |v p - w| < r} ≤ K * μ univ) :
    (μ.prod μ) (controlPencil v r) ≤ K * μ univ ^ 2 := by
  rw [Measure.prod_apply (measurableSet_controlPencil v hv r)]
  calc
    _ ≤ ∫⁻ _ : Ω, K * μ univ ∂μ := by
      apply lintegral_mono
      intro p
      simpa only [controlPencil, preimage_ofPred_eq, abs_sub_comm] using hthin (v p)
    _ = _ := by rw [lintegral_const]; ring

/-- Half of all original pairs have separated velocities when the
relative pencil ceiling is at most one half. -/
theorem separated_pair_mass_floor {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (v : Ω → ℝ) (hv : Measurable v)
    (r : ℝ)
    (hthin : ∀ w, μ {p | |v p - w| < r} ≤ ENNReal.ofReal (1 / 2 : ℝ) * μ univ) :
    ENNReal.ofReal (1 / 2 : ℝ) * μ univ ^ 2 ≤
      (μ.prod μ) {p | r ≤ |v p.1 - v p.2|} := by
  let H := ENNReal.ofReal (1 / 2 : ℝ) * μ univ ^ 2
  have hhalf : H + H = μ univ ^ 2 := by
    dsimp [H]
    rw [← add_mul, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  have hbad := relative_pencil_pair_mass μ v hv r _ hthin
  have hsplit := measure_add_measure_compl (μ := μ.prod μ)
    (measurableSet_controlPencil v hv r)
  have hcompl : (controlPencil v r)ᶜ = {p : Ω × Ω | r ≤ |v p.1 - v p.2|} := by
    ext p
    simp [controlPencil, not_lt]
  rw [hcompl] at hsplit
  apply ENNReal.le_of_add_le_add_right (a := H) (by dsimp [H]; finiteness)
  calc
    H + H = μ univ ^ 2 := hhalf
    _ = (μ.prod μ) (controlPencil v r) +
        (μ.prod μ) {p | r ≤ |v p.1 - v p.2|} := by
          have ht := Measure.prod_prod (μ := μ) (ν := μ) univ univ
          rw [univ_prod_univ] at ht
          simpa only [ht, pow_two] using hsplit.symm
    _ ≤ H + (μ.prod μ) {p | r ≤ |v p.1 - v p.2|} := add_le_add hbad le_rfl
    _ = _ := add_comm _ _

/-- A cellwise relative pencil bound supplies the actual two-copy
incidence tuples used by planar Kakeya. -/
theorem separated_cell_tuple_mass_floor {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (v : Ω → ℝ) (hv : Measurable v)
    (S : Set Ω) (hS : MeasurableSet S) (r : ℝ)
    (hthin : ∀ w, (μ.restrict S) {p | |v p - w| < r} ≤
      ENNReal.ofReal (1 / 2 : ℝ) * μ S) :
    ENNReal.ofReal (1 / 2 : ℝ) * μ S ^ 2 ≤
      Measure.pi (fun _ : Fin 2 => μ)
        {p | (∀ i, p i ∈ S) ∧ r ≤ |v (p 0) - v (p 1)|} := by
  have h := separated_pair_mass_floor (μ.restrict S) v hv r
    (by simpa only [Measure.restrict_apply_univ] using hthin)
  rw [Measure.restrict_apply_univ] at h
  have hsep : MeasurableSet {p : Ω × Ω | r ≤ |v p.1 - v p.2|} :=
    measurableSet_le measurable_const ((hv.comp measurable_fst).sub (hv.comp measurable_snd)).abs
  have hid : (μ.restrict S).prod (μ.restrict S) {p | r ≤ |v p.1 - v p.2|} =
      Measure.pi (fun _ : Fin 2 => μ)
        {p | (∀ i, p i ∈ S) ∧ r ≤ |v (p 0) - v (p 1)|} := by
    rw [Measure.prod_restrict, Measure.restrict_apply hsep]
    have heq := (measurePreserving_finTwoArrow μ).measure_preimage
      (hsep.inter (hS.prod hS)).nullMeasurableSet
    rw [← heq]
    congr 1
    ext p
    simp [Fin.forall_fin_two, and_comm, and_left_comm]
  rw [← hid]
  exact h

end
end Submission.Obl.k4_scalar_heavy_intercept_selection
