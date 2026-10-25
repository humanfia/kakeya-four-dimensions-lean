/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarAnchor.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarAnchor.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Choosing an original time anchor by overlap, before temporary scalar
groups are used to discover the common row. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set

/-- A finite original prior of mass `V` admits an anchor whose
duration-weighted overlap times `V` is at least the original event mass
squared. Any common null set of parameters can be avoided. -/
theorem exists_original_anchor_finite {Θ Λ : Type*} [MeasurableSpace Θ] [MeasurableSpace Λ]
    (μ : Measure Θ) [IsProbabilityMeasure μ] (ν : Measure Λ) [IsFiniteMeasure ν]
    {E : Set (Θ × Λ)} (hE : MeasurableSet E) {Z : Set Θ} (hZ : μ Z = 0) :
    ∃ θ ∉ Z, ((μ.prod ν).real E) ^ 2 ≤ ν.real univ * ∫ l,
      (Prod.mk θ ⁻¹' E).indicator
        (fun l => μ.real ((fun u => (u, l)) ⁻¹' E)) l ∂ν := by
  let D : Λ → ℝ := fun l => μ.real ((fun θ => (θ, l)) ⁻¹' E)
  have hDm : Measurable D := (measurable_measure_prodMk_right hE).ennreal_toReal
  have hDr l : 0 ≤ D l ∧ D l ≤ 1 := ⟨measureReal_nonneg, measureReal_le_one⟩
  have hDi : Integrable D ν := Integrable.of_bound hDm.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun l => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hDr l).1]
      exact (hDr l).2)
  have hDsq : Integrable (fun l => D l ^ 2) ν :=
    Integrable.of_bound (hDm.pow_const 2).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun l => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [(hDr l).1, (hDr l).2])
  have htotal : (∫ l, D l ∂ν) = (μ.prod ν).real E := by
    unfold D Measure.real
    rw [integral_toReal (measurable_measure_prodMk_right hE).aemeasurable
      (Filter.Eventually.of_forall fun l => measure_lt_top μ _), Measure.prod_apply_symm hE]
  have hJ : ((μ.prod ν).real E) ^ 2 ≤ ν.real univ * ∫ l, D l ^ 2 ∂ν := by
    rw [← htotal]
    by_cases hν : ν = 0
    · simp only [hν, integral_zero_measure, measureReal_zero_apply, zero_pow (by norm_num : 2 ≠ 0),
        zero_mul, le_refl]
    letI : NeZero ν := ⟨hν⟩
    have hV : 0 < ν.real univ := measureReal_univ_pos
    have h := (convexOn_pow (𝕜 := ℝ) 2).map_average_le
      (continuous_pow 2).continuousOn isClosed_Ici
      (Filter.Eventually.of_forall fun l => (hDr l).1) hDi hDsq
    simp only [average_eq, smul_eq_mul] at h
    have hmul := mul_le_mul_of_nonneg_left h (sq_nonneg (ν.real univ))
    have hleft : (ν.real univ) ^ 2 * ((ν.real univ)⁻¹ * ∫ l, D l ∂ν) ^ 2 = (∫ l, D l ∂ν) ^ 2 := by
      field_simp
    have hright : (ν.real univ) ^ 2 * ((ν.real univ)⁻¹ * ∫ l, D l ^ 2 ∂ν) =
        ν.real univ * ∫ l, D l ^ 2 ∂ν := by field_simp
    rwa [hleft, hright] at hmul
  let F : Θ × Λ → ℝ := E.indicator (fun p => D p.2)
  have hFm : Measurable F := (hDm.comp measurable_snd).indicator hE
  have hFi : Integrable F (μ.prod ν) := by
    apply Integrable.of_bound hFm.aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro p
    by_cases hp : p ∈ E
    · simpa only [F, indicator_of_mem hp, Real.norm_eq_abs,
        abs_of_nonneg (hDr p.2).1] using (hDr p.2).2
    · simp only [F, indicator_of_notMem hp, norm_zero, zero_le_one]
  have hinner l : (∫ θ, F (θ, l) ∂μ) = D l ^ 2 := by
    have he : (fun θ => F (θ, l)) =
        ((fun θ => (θ, l)) ⁻¹' E).indicator (fun _ => D l) := by
      funext θ
      by_cases h : (θ, l) ∈ E <;> simp [F, h]
    rw [he, integral_indicator (measurable_prodMk_right hE)]
    simp only [setIntegral_const, smul_eq_mul, D, pow_two]
  have hswap : (∫ θ, ∫ l, F (θ, l) ∂ν ∂μ) = ∫ l, D l ^ 2 ∂ν := by
    rw [integral_integral_swap (f := fun θ l => F (θ, l)) hFi]
    simp_rw [hinner]
  obtain ⟨θ, hθZ, hθ⟩ := exists_notMem_null_integral_le hFi.integral_prod_left hZ
  refine ⟨θ, hθZ, ?_⟩
  rw [hswap] at hθ
  have hh := hJ.trans (mul_le_mul_of_nonneg_left hθ measureReal_nonneg)
  convert hh using 1
  congr 1

/-- Probability-prior form, with the original quadratic overlap floor. -/
theorem exists_original_anchor {Θ Λ : Type*} [MeasurableSpace Θ] [MeasurableSpace Λ]
    (μ : Measure Θ) [IsProbabilityMeasure μ] (ν : Measure Λ) [IsProbabilityMeasure ν]
    {E : Set (Θ × Λ)} (hE : MeasurableSet E) {Z : Set Θ} (hZ : μ Z = 0) :
    ∃ θ ∉ Z, ((μ.prod ν).real E) ^ 2 ≤ ∫ l,
      (Prod.mk θ ⁻¹' E).indicator
        (fun l => μ.real ((fun u => (u, l)) ⁻¹' E)) l ∂ν := by
  obtain ⟨θ, hθ, hbound⟩ := exists_original_anchor_finite μ ν hE hZ
  refine ⟨θ, hθ, ?_⟩
  simpa only [Measure.real, measure_univ, ENNReal.toReal_one, one_mul] using hbound

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
