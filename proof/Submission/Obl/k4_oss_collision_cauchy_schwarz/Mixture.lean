import Submission.Obl.k4_oss_collision_cauchy_schwarz.Cells

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Obl.k4_oss_collision_cauchy_schwarz

/-- Collision Cauchy--Schwarz for an arbitrary measurable mixture of laws on the line. -/
theorem collision_mixture_le {P X : Type*} [MeasurableSpace P] [MeasurableSpace X]
    (π : Measure P) [IsProbabilityMeasure π] (μ : Measure X) [IsFiniteMeasure μ]
    (f : P × X → ℝ) (hf : Measurable f) {r : ℝ} (hr : 0 < r) :
    let ν := Measure.map f (π.prod μ)
    (ν.prod ν) {q : ℝ × ℝ | |q.1 - q.2| ≤ r} ≤
      3 * ∫⁻ p, (μ.prod μ) {q : X × X | |f (p, q.1) - f (p, q.2)| ≤ r} ∂π := by
  let ν := Measure.map f (π.prod μ)
  let a : ℤ → P → ℝ≥0∞ := fun k p => μ ((fun x => f (p, x)) ⁻¹' cell r k)
  have ha (k : ℤ) : Measurable (a k) :=
    measurable_measure_prodMk_left (hf (measurableSet_cell r k))
  have hmass (k : ℤ) : ν (cell r k) = ∫⁻ p, a k p ∂π := by
    rw [Measure.map_apply hf (measurableSet_cell r k),
      Measure.prod_apply (hf (measurableSet_cell r k))]
    rfl
  have hcond (p : P) : (∑' k : ℤ, a k p * a k p) ≤
      (μ.prod μ) {q : X × X | |f (p, q.1) - f (p, q.2)| ≤ r} := by
    have hfp : Measurable (fun x => f (p, x)) := hf.comp measurable_prodMk_left
    have h := cell_energy_le_collision (Measure.map (fun x => f (p, x)) μ) hr
    simp_rw [Measure.map_apply hfp (measurableSet_cell r _)] at h
    rw [Measure.map_prod_map μ μ hfp hfp,
      Measure.map_apply (hfp.prodMap hfp) (by measurability)] at h
    exact h
  calc
    _ ≤ 3 * ∑' k : ℤ, ν (cell r k) * ν (cell r k) :=
      collision_le_three_cell_energy ν hr
    _ = 3 * ∑' k : ℤ, (∫⁻ p, a k p ∂π) * (∫⁻ p, a k p ∂π) := by simp_rw [hmass]
    _ ≤ 3 * ∑' k : ℤ, ∫⁻ p, a k p * a k p ∂π := by
      gcongr with k
      exact lintegral_mul_self_le π (ha k)
    _ = 3 * ∫⁻ p, ∑' k : ℤ, a k p * a k p ∂π := by
      congr 1
      exact (lintegral_tsum (f := fun k p => a k p * a k p)
        (fun k => ((ha k).mul (ha k)).aemeasurable)).symm
    _ ≤ _ := by
      gcongr
      exact hcond _

end Submission.Obl.k4_oss_collision_cauchy_schwarz
