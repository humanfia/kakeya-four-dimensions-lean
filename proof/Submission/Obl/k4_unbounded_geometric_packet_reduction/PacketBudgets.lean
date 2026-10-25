import Mathlib

namespace Submission.Obl.k4_unbounded_geometric_packet_reduction

open MeasureTheory

noncomputable section

/-- Conditional prior normalization cancels the original world/packet budget.
The remaining denominator is the single common total weight. -/
theorem packet_weight_cancel {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (w s W : ENNReal) (hs : s ≠ 0) (hst : s ≠ ⊤) :
    (w * s / W) • (s⁻¹ • μ) = (W⁻¹ * w) • μ := by
  rw [smul_smul, div_eq_mul_inv]
  have heq : (w * s * W⁻¹) * s⁻¹ = (W⁻¹ * w) * (s * s⁻¹) := by ac_rfl
  rw [heq, ENNReal.mul_inv_cancel hs hst, mul_one]

theorem packet_family_weight_cancel {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : ι → Measure X) (w s : ι → ENNReal) (W : ENNReal)
    (hs : ∀ i, s i ≠ 0) (hst : ∀ i, s i ≠ ⊤) :
    (∑ i, (w i * s i / W) • ((s i)⁻¹ • μ i)) = W⁻¹ • ∑ i, w i • μ i := by
  simp_rw [packet_weight_cancel _ _ _ _ (hs _) (hst _)]
  rw [Finset.smul_sum]
  simp only [smul_smul]

/-- Restricting the conditional prior to an unchanged incidence selection
uses the original selected law, divided by the full assignment prior mass. -/
theorem conditional_prior_incidence {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] (A : Set X) (F : Set (X × ℝ))
    (hF : MeasurableSet F) (hsub : F ⊆ A ×ˢ Set.univ) :
    (((ν A)⁻¹ • ν.restrict A).prod volume).restrict F =
      (ν A)⁻¹ • ((ν.prod volume).restrict F) := by
  rw [Measure.prod_smul_left, Measure.restrict_smul,
    Measure.restrict_prod_eq_prod_univ, Measure.restrict_restrict hF,
    Set.inter_eq_left.mpr hsub]

/-- Discarding low-success conditional packets costs their common threshold
times the fixed original budget, regardless of their number. -/
theorem light_packet_mass_le {ι : Type*} [Fintype ι]
    (w m : ι → ENNReal) (θ : ENNReal) (hw : ∑ i, w i ≤ 1) :
    (∑ i ∈ Finset.univ.filter (fun i => m i < θ), w i * m i) ≤ θ := by
  classical
  calc
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i => m i < θ), w i * θ := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hi).2.le zero_le
    _ = θ * ∑ i ∈ Finset.univ.filter (fun i => m i < θ), w i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact mul_comm _ _
    _ ≤ θ * ∑ i, w i := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => zero_le)) zero_le
    _ ≤ θ * 1 := mul_le_mul_of_nonneg_left hw zero_le
    _ = θ := mul_one _

/-- A half-mass recovery in every substantial packet gives a global recovery
on the unchanged original budgets. -/
theorem packet_recovery_mass {ι : Type*} [Fintype ι]
    (w m recovered : ι → ENNReal) (θ : ENNReal) (hw : ∑ i, w i ≤ 1)
    (hrec : ∀ i, θ ≤ m i → m i ≤ 2 * recovered i) :
    (∑ i, w i * m i) ≤ 2 * (∑ i, w i * recovered i) + θ := by
  classical
  let good := Finset.univ.filter (fun i => θ ≤ m i)
  let bad := Finset.univ.filter (fun i => m i < θ)
  have hsplit : (∑ i, w i * m i) =
      (∑ i ∈ good, w i * m i) + ∑ i ∈ bad, w i * m i := by
    simpa only [good, bad, not_le] using
      (Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => θ ≤ m i)
        (fun i => w i * m i)).symm
  rw [hsplit]
  apply add_le_add _ (light_packet_mass_le w m θ hw)
  calc
    _ ≤ ∑ i ∈ good, w i * (2 * recovered i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hrec i (Finset.mem_filter.mp hi).2) zero_le
    _ = 2 * ∑ i ∈ good, w i * recovered i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ 2 * ∑ i, w i * recovered i := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => zero_le)) zero_le

end
end Submission.Obl.k4_unbounded_geometric_packet_reduction
