import Submission.Obl.k4_quadratic_atlas_normalization.AssignmentMass

namespace Submission.Obl.k4_contact_time_rate_rigidity

open MeasureTheory Set
open scoped ENNReal

/-- Coarse assignments charge a short time cover only once per time block. -/
theorem mass_bound_of_time_cover {α ι J : Type*} [MeasurableSpace α]
    [Fintype ι] [Fintype J] (ν : Measure α) [IsProbabilityMeasure ν]
    (μ : Measure (α × ℝ)) (A : ι → Set α) (j : ι → J) (c : ι → ℝ)
    {K τ : ℝ} (hK : 0 ≤ K)
    (hdom : μ ≤ ENNReal.ofReal K • (ν.prod volume))
    (hA : ∀ i, MeasurableSet (A i))
    (hdisj : ∀ i i', i ≠ i' → j i = j i' → Disjoint (A i) (A i'))
    (hcover : ∀ᵐ p ∂μ, ∃ i, p.1 ∈ A i ∧ p.2 ∈ Icc (c i - τ) (c i + τ)) :
    μ univ ≤ ENNReal.ofReal (2 * K * τ) * (Fintype.card J : ℝ≥0∞) := by
  classical
  have hbudget : (∑ i, ν (A i)) ≤ (Fintype.card J : ℝ≥0∞) := by
    simpa only [one_mul] using
      Submission.Obl.k4_quadratic_atlas_normalization.weighted_assignment_budget
        (fun _ : Unit => ν) (fun _ => 1) (fun _ => ()) j A
        (fun _ => measure_univ) (by simp) hA (fun i i' hne _ heq => hdisj i i' hne heq)
  let E := ⋃ i, A i ×ˢ Icc (c i - τ) (c i + τ)
  have hcover' : univ ≤ᵐ[μ] E := by
    filter_upwards [hcover] with p hp
    obtain ⟨i, hi, ht⟩ := hp
    exact fun _ => mem_iUnion.mpr ⟨i, hi, ht⟩
  have hprod (i : ι) : (ν.prod volume) (A i ×ˢ Icc (c i - τ) (c i + τ)) =
      ν (A i) * ENNReal.ofReal (2 * τ) := by
    rw [Measure.prod_prod, Real.volume_Icc]
    congr 2
    ring
  calc
    μ univ ≤ μ E := measure_mono_ae hcover'
    _ ≤ (ENNReal.ofReal K • (ν.prod volume)) E := hdom E
    _ = ENNReal.ofReal K * (ν.prod volume) E := by rw [Measure.smul_apply, smul_eq_mul]
    _ ≤ ENNReal.ofReal K * ∑ i, (ν.prod volume) (A i ×ˢ Icc (c i - τ) (c i + τ)) := by
      gcongr
      exact measure_iUnion_fintype_le _ _
    _ = ENNReal.ofReal K * (ENNReal.ofReal (2 * τ) * ∑ i, ν (A i)) := by
      simp only [hprod]
      rw [← Finset.sum_mul]
      congr 1
      ring
    _ ≤ ENNReal.ofReal K * (ENNReal.ofReal (2 * τ) * (Fintype.card J : ℝ≥0∞)) := by
      gcongr
    _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul hK]; congr 2; ring

end Submission.Obl.k4_contact_time_rate_rigidity
