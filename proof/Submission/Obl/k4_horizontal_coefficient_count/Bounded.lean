import Submission.Obl.k4_horizontal_coefficient_count.Common

namespace Submission.Obl.k4_horizontal_coefficient_count

open MeasureTheory Set
open scoped ENNReal

theorem current_total_mass_le {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (μ : Measure (α × ℝ))
    {K : ℝ} (hμ : μ ≤ ENNReal.ofReal K • ν.prod volume)
    (htime : μ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0) : μ univ ≤ ENNReal.ofReal K := by
  have hmeas : MeasurableSet (univ ×ˢ Icc (0 : ℝ) 1 : Set (α × ℝ)) :=
    MeasurableSet.univ.prod measurableSet_Icc
  calc
    μ univ = μ (univ ×ˢ Icc (0 : ℝ) 1) + μ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ :=
      (measure_add_measure_compl hmeas).symm
    _ = μ (univ ×ˢ Icc (0 : ℝ) 1) := by rw [htime, add_zero]
    _ ≤ (ENNReal.ofReal K • ν.prod volume) (univ ×ˢ Icc (0 : ℝ) 1) := hμ _
    _ = ENNReal.ofReal K := by
      rw [Measure.smul_apply, smul_eq_mul, Measure.prod_prod, measure_univ, one_mul,
        Real.volume_Icc]
      norm_num

theorem affine_scalar_coefficients {b : Fin 6 → ℝ} {K : ℝ}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, |b 2 + t * b 5| ≤ K) :
    |b 2| ≤ K ∧ |b 5| ≤ 2 * K := by
  have h₀ : |b 2| ≤ K := by simpa using h 0 (by simp)
  have h₁ : |b 2 + b 5| ≤ K := by simpa using h 1 (by simp)
  refine ⟨h₀, ?_⟩
  calc
    |b 5| = |(b 2 + b 5) - b 2| := by congr 1; ring
    _ ≤ |b 2 + b 5| + |b 2| := abs_sub _ _
    _ ≤ 2 * K := by linarith

/-- The prior bound on the four base coefficients and the full-time bound
on the horizontal residual bound all six coefficients on the current law. -/
theorem current_ae_coefficient_bound {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [SFinite ν] (μ : Measure (α × ℝ))
    (b : α → Fin 6 → ℝ) (hb : Measurable b) {K : ℝ} (hK : 0 ≤ K)
    {C : ENNReal} (hμ : μ ≤ C • ν.prod volume)
    (hbase : ∀ᵐ l ∂ν, |b l 0| + |b l 1| + |b l 3| + |b l 4| ≤ K)
    (hscalar : ∀ᵐ p ∂μ, ∀ t ∈ Icc (0 : ℝ) 1, |b p.1 2 + t * b p.1 5| ≤ K) :
    ∀ᵐ p ∂μ, ∀ e, |b p.1 e| ≤ 2 * K := by
  have hm : MeasurableSet {p : α × ℝ |
      |b p.1 0| + |b p.1 1| + |b p.1 3| + |b p.1 4| ≤ K} :=
    measurableSet_le (by fun_prop) measurable_const
  have hprod : ∀ᵐ (p : α × ℝ) ∂ν.prod volume,
      |b p.1 0| + |b p.1 1| + |b p.1 3| + |b p.1 4| ≤ K := by
    apply (Measure.ae_prod_iff_ae_ae hm).mpr
    filter_upwards [hbase] with l hl
    exact Filter.Eventually.of_forall (fun _ => hl)
  have hbμ := (Measure.absolutelyContinuous_of_le_smul hμ).ae_le hprod
  filter_upwards [hbμ, hscalar] with p hp hs
  have hc := affine_scalar_coefficients hs
  intro e
  fin_cases e
  · change |b p.1 0| ≤ 2 * K
    linarith [abs_nonneg (b p.1 1), abs_nonneg (b p.1 3), abs_nonneg (b p.1 4)]
  · change |b p.1 1| ≤ 2 * K
    linarith [abs_nonneg (b p.1 0), abs_nonneg (b p.1 3), abs_nonneg (b p.1 4)]
  · change |b p.1 2| ≤ 2 * K
    linarith [hc.1]
  · change |b p.1 3| ≤ 2 * K
    linarith [abs_nonneg (b p.1 0), abs_nonneg (b p.1 1), abs_nonneg (b p.1 4)]
  · change |b p.1 4| ≤ 2 * K
    linarith [abs_nonneg (b p.1 0), abs_nonneg (b p.1 1), abs_nonneg (b p.1 3)]
  · change |b p.1 5| ≤ 2 * K
    exact hc.2

end Submission.Obl.k4_horizontal_coefficient_count
