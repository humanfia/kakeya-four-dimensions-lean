import Submission.Obl.k4_horizontal_coefficient_count.LMSetup
import Submission.Obl.k4_horizontal_coefficient_count.Bounded

namespace Submission.Obl.k4_horizontal_coefficient_count

open MeasureTheory Set
open scoped ENNReal

/-- The endpoint scalar bounds and the original base bound control all
coefficients pointwise on the good set. -/
theorem goodSet_coefficient_bound {α : Type*} (b : α → Fin 6 → ℝ) {K E : ℝ}
    (hK : 0 ≤ K) {l : α} (hl : l ∈ goodSet b K E) : ∀ e, |b l e| ≤ 2 * K := by
  have hb := hl.1
  have hs : |b l 5| ≤ 2 * K := by
    calc
      _ = |(b l 2 + b l 5) - b l 2| := by congr 1; ring
      _ ≤ |b l 2 + b l 5| + |b l 2| := abs_sub _ _
      _ ≤ 2 * K := by linarith [hl.2.2.1, hl.2.2.2]
  intro e
  fin_cases e
  · change |b l 0| ≤ 2 * K
    linarith [abs_nonneg (b l 1), abs_nonneg (b l 3), abs_nonneg (b l 4)]
  · change |b l 1| ≤ 2 * K
    linarith [abs_nonneg (b l 0), abs_nonneg (b l 3), abs_nonneg (b l 4)]
  · change |b l 2| ≤ 2 * K
    linarith [hl.2.2.1]
  · change |b l 3| ≤ 2 * K
    linarith [abs_nonneg (b l 0), abs_nonneg (b l 1), abs_nonneg (b l 4)]
  · change |b l 4| ≤ 2 * K
    linarith [abs_nonneg (b l 0), abs_nonneg (b l 1), abs_nonneg (b l 3)]
  · exact hs

/-- Prior domination transfers the original base bound to the current law;
the full-time scalar bound supplies the two scalar endpoints. -/
theorem ae_goodSet {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [SFinite ν] (μ : Measure (α × ℝ))
    (b : α → Fin 6 → ℝ) (hb : Measurable b) {K E : ℝ} {C : ENNReal}
    (hdom : μ ≤ C • ν.prod volume)
    (hbase : ∀ᵐ l ∂ν, |b l 0| + |b l 1| + |b l 3| + |b l 4| ≤ K)
    (hhor : ∀ᵐ p ∂μ, |b p.1 4 + b p.1 0| ≤ E)
    (hscalar : ∀ᵐ p ∂μ, ∀ t ∈ Icc (0 : ℝ) 1, |b p.1 2 + t * b p.1 5| ≤ K) :
    ∀ᵐ p ∂μ, p.1 ∈ goodSet b K E := by
  have hm : MeasurableSet {p : α × ℝ |
      |b p.1 0| + |b p.1 1| + |b p.1 3| + |b p.1 4| ≤ K} :=
    measurableSet_le (by fun_prop) measurable_const
  have hprod : ∀ᵐ (p : α × ℝ) ∂ν.prod volume,
      |b p.1 0| + |b p.1 1| + |b p.1 3| + |b p.1 4| ≤ K := by
    apply (Measure.ae_prod_iff_ae_ae hm).mpr
    filter_upwards [hbase] with l hl
    exact Filter.Eventually.of_forall (fun _ => hl)
  have hbμ := (Measure.absolutelyContinuous_of_le_smul hdom).ae_le hprod
  filter_upwards [hbμ, hhor, hscalar] with p hp hhp hsp
  refine ⟨hp, hhp, ?_, ?_⟩
  · simpa using hsp 0 (by simp)
  · simpa using hsp 1 (by simp)

end Submission.Obl.k4_horizontal_coefficient_count
