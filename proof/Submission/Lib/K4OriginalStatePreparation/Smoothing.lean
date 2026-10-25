/- Adapted from: here:o247 (session x0870, original proofs in commits
4fa3d421, 60e815aa, 71be63c4, and 30be2d73). -/
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Sum

namespace Submission.Lib.K4OriginalStatePreparation

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Resample only the base point, independently inside its original mesh
cell. The first coordinate keeps the complete original event. -/
def cellCoupling {Ω Y Q : Type*} [MeasurableSpace Ω] [MeasurableSpace Y] [Fintype Q]
    (pieces : Q → Measure Ω) (cellLaw : Q → Measure Y) : Measure (Ω × Y) :=
  ∑ q, (pieces q).prod (cellLaw q)

/-- The smoothing keeps the full original law, not just its label masses. -/
theorem cellCoupling_fst {Ω Y Q : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    [Fintype Q] (pieces : Q → Measure Ω) (cellLaw : Q → Measure Y)
    [∀ q, IsFiniteMeasure (pieces q)] [∀ q, IsProbabilityMeasure (cellLaw q)] :
    (cellCoupling pieces cellLaw).map Prod.fst = ∑ q, pieces q := by
  rw [cellCoupling, Measure.map_finset_sum' measurable_fst.aemeasurable]
  simp only [Measure.map_fst_prod, measure_univ, one_smul]

theorem cellCoupling_finite {Ω Y Q : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    [Fintype Q] (pieces : Q → Measure Ω) (cellLaw : Q → Measure Y)
    [∀ q, IsFiniteMeasure (pieces q)] [∀ q, IsProbabilityMeasure (cellLaw q)] :
    IsFiniteMeasure (cellCoupling pieces cellLaw) := by
  unfold cellCoupling
  infer_instance

/-- Original mesh membership and the resampled mesh membership hold
simultaneously for the literal coupling. -/
theorem cellCoupling_support {Ω Y Q : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    [Fintype Q] (pieces : Q → Measure Ω) (cellLaw : Q → Measure Y)
    [∀ q, IsFiniteMeasure (pieces q)] [∀ q, IsProbabilityMeasure (cellLaw q)]
    (part : Q → Set Ω) (cell : Q → Set Y)
    (hp : ∀ q, ∀ᵐ p ∂pieces q, p ∈ part q)
    (hc : ∀ q, ∀ᵐ y ∂cellLaw q, y ∈ cell q) :
    ∀ᵐ z ∂cellCoupling pieces cellLaw, ∃ q, z.1 ∈ part q ∧ z.2 ∈ cell q := by
  rw [cellCoupling, ae_finsetSum_measure_iff]
  intro q _
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (hp q),
    Measure.quasiMeasurePreserving_snd.ae (hc q)] with z hz hy
  exact ⟨q, hz, hy⟩

/-- An equal-volume cell table with a mass ceiling smooths to a genuine
base density ceiling. No factor for the number of cells is incurred. -/
theorem cellCoupling_density {Ω Y Q : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    [Fintype Q] (pieces : Q → Measure Ω) (cellLaw : Q → Measure Y)
    [∀ q, IsFiniteMeasure (pieces q)] [∀ q, IsProbabilityMeasure (cellLaw q)]
    (β : Measure Y) (cell : Q → Set Y) (hcell : ∀ q, MeasurableSet (cell q))
    (hdisj : Pairwise (fun q q' => Disjoint (cell q) (cell q')))
    (V A : ℝ≥0∞) (hV : V ≠ 0) (hVtop : V ≠ ⊤)
    (E : Set Ω) (hcap : ∀ q, pieces q E ≤ A * V)
    (hk : ∀ q (U : Set Y), MeasurableSet U →
      cellLaw q U ≤ V⁻¹ * β (U ∩ cell q))
    (U : Set Y) (hU : MeasurableSet U) :
    cellCoupling pieces cellLaw (E ×ˢ U) ≤ A * β U := by
  have hsum : (∑ q, β (U ∩ cell q)) ≤ β U := by
    have hd : Pairwise (fun q q' => Disjoint (U ∩ cell q) (U ∩ cell q')) :=
      fun q q' h => (hdisj h).mono inter_subset_right inter_subset_right
    have h := measure_iUnion (μ := β) hd (fun q => hU.inter (hcell q))
    rw [tsum_fintype] at h
    calc
      _ = β (⋃ q, U ∩ cell q) := h.symm
      _ ≤ β U := measure_mono (iUnion_subset fun _ => inter_subset_left)
  calc
    _ = ∑ q, pieces q E * cellLaw q U := by
      simp only [cellCoupling, Measure.finsetSum_apply, Measure.prod_prod]
    _ ≤ ∑ q, (A * V) * (V⁻¹ * β (U ∩ cell q)) :=
      Finset.sum_le_sum fun q _ => mul_le_mul' (hcap q) (hk q U hU)
    _ = A * ∑ q, β (U ∩ cell q) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      calc
        (A * V) * (V⁻¹ * β (U ∩ cell q)) = A * (V * V⁻¹) * β (U ∩ cell q) := by ring
        _ = _ := by rw [ENNReal.mul_inv_cancel hV hVtop, mul_one]
    _ ≤ _ := mul_le_mul' le_rfl hsum

end

end Submission.Lib.K4OriginalStatePreparation
