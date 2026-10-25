/-
Adapted from this LOT tree o203, session x0699, commit 4341160d,
Submission/Obl/k4_horizontal_supercritical_rate_candidates/Conditioning.lean (namespace
Submission.Obl.k4_horizontal_supercritical_rate_candidates renamed to
Submission.Obl.k4_horizontal_supercritical_three_projections.Parent).
-/
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.ConditionalProbability

namespace Submission.Obl.k4_horizontal_supercritical_three_projections.Parent

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Divide by the full trajectory assignment weight. -/
def conditionedIncidences {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (μ : Measure (α × ℝ)) (A : Set α) : Measure (α × ℝ) :=
  (ν A)⁻¹ • μ.restrict (A ×ˢ univ)

theorem conditionedIncidences_mono {α : Type*} [MeasurableSpace α]
    (ν : Measure α) {μ μ' : Measure (α × ℝ)} (hμ : μ' ≤ μ) (A : Set α) :
    conditionedIncidences ν μ' A ≤ conditionedIncidences ν μ A := by
  intro E
  exact mul_le_mul' le_rfl (Measure.restrict_mono_measure hμ _ E)

/-- The original time domination survives conditioning with the same constant. -/
theorem conditionedIncidences_domination {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [SFinite ν] (μ : Measure (α × ℝ)) (A : Set α)
    (C : ENNReal) (hdom : μ ≤ C • (ν.prod volume)) :
    conditionedIncidences ν μ A ≤
      C • ((ProbabilityTheory.cond ν A).prod volume) := by
  have hrest := Measure.restrict_mono_measure hdom (A ×ˢ (univ : Set ℝ))
  rw [Measure.restrict_smul] at hrest
  have hscaled : (ν A)⁻¹ • μ.restrict (A ×ˢ univ) ≤
      (ν A)⁻¹ • (C • (ν.prod volume).restrict (A ×ˢ univ)) := by
    intro E
    exact mul_le_mul' le_rfl (hrest E)
  simpa only [conditionedIncidences, ProbabilityTheory.cond, Measure.prod_smul_left, Measure.restrict_prod_eq_prod_univ,
    smul_smul, mul_comm] using hscaled

theorem conditionedIncidences_unit_support {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (μ : Measure (α × ℝ)) (A : Set α)
    (hsupp : μ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0) :
    conditionedIncidences ν μ A (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0 := by
  have hz : μ.restrict (A ×ˢ univ) (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0 :=
    le_antisymm ((Measure.restrict_le_self _).trans_eq hsupp) bot_le
  simp only [conditionedIncidences, Measure.smul_apply, smul_eq_mul, hz, mul_zero]

/-- Return every counted event to its original, unnormalized law. -/
theorem conditionedIncidences_mass_identity {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (μ : Measure (α × ℝ)) (A : Set α)
    (hA : ν A ≠ 0) (hAfin : ν A ≠ ⊤) (E : Set (α × ℝ)) (hE : MeasurableSet E) :
    ν A * conditionedIncidences ν μ A E = μ (E ∩ (A ×ˢ univ)) := by
  rw [conditionedIncidences, Measure.smul_apply, smul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel hA hAfin, one_mul, Measure.restrict_apply hE]

theorem conditionedIncidences_floor_return {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (μ : Measure (α × ℝ)) (A : Set α)
    (hA : ν A ≠ 0) (hAfin : ν A ≠ ⊤) (E : Set (α × ℝ)) (hE : MeasurableSet E)
    {m : ℝ} (_hm : 0 ≤ m) (hfloor : ENNReal.ofReal m ≤ conditionedIncidences ν μ A E) :
    ENNReal.ofReal ((ν A).toReal * m) ≤ μ (E ∩ (A ×ˢ univ)) := by
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hAfin,
    ← conditionedIncidences_mass_identity ν μ A hA hAfin E hE]
  exact mul_le_mul' le_rfl hfloor

end

end Submission.Obl.k4_horizontal_supercritical_three_projections.Parent
