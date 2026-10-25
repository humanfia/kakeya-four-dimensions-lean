/- Adapted within this LOT tree from o120/x0402, commit 70956fccdfd7e9924a3fa094355c65a03c16ee9c,
Submission/Obl/k4_unbounded_width_exclusion/RealPosterior.lean. -/
import Submission.Obl.k4_fixed_budget_quadratic_recovery.PosteriorPair

noncomputable section

namespace Submission.Obl.k4_fixed_budget_quadratic_recovery

open MeasureTheory Finset Filter
open scoped ENNReal

variable {X β : Type*} [MeasurableSpace X] [Fintype β]

/-- A measurable real subprobability vector, changed only off the
probability-vector locus of the extended-real posterior. -/
def realPosterior (π : X → β → ENNReal) (x : X) (b : β) : ℝ :=
  if (∑ a, π x a) = 1 then (π x b).toReal else 0

theorem realPosterior_measurable (π : X → β → ENNReal)
    (hπ : ∀ b, Measurable (fun x => π x b)) (b : β) :
    Measurable (fun x => realPosterior π x b) := by
  have hsum : Measurable (fun x => ∑ a, π x a) :=
    Finset.measurable_sum _ (fun a _ => hπ a)
  exact Measurable.ite (measurableSet_eq_fun hsum measurable_const)
    (hπ b).ennreal_toReal measurable_const

omit [MeasurableSpace X] in
theorem realPosterior_nonneg (π : X → β → ENNReal) (x : X) (b : β) :
    0 ≤ realPosterior π x b := by
  unfold realPosterior
  split_ifs
  · exact ENNReal.toReal_nonneg
  · exact le_rfl

omit [MeasurableSpace X] in
theorem realPosterior_mass_le (π : X → β → ENNReal) (x : X) :
    ∑ b, realPosterior π x b ≤ 1 := by
  classical
  by_cases hx : (∑ a, π x a) = 1
  · have hfinite (b : β) : π x b ≠ ∞ := by
      apply ne_top_of_le_ne_top ENNReal.one_ne_top
      exact (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ b)).trans_eq hx
    simp only [realPosterior, hx, ite_true]
    rw [← ENNReal.toReal_sum (fun b _ => hfinite b), hx, ENNReal.toReal_one]
  · simp only [realPosterior, hx, ite_false, Finset.sum_const_zero]
    exact zero_le_one

theorem realPosterior_ofReal_ae (μ : Measure X) (π : X → β → ENNReal)
    (hmass : ∀ᵐ x ∂μ, ∑ b, π x b = 1) :
    ∀ᵐ x ∂μ, ∀ b, ENNReal.ofReal (realPosterior π x b) = π x b := by
  filter_upwards [hmass] with x hx
  intro b
  have hfinite : π x b ≠ ∞ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    exact (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ b)).trans_eq hx
  simp only [realPosterior, hx, ite_true, ENNReal.ofReal_toReal hfinite]

variable [MeasurableSpace β]

theorem posteriorColorLaw_congr_ae (μ : Measure X) {π π' : X → β → ENNReal}
    (h : ∀ᵐ x ∂μ, ∀ b, π x b = π' x b) : posteriorColorLaw μ π = posteriorColorLaw μ π' := by
  unfold posteriorColorLaw
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  apply withDensity_congr_ae
  exact h.mono (fun x hx => hx b)

theorem realPosterior_colorLaw (μ : Measure X) (π : X → β → ENNReal)
    (hmass : ∀ᵐ x ∂μ, ∑ b, π x b = 1) :
    posteriorColorLaw μ (fun x b => ENNReal.ofReal (realPosterior π x b)) =
      posteriorColorLaw μ π :=
  posteriorColorLaw_congr_ae μ (realPosterior_ofReal_ae μ π hmass)

theorem posteriorPairLaw_congr_ae (μ : Measure X) {π π' : X → β → ENNReal}
    (h : ∀ᵐ x ∂μ, ∀ b, π x b = π' x b) : posteriorPairLaw μ π = posteriorPairLaw μ π' := by
  unfold posteriorPairLaw
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro b' _
  congr 1
  apply withDensity_congr_ae
  filter_upwards [h] with x hx
  rw [hx b, hx b']

/-- Converting to real posterior weights for list recovery preserves the
pair law, including its original total mass. -/
theorem realPosterior_pairLaw (μ : Measure X) (π : X → β → ENNReal)
    (hmass : ∀ᵐ x ∂μ, ∑ b, π x b = 1) :
    posteriorPairLaw μ (fun x b => ENNReal.ofReal (realPosterior π x b)) =
      posteriorPairLaw μ π :=
  posteriorPairLaw_congr_ae μ (realPosterior_ofReal_ae μ π hmass)

end Submission.Obl.k4_fixed_budget_quadratic_recovery
