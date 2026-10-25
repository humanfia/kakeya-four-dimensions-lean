import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.RootReadouts

/-! The original world weight is positive almost everywhere under the
actual tagged mixture and every pulled-back dominated residual. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures

open MeasureTheory Set
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

theorem worldMixture_positive_weight_ae (p : Code) (k : ℕ) :
    ∀ᵐ z ∂worldMixture p k, 0 < ω p k z.1 := by
  have hm : MeasurableSet {z : Fin (W p k) × State | 0 < ω p k z.1} :=
    measurableSet_lt measurable_const ((measurable_of_countable (ω p k)).comp measurable_fst)
  rw [worldMixture, ← Measure.sum_fintype]
  apply Measure.ae_sum_iff.mpr
  intro g
  by_cases hg : 0 < ω p k g
  · apply Measure.smul_absolutelyContinuous.ae_le
    apply (ae_map_iff measurable_prodMk_left.aemeasurable hm).mpr
    exact Filter.Eventually.of_forall fun _ => hg
  · have hw : ENNReal.ofReal (ω p k g) = 0 :=
      ENNReal.ofReal_eq_zero.mpr (le_of_not_gt hg)
    rw [hw, zero_smul]
    simp

/-- Original world labels of a view retain positive weights under the
same common law, independently of how its original total mass is scaled. -/
theorem RefinementChain.positive_weight_pullback_ae {p z : Code}
    (chain : RefinementChain p z) (k : ℕ)
    (ρ : Measure (Fin (W z k) × State)) (hρ : ρ ≪ worldMixture z k) :
    ∀ᵐ u ∂ρ, 0 < ω p (chain.sample k) (chain.pullback k u).1 :=
  hρ.ae_le (chain.pullback_ae k (worldMixture_positive_weight_ae p (chain.sample k)))

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures
