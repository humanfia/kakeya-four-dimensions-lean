import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.SubmeasurePaths
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.IntermediateLiftSupport

/-! Common tagged-law supports and masks descend to all original worlds,
including original worlds of zero weight. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_scalar_true_terminal_lifting (ChartW)
open IntermediateLiftSupport

noncomputable section

theorem originalFibers_null_of_tagged_null {p : Code} {k : ℕ}
    (ρ : Measure (Fin (W p k) × State)) (E : Fin (W p k) → Set State)
    (hmeas : ∀ g, MeasurableSet (E g))
    (hnull : ρ {u | u.2 ∈ E u.1} = 0) (g : Fin (W p k)) :
    originalFibers p k ρ g (E g) = 0 := by
  have hsub : ({g} ×ˢ E g) ⊆ {u | u.2 ∈ E u.1} := by
    rintro ⟨a, z⟩ ⟨ha, hz⟩
    have ha' : a = g := ha
    subst a
    exact hz
  rw [originalFibers, Measure.smul_apply, worldFiber_apply _ _ (hmeas g),
    measure_mono_null hsub hnull, smul_eq_mul, mul_zero]

/-- A common-law cover by unchanged original witnesses gives the same
cover in every original within-world submeasure. -/
theorem originalFibers_chart_cover {p : Code} {B k : ℕ} {r b h ε : ℝ} {flag : Bool}
    (Q : ChartW p B r b h ε flag k) (ρ : Measure (Fin (W p k) × State))
    (hcover : ∀ᵐ u ∂ρ, u ∈ chartRegion Q) (g : Fin (W p k)) :
    originalFibers p k ρ g {z | ∃ i, Q.γ i = g ∧ z ∈ Q.C i}ᶜ = 0 := by
  let E : Fin (W p k) → Set State :=
    fun a => ((Prod.mk a) ⁻¹' chartRegion Q)ᶜ
  have hE (a) : MeasurableSet (E a) :=
    ((measurableSet_chartRegion Q).preimage measurable_prodMk_left).compl
  apply originalFibers_null_of_tagged_null ρ E hE
  exact hcover

namespace RefinementChain

variable {p z : Code} (chain : RefinementChain p z) (k : ℕ)
  {η : Measure (Fin (W z k) × State)}

theorem submeasureLaw_null (E : Set (Fin (W p (chain.sample k)) × State))
    (hE : MeasurableSet E) (hnull : η (chain.pullback k ⁻¹' E) = 0) :
    chain.submeasureLaw k η E = 0 := by
  rw [submeasureLaw, Measure.smul_apply,
    Measure.map_apply (chain.measurable_pullback k) hE, hnull, smul_eq_mul, mul_zero]

/-- A common mask of the final law removes each prescribed event in all
original worlds of this view. -/
theorem submeasureWorldLaw_null (E : Fin (W p (chain.sample k)) → Set State)
    (hmeas : ∀ g, MeasurableSet (E g))
    (hnull : η (chain.pullback k ⁻¹' {u | u.2 ∈ E u.1}) = 0)
    (g : Fin (W p (chain.sample k))) :
    chain.submeasureWorldLaw k η g (E g) = 0 := by
  apply originalFibers_null_of_tagged_null _ E hmeas
  apply chain.submeasureLaw_null k _ ?_ hnull
  have heq : {u : Fin (W p (chain.sample k)) × State | u.2 ∈ E u.1} =
      ⋃ a, ({a} ×ˢ E a) := by
    ext u
    simp
  rw [heq]
  exact MeasurableSet.iUnion fun a => (measurableSet_singleton a).prod (hmeas a)

/-- The universal TRUE-layer cover from a chosen path applies to every
later dominated common law, with its original weights and priors. -/
theorem submeasureWorldLaw_chart_cover {B : ℕ} {r b h ε : ℝ} {flag : Bool}
    (Q : ChartW p B r b h ε flag (chain.sample k))
    (hη : η ≤ normalizedWorldMixture z k)
    (hQ : ∀ ρ : Measure (Fin (W z k) × State), ρ ≪ worldMixture z k →
      ∀ᵐ u ∂ρ.map (chain.pullback k), u ∈ chartRegion Q)
    (g : Fin (W p (chain.sample k))) :
    chain.submeasureWorldLaw k η g {u | ∃ i, Q.γ i = g ∧ u ∈ Q.C i}ᶜ = 0 := by
  have hηac : η ≪ worldMixture z k :=
    (Measure.absolutelyContinuous_of_le hη).trans Measure.smul_absolutelyContinuous
  apply originalFibers_chart_cover Q (chain.submeasureLaw k η)
  exact Measure.smul_absolutelyContinuous.ae_le (hQ η hηac)

end RefinementChain

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures
