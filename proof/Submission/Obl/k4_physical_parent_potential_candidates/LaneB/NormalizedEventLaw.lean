import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.AeTransfer

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

open Set Metric MeasureTheory

noncomputable section

/-- The base law of the retained events has exactly their original mass,
and inherits their relative density and support without renormalization. -/
theorem event_base_law {Ω : Type*} [MeasurableSpace Ω]
    (μe : Measure Ω) (Core : Set Ω) (X : Ω → Base)
    (hCore : MeasurableSet Core) (hX : Measurable X)
    {A : ℝ}
    (hdom : ∀ E:Set Base,MeasurableSet E →
      μe (Core ∩ X ⁻¹' E) ≤ ENNReal.ofReal A*μe Core*volume E)
    (hpts : ∀ e∈Core, X e∈closedBall (0:Base) (1/2)) :
    let μ := (μe.restrict Core).map X
    μ univ=μe Core ∧
      (∀ E:Set Base,MeasurableSet E → μ E ≤ ENNReal.ofReal A*μ univ*volume E) ∧
      μ (closedBall (0:Base) (1/2))ᶜ=0 ∧
      (∀ cq:Base,∀ r:ℝ,μ (ball cq r)=μe (Core ∩ X ⁻¹' ball cq r)) := by
  intro μ
  have hmap (E:Set Base) (hE:MeasurableSet E) : μ E=μe (Core ∩ X ⁻¹' E) := by
    rw [Measure.map_apply hX hE,Measure.restrict_apply' hCore,inter_comm]
  have hmass : μ univ=μe Core := by rw [hmap _ MeasurableSet.univ]; simp
  refine ⟨hmass,?_,?_,fun cq r => hmap _ measurableSet_ball⟩
  · intro E hE
    rw [hmap E hE,hmass]
    exact hdom E hE
  · rw [hmap _ measurableSet_closedBall.compl]
    have heq : Core ∩ X ⁻¹' (closedBall (0:Base) (1/2))ᶜ=∅ := by
      ext e
      simp only [mem_inter_iff,mem_preimage,mem_compl_iff,mem_empty_iff_false,
        iff_false,not_and]
      exact fun he => not_not.mpr (hpts e he)
    rw [heq,measure_empty]

/-- A continuous bound at every retained event holds almost everywhere
for its base law, even if the function is unspecified outside the support. -/
theorem ae_base_function_bound {Ω : Type*} [MeasurableSpace Ω]
    (μe : Measure Ω) (Core : Set Ω) (X : Ω → Base) (hX : Measurable X)
    {f:Base → ℝ} {V:ℝ}
    (hcont : ContinuousOn f (closedBall (0:Base) (1/2)))
    (hpts : ∀ e∈Core, X e∈closedBall (0:Base) (1/2) ∧ |f (X e)| ≤ V) :
    ∀ᵐ x ∂(μe.restrict Core).map X, |f x| ≤ V := by
  let G := {x:Base | x∈closedBall (0:Base) (1/2) ∧ |f x| ≤ V}
  have hG : MeasurableSet G :=
    (hcont.abs.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_Iic).measurableSet
  apply ae_map_restrict_of_bad_set μe Core X hX (fun x => |f x| ≤ V) Gᶜ hG.compl
  · intro x hx hxG
    exact hx hxG.2
  · intro e he hn
    exact hn (hpts e he)

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
