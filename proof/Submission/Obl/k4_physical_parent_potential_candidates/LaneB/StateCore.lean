import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.StateSampling
import Submission.Lib.K4ScalarCoreAssembly.PositiveCodeCore

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open Set MeasureTheory GeneralPositionSampling
open scoped ENNReal

/-- Remove only null original code classes and select seven original events
of the same state at every remaining event. The restricted source law is
unchanged, and the selected directions may vary from state to state. -/
theorem exists_seven_state_core {X I : Type*} [MeasurableSpace X]
    [MeasurableSpace I] [MeasurableSingletonClass I] [Countable I]
    (μ : Measure X) (G : Set X) (hG : MeasurableSet G) (hfin : μ G ≠ ⊤)
    (code : X → I) (hcode : Measurable code)
    (vel : X → EuclideanSpace ℝ (Fin 2)) (hvel : Measurable vel)
    {δ : ℝ} (hδ : 0 < δ) {κ : ℝ≥0∞} (hκ : 686*κ < 1)
    (hb : ∀ i : I, ∀ (m : EuclideanSpace ℝ (Fin 2)) (t : ℝ), ‖m‖ = 1 →
      μ ((G ∩ code ⁻¹' {i}) ∩ vel ⁻¹' {x | |inner ℝ m x-t| ≤ δ}) ≤
        κ*μ (G ∩ code ⁻¹' {i})) :
    ∃ U : Set X, MeasurableSet U ∧ U ⊆ G ∧ μ.restrict U = μ.restrict G ∧
      ∀ x ∈ U, ∃ e : Fin 7 → X,
        (∀ i, e i ∈ G ∧ code (e i) = code x) ∧
        ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
          δ^2 ≤ |tripleDet (vel (e i)) (vel (e j)) (vel (e k))| := by
  obtain ⟨U,hUm,hUG,hlaw,hpos⟩ :=
    Submission.Lib.K4ScalarCoreAssembly.exists_original_positive_code_core μ G hG code hcode
  refine ⟨U,hUm,hUG,hlaw,?_⟩
  intro x hx
  have hS : MeasurableSet (G ∩ code ⁻¹' {code x}) := hG.inter (hcode (measurableSet_singleton _))
  have hp : μ (G ∩ code ⁻¹' {code x}) ≠ 0 := hpos x hx
  have hf : μ (G ∩ code ⁻¹' {code x}) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (measure_mono inter_subset_left)
  obtain ⟨e,he,hdet⟩ := exists_seven_of_broad_cell μ (G ∩ code ⁻¹' {code x}) hS hp hf
    vel hvel hδ hκ (hb (code x))
  refine ⟨e,fun i => ?_,hdet⟩
  exact ⟨(he i).1, (he i).2⟩

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
