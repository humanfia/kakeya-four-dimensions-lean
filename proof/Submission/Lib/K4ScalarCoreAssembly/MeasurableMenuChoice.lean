/-
Adapted from: here:o062
Original proof: o062/x0212, 01e16678, Submission/Obl/k4_scalar_mesh_projection/MeasurableMenuChoice.lean.
Finite representative menus replace arbitrary measurable-choice assumptions;
original long-row and whole-block conclusions keep the original finite prior mass.
-/

import Submission.Lib.K4ScalarCoreTools.Finalization.CartesianOriginalMass

namespace Submission.Lib.K4ScalarCoreAssembly

open Submission.Lib.K4ScalarCoreTools.Finalization



open Set MeasureTheory

/-- Fixed measurable tests in a finite menu admit a measurable choice.
Only membership in the source set is needed for the choice to be valid. -/
theorem exists_measurable_finite_menu_choice {Ω β : Type*}
    [MeasurableSpace Ω] [Nonempty β] (U : Finset β) (good : β → Ω → Prop)
    (hgood : ∀ b, MeasurableSet {ω | good b ω}) (A : Set Ω)
    (hcover : ∀ ω ∈ A, ∃ b ∈ U, good b ω) :
    ∃ f : Ω → β, (∀ Q : β → Prop, MeasurableSet {ω | Q (f ω)}) ∧
      ∀ ω ∈ A, f ω ∈ U ∧ good (f ω) ω := by
  classical
  let : MeasurableSpace β := ⊤
  have hchoice (V : Finset β) : ∃ f : Ω → β, Measurable f ∧
      ∀ ω, (∃ b ∈ V, good b ω) → f ω ∈ V ∧ good (f ω) ω := by
    induction V using Finset.induction_on with
    | empty =>
      refine ⟨fun _ => Classical.arbitrary β,measurable_const,?_⟩
      intro ω h
      simp at h
    | @insert b V hb ih =>
      obtain ⟨f,hfm,hf⟩ := ih
      let g : Ω → β := fun ω => if good b ω then b else f ω
      refine ⟨g,Measurable.ite (hgood b) measurable_const hfm,?_⟩
      intro ω h
      by_cases hω : good b ω
      · simp only [g,ite_eq_left hω]
        exact ⟨Finset.mem_insert_self _ _,hω⟩
      · obtain ⟨a,ha,hga⟩ := h
        have haV : a ∈ V := by
          rcases Finset.mem_insert.mp ha with hab | haV
          · exact (hω (by simpa only [← hab] using hga)).elim
          · exact haV
        obtain ⟨hmem,hfit⟩ := hf ω ⟨a,haV,hga⟩
        simpa only [g,ite_eq_right hω] using And.intro (Finset.mem_insert_of_mem hmem) hfit
  obtain ⟨f,hfm,hf⟩ := hchoice U
  refine ⟨f,?_,fun ω hω => hf ω (hcover ω hω)⟩
  intro Q
  change MeasurableSet (f ⁻¹' {b | Q b})
  exact hfm (by trivial)

/-- Local menus may vary with a finite observed state. The selected
label still has measurable fibers in the original source space. -/
theorem exists_measurable_observed_menu_choice {Ω I β : Type*}
    [MeasurableSpace Ω] [Fintype I] [Nonempty β]
    (obs : Ω → I) (hobs : ∀ i, MeasurableSet {ω | obs ω=i})
    (L : I → Finset β) (good : β → Ω → Prop)
    (hgood : ∀ b, MeasurableSet {ω | good b ω}) (A : Set Ω)
    (hcover : ∀ ω ∈ A, ∃ b ∈ L (obs ω), good b ω) :
    ∃ f : Ω → β, (∀ Q : β → Prop, MeasurableSet {ω | Q (f ω)}) ∧
      ∀ ω ∈ A, f ω ∈ L (obs ω) ∧ good (f ω) ω := by
  classical
  let U := (Finset.univ : Finset I).biUnion L
  let Q : β → Ω → Prop := fun b ω => b ∈ L (obs ω) ∧ good b ω
  have hmQ (b : β) : MeasurableSet {ω | Q b ω} :=
    (measurableSet_finite_observation_predicate obs hobs (fun i => b ∈ L i)).inter (hgood b)
  have hcQ (ω : Ω) (hω : ω ∈ A) : ∃ b ∈ U, Q b ω := by
    obtain ⟨b,hb,hfit⟩ := hcover ω hω
    exact ⟨b,Finset.mem_biUnion.mpr ⟨obs ω,Finset.mem_univ _,hb⟩,hb,hfit⟩
  obtain ⟨f,hfm,hf⟩ := exists_measurable_finite_menu_choice U Q hmQ A hcQ
  exact ⟨f,hfm,fun ω hω => (hf ω hω).2⟩

end Submission.Lib.K4ScalarCoreAssembly
