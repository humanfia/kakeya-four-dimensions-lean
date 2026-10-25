-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.WholeGraphStateSelection, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.Clauses

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Set MeasureTheory

noncomputable section

/-- Source-local code refinement suffices to keep whole natural states.
This applies to clipped native models, whose code agrees with the true
ancestor code only on the actual original source. -/
theorem StateClauses.restrict_coarser_code_on
    {Code : Type*} {K eps pv : ℝ} {ν : Measure O204.Split.Ln}
    {base : O204.Split.Ev → O204.Split.P3} {signal : O204.Split.Ev → ℝ}
    {E : Set O204.Split.Ev} {state : O204.Split.Ev → ℕ} {palette : Measure (Fin 2 → ℤ)}
    (h : StateClauses K eps pv ν base signal E state palette)
    (code : O204.Split.Ev → Code)
    (hfaith : ∀ x∈E, ∀ y∈E, state x=state y → code x=code y) (U : Set Code) :
    StateClauses K eps pv ν base signal (E∩code ⁻¹' U) state palette := by
  let keptStates := {n : ℕ | ∃ z∈E, state z=n ∧ code z∈U}
  have heq : E∩state ⁻¹' keptStates=E∩code ⁻¹' U := by
    ext z
    constructor
    · rintro ⟨hzE,w,hwE,hw,hU⟩
      refine ⟨hzE,?_⟩
      change code z∈U
      rw [←hfaith w hwE z hzE hw]
      exact hU
    · rintro ⟨hzE,hzU⟩
      exact ⟨hzE,z,hzE,rfl,hzU⟩
  rw [←heq]
  exact h.restrict keptStates

/-- Restricting by a code coarser than the natural state selects whole
natural states. In particular a possibly tiny whole-graph-code choice
preserves the SAME conditional breadth and original palette at no cost. -/
theorem StateClauses.restrict_coarser_code
    {Code : Type*} {K eps pv : ℝ} {ν : Measure O204.Split.Ln}
    {base : O204.Split.Ev → O204.Split.P3} {signal : O204.Split.Ev → ℝ}
    {E : Set O204.Split.Ev} {state : O204.Split.Ev → ℕ} {palette : Measure (Fin 2 → ℤ)}
    (h : StateClauses K eps pv ν base signal E state palette)
    (code : O204.Split.Ev → Code)
    (hfaith : ∀ x y, state x=state y → code x=code y) (U : Set Code) :
    StateClauses K eps pv ν base signal (E∩code ⁻¹' U) state palette := by
  let keptStates := {n : ℕ | ∃ z, state z=n ∧ code z∈U}
  have heq : E∩state ⁻¹' keptStates=E∩code ⁻¹' U := by
    ext z
    constructor
    · rintro ⟨hzE,w,hw,hU⟩
      refine ⟨hzE,?_⟩
      change code z∈U
      rw [←hfaith w z hw]
      exact hU
    · rintro ⟨hzE,hzU⟩
      exact ⟨hzE,z,rfl,hzU⟩
  rw [←heq]
  exact h.restrict keptStates

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
