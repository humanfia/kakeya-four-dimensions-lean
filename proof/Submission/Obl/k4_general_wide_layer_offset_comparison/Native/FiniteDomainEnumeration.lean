-- Adapted from this LOT tree, obligation o254, branch x0898, commit f25a0cc9, file Submission/Obl/k4_general_parent_wide_layer_candidates/Native/FiniteDomainEnumeration.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
/- Adapted from this LOT tree, obligation o200, session x0934, commit 3ef9d3b45123d3245f500a2dc2bd85270a8fff3d,
   Submission/Obl/k4_finite_projected_horizontal_candidates/FiniteDomainEnumeration.lean. Original source attributions are retained below. -/
import Mathlib
import Submission.Lib.K4ScalarCoreAssembly.MeasurableMenuChoice

/-! Measurable enumeration of the literal finite common-domain code menu. -/

namespace Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison

open MeasureTheory Set

noncomputable section

/-- Enumerate a finite literal-code menu once. The observed code is preserved
pointwise on its valid source set, and the decoder is injective. -/
theorem finite_domain_enumeration {Ω Q : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (state : Ω → Q) (hstate : Measurable state) (S : Finset Q) (hS : S.Nonempty) :
    ∃ (n : ℕ), 0 < n ∧ ∃ (code : Ω → Fin n) (decode : Fin n → Q),
      Measurable code ∧ Function.Injective decode ∧ (∀ i, decode i ∈ S) ∧
      ∀ p, state p ∈ S → decode (code p) = state p := by
  classical
  let e : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  let decode : Fin (Fintype.card S) → Q := fun i => (e.symm i).val
  have hn : 0 < Fintype.card S := by simpa using Finset.card_pos.mpr hS
  letI : Nonempty (Fin (Fintype.card S)) := ⟨⟨0, hn⟩⟩
  let A : Set Ω := {p | state p ∈ S}
  have hgood (i : Fin (Fintype.card S)) : MeasurableSet {p | state p = decode i} :=
    hstate (measurableSet_singleton _)
  have hcover (p : Ω) (hp : p ∈ A) :
      ∃ i ∈ (Finset.univ : Finset (Fin (Fintype.card S))), state p = decode i := by
    refine ⟨e ⟨state p, hp⟩, Finset.mem_univ _, ?_⟩
    simp only [decode, Equiv.symm_apply_apply]
  obtain ⟨code, hcode, hvalid⟩ := Submission.Lib.K4ScalarCoreAssembly.exists_measurable_finite_menu_choice
    Finset.univ (fun i p => state p = decode i) hgood A hcover
  refine ⟨Fintype.card S, hn, code, decode, (fun E _ => hcode (fun i => i ∈ E)), ?_, ?_, ?_⟩
  · intro i j hij
    exact e.symm.injective (Subtype.ext hij)
  · intro i
    exact (e.symm i).property
  · intro p hp
    exact (hvalid p hp).2.symm

end

end Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison
