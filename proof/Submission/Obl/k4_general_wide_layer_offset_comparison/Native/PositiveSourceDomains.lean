-- Adapted from this LOT tree, obligation o254, branch x0898, commit f25a0cc9, file Submission/Obl/k4_general_parent_wide_layer_candidates/Native/PositiveSourceDomains.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
/- Adapted from this LOT tree, obligation o200, session x0934, commit 3ef9d3b45123d3245f500a2dc2bd85270a8fff3d,
   Submission/Obl/k4_finite_projected_horizontal_candidates/PositiveSourceDomains.lean. Original source attributions are retained below. -/
import Mathlib
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.FiniteDomainEnumeration
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SourceSheetFamilies
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.MeshPairLaw
import Submission.Obl.k4_two_velocity_row_list_completion.MeasureTable

/-! Enumerate only positive literal source domains and keep one full source core. -/

namespace Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison

open MeasureTheory Set
open scoped Classical

noncomputable section

theorem positive_source_domains {Ω Q : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    (μ : Measure Ω) (hμ : μ univ ≠ 0) (state : Ω → Q) (hstate : Measurable state)
    (menu : Finset Q) (hmenu : ∀ᵐ p ∂μ, state p ∈ menu)
    (P : Ω → Prop) (hP : ∀ᵐ p ∂μ, P p) :
    ∃ (S : Finset Q), S ⊆ menu ∧ ∃ n : ℕ, 0 < n ∧
      ∃ (code : Ω → Fin n) (decode : Fin n → Q) (G : Set Ω),
        Measurable code ∧ Function.Injective decode ∧ (∀ i, decode i ∈ S) ∧
        MeasurableSet G ∧ μ Gᶜ = 0 ∧
        (∀ p ∈ G, P p ∧ state p ∈ S ∧ decode (code p) = state p) ∧
        (∀ i, codePieces μ code i univ ≠ 0) ∧
        ∀ i, ∃ p ∈ G, code p = i := by
  let S := Submission.Obl.k4_two_velocity_row_list_completion.positiveStates
    μ (fun _ : Ω => ()) state menu ()
  have hS : ∀ᵐ p ∂μ, state p ∈ S :=
    Submission.Obl.k4_two_velocity_row_list_completion.ae_mem_positiveStates
      μ (fun _ : Ω => ()) state menu hmenu
  have hsub : S ⊆ menu := Finset.filter_subset _ _
  have hpos (q : Q) (hq : q ∈ S) : μ {p | state p = q} ≠ 0 := by
    simpa only [S, Submission.Obl.k4_two_velocity_row_list_completion.positiveStates,
      Finset.mem_filter, true_and] using (Finset.mem_filter.mp hq).2
  have hSnonempty : S.Nonempty := by
    obtain ⟨p, -, hp⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hμ
      (ae_restrict_of_ae hS : ∀ᵐ p ∂μ.restrict univ, state p ∈ S)
    exact ⟨state p, hp⟩
  obtain ⟨n, hn, code, decode, hcode, hinj, hdecode, hexact⟩ :=
    finite_domain_enumeration state hstate S hSnonempty
  obtain ⟨G, hG, hnull, hgood⟩ := measurable_full_source μ (fun p => P p ∧ state p ∈ S)
    (hP.and hS)
  have hGa : ∀ᵐ p ∂μ, p ∈ G := ae_iff.mpr hnull
  have hcore (p : Ω) (hp : p ∈ G) : P p ∧ state p ∈ S ∧ decode (code p) = state p :=
    ⟨(hgood p hp).1, (hgood p hp).2, hexact p (hgood p hp).2⟩
  have hmass (i : Fin n) : μ {p | code p = i} ≠ 0 := by
    have heq : {p | code p = i} =ᵐ[μ] {p | state p = decode i} := by
      filter_upwards [hGa] with p hp
      have hc := (hcore p hp).2.2
      apply propext
      constructor
      · intro hi
        exact hc.symm.trans (congrArg decode hi)
      · intro hi
        exact hinj (hc.trans hi)
    rw [measure_congr heq]
    exact hpos (decode i) (hdecode i)
  refine ⟨S, hsub, n, hn, code, decode, G, hcode, hinj, hdecode, hG, hnull, hcore, ?_, ?_⟩
  · intro i
    simpa only [codePieces, Measure.restrict_apply_univ] using hmass i
  · intro i
    obtain ⟨p, hp, hGp⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae (hmass i)
      (ae_restrict_of_ae hGa : ∀ᵐ p ∂μ.restrict {p | code p = i}, p ∈ G)
    exact ⟨p, hGp, hp⟩

end

end Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison
