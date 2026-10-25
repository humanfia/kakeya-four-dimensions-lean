-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.FiniteStateLaws, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/FiniteStateLaws.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/FiniteStateLaws.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.FiniteDomainEnumeration
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity.CellBreadth

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set

noncomputable section

/-- Finite enumeration preserves the literal original state laws. -/
theorem enumerated_fibre_law {X I : Type*} [MeasurableSpace X] {m : ℕ}
    (μ : Measure X) (state : X → I) (code : X → Fin m) (decode : Fin m → I)
    (hinj : Function.Injective decode) (hvalid : ∀ᵐ x ∂μ, decode (code x) = state x) (i : Fin m) :
    μ.restrict (code ⁻¹' {i}) = μ.restrict (state ⁻¹' {decode i}) := by
  apply Measure.restrict_congr_set
  filter_upwards [hvalid] with x hx
  apply propext
  change code x = i ↔ state x = decode i
  rw [← hx]
  exact ⟨fun h => congrArg decode h, fun h => hinj h⟩

theorem finite_state_enumeration_with_laws {X I : Type*} [MeasurableSpace X]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    (state : X → I) (hstate : Measurable state) (S : Finset I) (hS : S.Nonempty) :
    ∃ m : ℕ, 0 < m ∧ m ≤ S.card ∧
      ∃ (code : X → Fin m) (decode : Fin m → I), Measurable code ∧
        Function.Injective decode ∧ (∀ i, decode i ∈ S) ∧
        (∀ x, state x ∈ S → decode (code x) = state x) ∧
        ∀ μ : Measure X, (∀ᵐ x ∂μ, state x ∈ S) → ∀ i : Fin m,
          μ.restrict (code ⁻¹' {i}) = μ.restrict (state ⁻¹' {decode i}) := by
  classical
  obtain ⟨m, hm, code, decode, hcode, hinj, hdecode, hvalid⟩ :=
    k4_narrow_projected_row_parents.Cmp.SheetComparison.finite_domain_enumeration state hstate S hS
  have hcard : m ≤ S.card := by
    have hh := Fintype.card_le_of_injective (fun i : Fin m => (⟨decode i, hdecode i⟩ : ↥S))
      (fun i j hij => hinj (congrArg Subtype.val hij))
    simpa only [Fintype.card_fin, Fintype.card_coe] using hh
  refine ⟨m, hm, hcard, code, decode, hcode, hinj, hdecode, hvalid, ?_⟩
  intro μ hμ i
  exact enumerated_fibre_law μ state code decode hinj
    (hμ.mono (fun x hx => hvalid x hx)) i

/-- A retained line prior supplies the same original incidence law on
any source all of whose lines satisfy that earlier retention. -/
theorem restrict_prior_incidence_eq {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] (A : Set X) (E : Set (X × ℝ)) (hE : MeasurableSet E)
    (hEA : E ⊆ A ×ˢ univ) :
    (((ν.restrict A).prod volume).restrict E) = (ν.prod volume).restrict E := by
  have hh : (ν.restrict A).prod (volume : Measure ℝ) =
      (ν.prod (volume : Measure ℝ)).restrict (A ×ˢ (univ : Set ℝ)) := by
    simpa only [Measure.restrict_univ] using
      (Measure.prod_restrict (μ := ν) (ν := (volume : Measure ℝ)) A (univ : Set ℝ))
  rw [hh, Measure.restrict_restrict hE, inter_eq_left.mpr hEA]

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
