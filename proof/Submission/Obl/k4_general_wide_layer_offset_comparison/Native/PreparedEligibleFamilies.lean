-- Adapted from this LOT tree, obligation o200, branch x0934, commit 2510f406, file Submission/Obl/k4_finite_projected_horizontal_candidates/PreparedEligibleFamilies.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.Native.
import Mathlib
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.PreparedDomainMeshes
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.EligibleDomainFamilies

/-! Keep exactly the geometrically eligible original labels on each prepared domain. -/

namespace Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison

open MeasureTheory Set
open Submission.Obl.k4_general_parent_projected_layers
open scoped Classical

noncomputable section

namespace PreparedDomainData

variable {α : Type} [MeasurableSpace α] {p : Parameters} {a : PreparedModel α}
  {k : ℕ} {s H q χ m : ℝ} {L : ProjLayer α} {ζ : Measure (α × ℝ)} {Extra : α × ℝ → Prop}
  (D : PreparedDomainData p a k s H q χ m L ζ Extra)

theorem eligible_true_family (u : Fin D.n) {aTable : ℝ} {K : NNReal}
    {base : α × ℝ → EuclideanSpace ℝ (Fin 3)} {signal : α × ℝ → ℝ}
    (F : OriginalSheetFamily (D.law u) 4 aTable K base signal)
    (oldIdx : Fin F.n → Fin (a.n k s) × Bool) (hidx : Function.Injective oldIdx)
    (hsource : ∀ i z, z ∈ F.witness i → z ∈ D.core u ∧
      z.1 ∈ a.B k s (oldIdx i).1 ∧ z.2 ∈ a.block k s (oldIdx i).1) :
    ∃ (F' : OriginalSheetFamily (D.law u) 4 aTable K base signal)
      (idx : Fin F'.n → Fin (a.n k s) × Bool),
      Function.Injective idx ∧ (∀ i, D.decode u ∈ D.trueMenus (idx i).1) ∧
      (∀ i z, z ∈ F'.witness i → z ∈ D.core u ∧
        z.1 ∈ a.B k s (idx i).1 ∧ z.2 ∈ a.block k s (idx i).1) ∧
      ∃ retain : Fin F'.n → Fin F.n, Function.Injective retain ∧
        (∀ i, idx i = oldIdx (retain i)) ∧
        (∀ i, F'.f i = F.f (retain i)) ∧ (∀ i, F'.witness i = F.witness (retain i)) ∧
        ∀ᵐ z ∂D.law u, retain (F'.index z) = F.index z := by
  let S : Finset (Fin F.n) := Finset.univ.filter (fun i => D.decode u ∈ D.trueMenus (oldIdx i).1)
  have heligible : ∀ᵐ z ∂D.law u, F.index z ∈ S := by
    filter_upwards [F.assigned] with z hz
    obtain ⟨hc, hB, ht⟩ := hsource (F.index z) z hz
    have hp := D.core_point hc
    have hm := D.true_cover (oldIdx (F.index z)).1 z.1 hB hp.1.coefficients z.2 ht
    rw [hp.2] at hm
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩
  obtain ⟨F', retain, -, hinj, hmem, hsame, hW, hcurrent⟩ :=
    F.subfamily (D.positive_domain u) S heligible
  let idx := oldIdx ∘ retain
  refine ⟨F', idx, hidx.comp hinj, ?_, ?_, retain, hinj, (fun _ => rfl), hsame, hW, hcurrent⟩
  · intro i
    exact (Finset.mem_filter.mp (hmem i)).2
  · intro i z hz
    rw [hW i] at hz
    exact hsource (retain i) z hz

theorem eligible_projected_family (u : Fin D.n) {aTable : ℝ} {K : NNReal}
    {base : α × ℝ → EuclideanSpace ℝ (Fin 3)} {signal : α × ℝ → ℝ}
    (F : OriginalSheetFamily (D.law u) 4 aTable K base signal)
    (oldIdx : Fin F.n → Fin L.n) (hidx : Function.Injective oldIdx)
    (hsource : ∀ i z, z ∈ F.witness i → z ∈ D.core u ∧ z.1 ∈ L.C (oldIdx i)) :
    ∃ (F' : OriginalSheetFamily (D.law u) 4 aTable K base signal)
      (idx : Fin F'.n → Fin L.n),
      Function.Injective idx ∧ (∀ i, D.decode u ∈ D.projectedMenus (idx i)) ∧
      (∀ i z, z ∈ F'.witness i → z ∈ D.core u ∧ z.1 ∈ L.C (idx i)) ∧
      ∃ retain : Fin F'.n → Fin F.n, Function.Injective retain ∧
        (∀ i, idx i = oldIdx (retain i)) ∧
        (∀ i, F'.f i = F.f (retain i)) ∧ (∀ i, F'.witness i = F.witness (retain i)) ∧
        ∀ᵐ z ∂D.law u, retain (F'.index z) = F.index z := by
  let S : Finset (Fin F.n) := Finset.univ.filter (fun i => D.decode u ∈ D.projectedMenus (oldIdx i))
  have heligible : ∀ᵐ z ∂D.law u, F.index z ∈ S := by
    filter_upwards [F.assigned] with z hz
    obtain ⟨hc, hC⟩ := hsource (F.index z) z hz
    have hp := D.core_point hc
    have hm := D.projected_cover (oldIdx (F.index z)) z.1 hC z.2 hp.1.time
    rw [hp.2] at hm
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩
  obtain ⟨F', retain, -, hinj, hmem, hsame, hW, hcurrent⟩ :=
    F.subfamily (D.positive_domain u) S heligible
  let idx := oldIdx ∘ retain
  refine ⟨F', idx, hidx.comp hinj, ?_, ?_, retain, hinj, (fun _ => rfl), hsame, hW, hcurrent⟩
  · intro i
    exact (Finset.mem_filter.mp (hmem i)).2
  · intro i z hz
    rw [hW i] at hz
    exact hsource (retain i) z hz

end PreparedDomainData

end

end Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison
