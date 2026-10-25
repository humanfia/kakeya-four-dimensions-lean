-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.CoverAssembly.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.CoverGrouping

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open Set MeasureTheory LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_rescaled_fibre_alternatives (ConvexCount SlabBound doubled convexExpansionLoss convexCount_mono slabBound_mono)

structure CoverGrouping {J k : ℕ} {T : TubeHierarchy J} {d θ ζ C ω H B : ℝ}
    {Y : Fin (T.layer (k + 1)).card → Set Space} (D : IndexedCovers T k d θ ζ C ω H B Y)
    (P : Finset (Fin (T.layer k).card)) where
  selection : GroupedSelection (T.parent k) H B
  parents : selection.parents = P
  mem : ∀ t i, D.index t i ∈ selection.selected ↔ t ∈ P ∧ i ∈ (D.cover t).selected
  group : ∀ t i, selection.group (D.index t i) = D.index t ((D.cover t).representative ((D.cover t).assign i))

theorem IndexedCovers.exists_grouping {J k : ℕ} {T : TubeHierarchy J} {d θ ζ C ω H B : ℝ}
    {Y : Fin (T.layer (k + 1)).card → Set Space} (D : IndexedCovers T k d θ ζ C ω H B Y)
    (P : Finset (Fin (T.layer k).card)) : Nonempty (CoverGrouping D P) := by
  obtain ⟨G, hP, hmem, hg⟩ := D.grouping P
  exact ⟨⟨G, hP, hmem, hg⟩⟩

lemma CoverGrouping.representative_injective {J k : ℕ} {T : TubeHierarchy J} {d θ ζ C ω H B : ℝ}
    {Y : Fin (T.layer (k + 1)).card → Set Space} {D : IndexedCovers T k d θ ζ C ω H B Y}
    {P : Finset (Fin (T.layer k).card)} (G : CoverGrouping D P) (t) :
    Function.Injective (D.index t ∘ (D.cover t).representative) := by
  intro i j he
  have hh := congrArg (D.cover t).assign (D.injective t he)
  simpa only [(D.cover t).representative_assign] using hh

lemma CoverGrouping.coarse_image {J k : ℕ} {T : TubeHierarchy J} {d θ ζ C ω H B : ℝ}
    {Y : Fin (T.layer (k + 1)).card → Set Space} {D : IndexedCovers T k d θ ζ C ω H B Y}
    {P : Finset (Fin (T.layer k).card)} (G : CoverGrouping D P) {t} (ht : t ∈ P) :
    (D.index t ∘ (D.cover t).representative) '' {i | True} =
      {i | i ∈ G.selection.selected ∧ G.selection.group i = i ∧ T.parent k i = t} := by
  ext i
  constructor
  · rintro ⟨a, _, rfl⟩
    refine ⟨(G.mem t _).mpr ⟨ht, (D.cover t).representative_mem _⟩, ?_, D.parent t _⟩
    simp only [Function.comp_apply, G.group, (D.cover t).representative_assign]
  · rintro ⟨hi, hgi, hpi⟩
    have hir : i ∈ Set.range (D.index t) := by rw [D.image]; exact hpi
    obtain ⟨a, rfl⟩ := hir
    exact ⟨(D.cover t).assign a, trivial, by simpa only [G.group, Function.comp_apply] using hgi⟩

lemma CoverGrouping.fine_image {J k : ℕ} {T : TubeHierarchy J} {d θ ζ C ω H B : ℝ}
    {Y : Fin (T.layer (k + 1)).card → Set Space} {D : IndexedCovers T k d θ ζ C ω H B Y}
    {P : Finset (Fin (T.layer k).card)} (G : CoverGrouping D P) {t} (ht : t ∈ P)
    (a : Fin (D.cover t).card) :
    D.index t '' {i | i ∈ (D.cover t).selected ∧ (D.cover t).assign i = a} =
      {i | i ∈ G.selection.selected ∧ G.selection.group i = D.index t ((D.cover t).representative a)} := by
  ext i
  constructor
  · rintro ⟨b, ⟨hb, hba⟩, rfl⟩
    exact ⟨(G.mem t b).mpr ⟨ht, hb⟩, by rw [G.group, hba]⟩
  · rintro ⟨hi, hgi⟩
    have hpi : T.parent k i = t := by rw [← G.selection.parent_group, hgi, D.parent]
    have hir : i ∈ Set.range (D.index t) := by rw [D.image]; exact hpi
    obtain ⟨b, rfl⟩ := hir
    have he : (D.cover t).assign b = a := by
      rw [G.group] at hgi
      have hh := congrArg (D.cover t).assign (D.injective t hgi)
      simpa only [(D.cover t).representative_assign] using hh
    exact ⟨b, ⟨((G.mem t b).mp hi).2, he⟩, rfl⟩

end WangZahlLot.Obl.wz_multiscale_finite_tower
