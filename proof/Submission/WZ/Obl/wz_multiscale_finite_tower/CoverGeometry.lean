-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.CoverGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.CoverAssembly

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open Set MeasureTheory LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_rescaled_fibre_alternatives
  (ConvexCount SlabBound doubled convexExpansionLoss convexCount_mono slabBound_mono)

theorem CoverGrouping.geometry {J k : ℕ} {T : TubeHierarchy J} {d θ ζ C ω H B r K L F : ℝ}
    {Y : Fin (T.layer (k + 1)).card → Set Space} {D : IndexedCovers T k d θ ζ C ω H B Y}
    {P : Finset (Fin (T.layer k).card)} (G : CoverGrouping D P)
    {u : Space} {h : ℝ} (A : HierarchyAlignment u h T) (hk : k < J)
    (hd : 0 ≤ d) (hr : 0 < (T.layer k).radius) (hs : 0 < (T.layer (k + 1)).radius)
    (hds : d ≤ (T.layer (k + 1)).radius) (hH : 0 < H) (hB : 0 ≤ B) (hr1 : r ≤ 1)
    (hρs : ∀ t ∈ P, (T.layer (k + 1)).radius ≤ (D.cover t).radius)
    (hρ1 : ∀ t ∈ P, (D.cover t).radius ≤ 1 / 160)
    (hρr : ∀ t ∈ P, 1024 * (D.cover t).radius ≤ r)
    (hK : ∀ t ∈ P, (r / (D.cover t).radius) ^ 2 * d ^ (-ζ) * convexExpansionLoss 6 ≤ K)
    (hL : 2000000 * (B * d ^ (-θ) / H) ≤ L)
    (hF : ∀ t ∈ P, 262144 * (r / (D.cover t).radius) ^ 2 * d ^ (-ζ) ≤ F) :
    GroupedGeometry T G.selection d r K L F := by
  have hcap (t) (i) := A.direction_cap (k + 1) (by omega) (by omega) (D.index t i)
  have hmid (t) (i) : ‖axisMidpoint (((T.layer (k + 1)).position ∘ D.index t) i)
      (((T.layer (k + 1)).direction ∘ D.index t) i)‖ ≤ 1 :=
    (A.midpoint (k + 1) (by omega) (by omega) (D.index t i)).trans (by norm_num)
  have halign (t) (i) := A.aligned (k + 1) (by omega) (by omega) (D.index t i)
  have hunit (t) (i) := (T.layer (k + 1)).unit (D.index t i)
  have h320 (t) (ht : t ∈ P) : 320 * (D.cover t).radius ≤ r := by
    have hh := hρr t ht
    have hp := (D.cover t).radius_pos
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    let t := T.parent k i
    have hir : i ∈ Set.range (D.index t) := by rw [D.image]; rfl
    obtain ⟨a, ha⟩ := hir
    have hia : D.index t a ∈ G.selection.selected := ha ▸ hi
    obtain ⟨ht, has⟩ := (G.mem t a).mp hia
    have hh := ((D.cover t).representative_contains hs (hρs t ht) (hρ1 t ht)
      (hunit t) (hcap t) (hmid t) (halign t) a has).trans (Metric.thickening_mono (h320 t ht) _)
    simpa only [Function.comp_apply, ← G.group, ha] using hh
  · intro i hi
    let t := T.parent k i
    have hir : i ∈ Set.range (D.index t) := by rw [D.image]; rfl
    obtain ⟨a, ha⟩ := hir
    have hia : D.index t a ∈ G.selection.selected := ha ▸ hi
    obtain ⟨ht, has⟩ := (G.mem t a).mp hia
    have hh := (D.cover t).representative_child_buffer hds hs (hρs t ht) (hρ1 t ht)
      (hρr t ht) (hunit t) (hcap t) (hmid t) (halign t) a has
    simpa only [Function.comp_apply, ← G.group, ha] using hh
  · intro t
    by_cases ht : t ∈ P
    · have hh := convexCount_image (convexCount_mono (hK t ht)
        ((D.cover t).representative_count hd hs (h320 t ht) hr1 (hunit t) (hmid t)))
        (D.index t ∘ (D.cover t).representative) (G.representative_injective t)
        (G.coarse_image ht) (V := fun i => Tube r ((T.layer (k + 1)).position i) ((T.layer (k + 1)).direction i))
        (fun _ _ => rfl)
      exact hh
    · intro W hW
      have he : {i | (i ∈ G.selection.selected ∧ G.selection.group i = i ∧ T.parent k i = t) ∧
          Tube r ((T.layer (k + 1)).position i) ((T.layer (k + 1)).direction i) ⊆ W} = ∅ := by
        ext i
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro hi hW
        exact ht (by simpa only [← G.parents, hi.2.2] using G.selection.selected_parent i hi.1)
      rw [he]
      simp
  · intro t
    by_cases ht : t ∈ P
    · exact slabBound_image (slabBound_mono hL
        ((D.cover t).representative_coarse_slab (D.frame t) hd hr hs hH hB
          (hρs t ht) (hρ1 t ht) (h320 t ht) (hcap t) (hmid t) (halign t)))
        (D.index t ∘ (D.cover t).representative) (G.representative_injective t)
        (G.coarse_image ht) (fun _ _ => rfl)
    · intro u' t' r' hu hr'
      have he : {i | (i ∈ G.selection.selected ∧ G.selection.group i = i ∧ T.parent k i = t) ∧
          Tube r ((T.layer (k + 1)).position i) ((T.layer (k + 1)).direction i) ⊆
            doubled (T.layer k).radius ((T.layer k).position t) ((T.layer k).direction t) ∩
              {p | |inner ℝ u' p - t'| ≤ r'}} = ∅ := by
        ext i
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro hi hW
        exact ht (by simpa only [← G.parents, hi.2.2] using G.selection.selected_parent i hi.1)
      rw [he]
      simp
  · intro i hi hgi
    let t := T.parent k i
    have ht : t ∈ P := by simpa only [← G.parents] using G.selection.selected_parent i hi
    have hir : i ∈ (D.index t ∘ (D.cover t).representative) '' {a | True} := by
      rw [G.coarse_image ht]
      exact ⟨hi, hgi, rfl⟩
    obtain ⟨a, _, ha⟩ := hir
    have hh := slabBound_image (slabBound_mono (hF t ht)
      ((D.cover t).representative_fine_slab hs (hρs t ht) (hρ1 t ht) (h320 t ht) hr1
        (hunit t) (hcap t) (hmid t) (halign t) a))
      (D.index t) (D.injective t) (G.fine_image ht a)
      (V := fun i => Tube (T.layer (k + 1)).radius ((T.layer (k + 1)).position i) ((T.layer (k + 1)).direction i))
      (fun _ _ => rfl)
    change D.index t ((D.cover t).representative a) = i at ha
    simpa only [Function.comp_apply, ha] using hh

end WangZahlLot.Obl.wz_multiscale_finite_tower
