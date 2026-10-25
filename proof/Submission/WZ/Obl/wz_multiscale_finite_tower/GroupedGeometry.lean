-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.GroupedGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.GroupRetention
import Submission.WZ.Obl.wz_multiscale_finite_tower.BufferedGeometry

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory Set LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_rescaled_fibre_alternatives (ConvexCount SlabBound doubled convexCount_mono slabBound_mono)

structure GroupedGeometry {J k : ℕ} (T : TubeHierarchy J) {H B : ℝ}
    (G : GroupedSelection (T.parent k) H B) (d r K L F : ℝ) : Prop where
  containment : ∀ i ∈ G.selected,
    Tube (T.layer (k + 1)).radius ((T.layer (k + 1)).position i) ((T.layer (k + 1)).direction i) ⊆
      Tube r ((T.layer (k + 1)).position (G.group i)) ((T.layer (k + 1)).direction (G.group i))
  buffer : ∀ i ∈ G.selected,
    Tube d ((T.layer (k + 1)).position i) ((T.layer (k + 1)).direction i) ⊆
      Tube ((31 / 32) * r) ((T.layer (k + 1)).position (G.group i)) ((T.layer (k + 1)).direction (G.group i))
  count : ∀ t, ConvexCount r K (fun i => i ∈ G.selected ∧ G.group i = i ∧ T.parent k i = t)
    (fun i => Tube r ((T.layer (k + 1)).position i) ((T.layer (k + 1)).direction i))
  slab : ∀ t, SlabBound (doubled (T.layer k).radius ((T.layer k).position t) ((T.layer k).direction t))
    L (fun i => i ∈ G.selected ∧ G.group i = i ∧ T.parent k i = t)
    (fun i => Tube r ((T.layer (k + 1)).position i) ((T.layer (k + 1)).direction i))
  fine_slab : ∀ t ∈ G.selected, G.group t = t →
    SlabBound (doubled r ((T.layer (k + 1)).position t) ((T.layer (k + 1)).direction t))
      F (fun i => i ∈ G.selected ∧ G.group i = t)
      (fun i => Tube (T.layer (k + 1)).radius ((T.layer (k + 1)).position i) ((T.layer (k + 1)).direction i))

lemma RestrictedGrouping.child_selected {J k : ℕ} {T : TubeHierarchy J} {H B r : ℝ}
    {G : GroupedSelection (T.parent k) H B} {S : Finset (Fin (T.layer J).card)}
    {R : HierarchyRestriction T S} (I : RestrictedGrouping T G R r)
    (i : Fin (R.tree.layer (k + 1)).card) : R.map (k + 1) i ∈ G.selected := by
  have hh : R.map (k + 1) i ∈ R.map (k + 1) '' {j | I.lower j = I.lower i} := ⟨i, rfl, rfl⟩
  rw [I.fine_image] at hh
  exact hh.1

theorem RestrictedGrouping.upper_control {J k : ℕ} {T : TubeHierarchy J}
    {H B d θ θ' g g' gap gap' r K L F : ℝ}
    {G : GroupedSelection (T.parent k) H B} {S : Finset (Fin (T.layer J).card)}
    {R : HierarchyRestriction T S} (I : RestrictedGrouping T G R r)
    (C : HierarchyControl d θ g gap T) (Q : GroupedGeometry T G d r K L F) (hk : k < J)
    (hd : 0 < d) (hr : 0 < r) (hr64 : r ≤ (T.layer k).radius / 64)
    (hlo : d ^ g' * (T.layer k).radius ≤ r) (hhi : r ≤ d ^ gap' * (T.layer k).radius)
    (hK : K ≤ d ^ (-θ'))
    (hL : ∀ t : Fin (R.tree.layer k).card,
      L * {i | i ∈ G.selected ∧ G.group i = i ∧ T.parent k i = R.map k t}.ncard ≤
        d ^ (-θ') * {i | I.upper i = t}.ncard) :
    EdgeControl d θ' g' gap' (R.tree.layer k) I.middle I.upper := by
  have hp := C.positive k hk.le
  refine ⟨by simpa only [R.radius] using hp, by simpa only [I.radius] using hr,
    by rw [I.radius, R.radius]; linarith,
    by simpa only [I.radius, R.radius] using hlo,
    by simpa only [I.radius, R.radius] using hhi, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [I.radius, I.position, I.direction, R.radius, R.position, R.direction, I.upper_map]
    exact (buffered_tube_containment hd hr64 (C.axis_buffer k hk (I.map i))).trans
      (Metric.thickening_mono (by linarith) _)
  · intro i
    simpa only [I.position, I.direction, R.radius, R.position, R.direction, I.upper_map] using
      C.axis_buffer k hk (I.map i)
  · intro t
    have hh := convexCount_reindex (convexCount_mono hK (Q.count (R.map k t))) I.map I.injective
      (Q := fun i => I.upper i = t)
      (fun i hi => ⟨I.selected i, I.fixed i, (I.upper_map i).symm.trans (congrArg (R.map k) hi)⟩)
    simpa only [Function.comp_def, I.radius, I.position, I.direction] using hh
  · intro t
    have hh := slabBound_reindex (Q.slab (R.map k t)) I.map I.injective
      (Q := fun i => I.upper i = t)
      (fun i hi => ⟨I.selected i, I.fixed i, (I.upper_map i).symm.trans (congrArg (R.map k) hi)⟩) (hL t)
    simpa only [Function.comp_def, I.radius, I.position, I.direction,
      R.radius, R.position, R.direction] using hh

theorem RestrictedGrouping.lower_control {J k : ℕ} {T : TubeHierarchy J}
    {H B d θ θ' g g' gap gap' r K L F : ℝ}
    {G : GroupedSelection (T.parent k) H B} {S : Finset (Fin (T.layer J).card)}
    {R : HierarchyRestriction T S} (I : RestrictedGrouping T G R r)
    (C : HierarchyControl d θ g gap T) (Q : GroupedGeometry T G d r K L F) (hk : k < J)
    (hd : 0 < d) (hd1 : d ≤ 1) (hθ : θ ≤ θ') (hr : 0 < r)
    (hsr : (T.layer (k + 1)).radius < r)
    (hlo : d ^ g' * r ≤ (T.layer (k + 1)).radius)
    (hhi : (T.layer (k + 1)).radius ≤ d ^ gap' * r) (hF : F ≤ d ^ (-θ')) :
    EdgeControl d θ' g' gap' I.middle (R.tree.layer (k + 1)) I.lower := by
  have hs := C.positive (k + 1) (by omega)
  have hcoef : d ^ (-θ) ≤ d ^ (-θ') := Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hθ)
  refine ⟨by simpa only [I.radius] using hr, by simpa only [R.radius] using hs,
    by simpa only [I.radius, R.radius] using hsr,
    by simpa only [I.radius, R.radius] using hlo,
    by simpa only [I.radius, R.radius] using hhi, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa only [I.radius, I.position, I.direction, I.lower_map, R.radius, R.position, R.direction] using
      Q.containment (R.map (k + 1) i) (I.child_selected i)
  · intro i
    simpa only [I.radius, I.position, I.direction, I.lower_map, R.position, R.direction] using
      Q.buffer (R.map (k + 1) i) (I.child_selected i)
  · intro t
    have hh := convexCount_reindex (convexCount_mono hcoef (C.count k hk (T.parent k (I.map t))))
      (R.map (k + 1)) (R.injective (k + 1)) (Q := fun i => I.lower i = t) (fun i hi => by
        rw [← G.parent_group, ← I.lower_map, hi])
    simpa only [Function.comp_def, R.radius, R.position, R.direction] using hh
  · intro t
    have hh := slabBound_reindex (slabBound_mono hF (Q.fine_slab (I.map t) (I.selected t) (I.fixed t)))
      (R.map (k + 1)) (R.injective (k + 1)) (Q := fun i => I.lower i = t)
      (fun i hi => ⟨I.child_selected i, (I.lower_map i).symm.trans (congrArg I.map hi)⟩)
      (by rw [I.fine_card])
    simpa only [Function.comp_def, I.radius, I.position, I.direction,
      R.radius, R.position, R.direction] using hh

end WangZahlLot.Obl.wz_multiscale_finite_tower
