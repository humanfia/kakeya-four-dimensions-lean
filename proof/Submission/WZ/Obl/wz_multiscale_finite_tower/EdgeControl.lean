-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.EdgeControl.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.IndexTransport

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory Set LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_rescaled_fibre_alternatives (ConvexCount SlabBound doubled)

structure LayerEquiv (p q : Layer) where
  index : Fin p.card ≃ Fin q.card
  radius : p.radius = q.radius
  position : ∀ i, p.position i = q.position (index i)
  direction : ∀ i, p.direction i = q.direction (index i)

def LayerEquiv.of_eq {p q : Layer} (h : p = q) : LayerEquiv p q := by
  subst q
  exact ⟨Equiv.refl _, rfl, fun _ => rfl, fun _ => rfl⟩

lemma LayerEquiv.of_eq_val {p q : Layer} (h : p = q) (i : Fin p.card) :
    ((LayerEquiv.of_eq h).index i).val = i.val := by
  subst q
  rfl

structure EdgeControl (d θ g gap : ℝ) (p c : Layer) (f : Fin c.card → Fin p.card) : Prop where
  parent_pos : 0 < p.radius
  child_pos : 0 < c.radius
  decreasing : c.radius < p.radius
  lower_gap : d ^ g * p.radius ≤ c.radius
  upper_gap : c.radius ≤ d ^ gap * p.radius
  containment : ∀ i, Tube c.radius (c.position i) (c.direction i) ⊆
    Tube p.radius (p.position (f i)) (p.direction (f i))
  buffer : ∀ i, Tube d (c.position i) (c.direction i) ⊆
    Tube ((31 / 32) * p.radius) (p.position (f i)) (p.direction (f i))
  count : ∀ k, ConvexCount c.radius (d ^ (-θ)) (fun i => f i = k)
    (fun i => Tube c.radius (c.position i) (c.direction i))
  slab : ∀ k, SlabBound (doubled p.radius (p.position k) (p.direction k)) (d ^ (-θ))
    (fun i => f i = k) (fun i => Tube c.radius (c.position i) (c.direction i))

lemma HierarchyControl.edge {d θ g gap : ℝ} {J : ℕ} {T : TubeHierarchy J}
    (H : HierarchyControl d θ g gap T) {j : ℕ} (hj : j < J) :
    EdgeControl d θ g gap (T.layer j) (T.layer (j + 1)) (T.parent j) :=
  ⟨H.positive j hj.le, H.positive (j + 1) (by omega), H.decreasing j hj,
    H.lower_gap j hj, H.upper_gap j hj, H.containment j hj, H.axis_buffer j hj,
    H.count j hj, H.slab j hj⟩

lemma EdgeControl.transport {d θ g gap : ℝ} {p c p' c' : Layer}
    {f : Fin c.card → Fin p.card} {f' : Fin c'.card → Fin p'.card}
    (P : LayerEquiv p' p) (C : LayerEquiv c' c)
    (H : EdgeControl d θ g gap p c f)
    (hcomm : ∀ i, P.index (f' i) = f (C.index i)) : EdgeControl d θ g gap p' c' f' := by
  refine ⟨by simpa only [P.radius] using H.parent_pos,
    by simpa only [C.radius] using H.child_pos,
    by simpa only [P.radius, C.radius] using H.decreasing,
    by simpa only [P.radius, C.radius] using H.lower_gap,
    by simpa only [P.radius, C.radius] using H.upper_gap, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa only [P.radius, C.radius, P.position, C.position, P.direction, C.direction, hcomm] using
      H.containment (C.index i)
  · intro i
    simpa only [P.radius, P.position, C.position, P.direction, C.direction, hcomm] using H.buffer (C.index i)
  · intro k
    have hh := convexCount_reindex (H.count (P.index k)) C.index C.index.injective
      (Q := fun i => f' i = k) (fun i hi => (hcomm i).symm.trans (congrArg P.index hi))
    simpa only [Function.comp_def, C.radius, C.position, C.direction] using hh
  · intro k
    have hc : {i | f (C.index i) = P.index k}.ncard = {i | f i = P.index k}.ncard :=
      Set.ncard_preimage_of_injective_subset_range (s := {i | f i = P.index k}) C.index.injective (by
        intro i hi
        exact C.index.surjective i)
    have he : {i | f (C.index i) = P.index k} = {i | f' i = k} := by
      ext i
      change (f (C.index i) = P.index k) ↔ f' i = k
      rw [← hcomm i]
      exact P.index.injective.eq_iff
    rw [he] at hc
    have hh := slabBound_reindex (H.slab (P.index k)) C.index C.index.injective
      (Q := fun i => f' i = k) (fun i hi => (hcomm i).symm.trans (congrArg P.index hi))
      (by rw [hc])
    simpa only [Function.comp_def, P.radius, C.radius, P.position, C.position, P.direction, C.direction] using hh

end WangZahlLot.Obl.wz_multiscale_finite_tower
