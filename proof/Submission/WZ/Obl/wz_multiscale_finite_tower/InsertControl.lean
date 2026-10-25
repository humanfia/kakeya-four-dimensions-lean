-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.InsertControl.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.InsertEdges
import Submission.WZ.Obl.wz_multiscale_finite_tower.DenseRestriction

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory Set LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_tower_balanced_refinement (Balanced leafFiber)

lemma balanced_postcomp_iff {α β γ : Type*} [DecidableEq α] (S : Finset α)
    (p : α → β) (q : β → γ) (hq : Function.Injective q) (R : ℝ) :
    Balanced S (q ∘ p) R ↔ Balanced S p R := by
  classical
  have he (i) : leafFiber S (q ∘ p) i = leafFiber S p i := by
    ext a
    simp only [leafFiber, Finset.mem_filter, Function.comp_apply, hq.eq_iff]
  unfold WangZahlLot.Obl.wz_tower_balanced_refinement.Balanced
  simp only [he]

lemma insertedLabels_balanced {d θ g gap : ℝ} {J : ℕ} {T : TubeHierarchy J}
    (H : HierarchyControl d θ g gap T) {k : ℕ} (hk : k < J) (M : Layer)
    (a : Fin (T.layer (k + 1)).card → Fin M.card)
    (hmid : Balanced Finset.univ (a ∘ T.ancestor (k + 1)) (d ^ (-θ)))
    (j : ℕ) (hj : j ≤ J + 1) : Balanced Finset.univ (insertedLabels T k M a j) (d ^ (-θ)) := by
  by_cases hjk : j ≤ k
  · let E := beforeLayerEquiv k M T.layer j hjk
    apply (balanced_postcomp_iff Finset.univ _ E.index E.index.injective _).mp
    have he : E.index ∘ insertedLabels T k M a j = T.ancestor j :=
      funext fun i => beforeLayerEquiv_label T k M a j hjk i
    rw [he]
    exact H.balanced j (by omega)
  · by_cases he : j = k + 1
    · subst j
      let E := middleLayerEquiv k M T.layer
      apply (balanced_postcomp_iff Finset.univ _ E.index E.index.injective _).mp
      have he : E.index ∘ insertedLabels T k M a (k + 1) = a ∘ T.ancestor (k + 1) :=
        funext fun i => middleLayerEquiv_label T k M a i
      rw [he]
      exact hmid
    · let E := afterLayerEquiv k M T.layer j (j - 1) (by omega) rfl
      apply (balanced_postcomp_iff Finset.univ _ E.index E.index.injective _).mp
      have he : E.index ∘ insertedLabels T k M a j = T.ancestor (j - 1) :=
        funext fun i => afterLayerEquiv_label T k M a j (j - 1) (by omega) rfl i
      rw [he]
      exact H.balanced (j - 1) (by omega)

theorem insertHierarchy_control {d θ g gap : ℝ} {J : ℕ} {T : TubeHierarchy J}
    (H : HierarchyControl d θ g gap T) {k : ℕ} (hk : k < J) (M : Layer)
    (a : Fin (T.layer (k + 1)).card → Fin M.card) (ha : Function.Surjective a)
    (b : Fin M.card → Fin (T.layer k).card) (hab : ∀ i, b (a i) = T.parent k i)
    (Hupper : EdgeControl d θ g gap (T.layer k) M b)
    (Hlower : EdgeControl d θ g gap M (T.layer (k + 1)) a)
    (hmid : Balanced Finset.univ (a ∘ T.ancestor (k + 1)) (d ^ (-θ))) :
    HierarchyControl d θ g gap (insertHierarchy T hk M a ha b hab) := by
  have he := insertHierarchy_edges H hk M a ha b hab Hupper Hlower
  refine ⟨by omega, ?_, ?_, ?_, ?_,
    (fun j hj => (he j hj).decreasing), (fun j hj => (he j hj).lower_gap),
    (fun j hj => (he j hj).upper_gap), (fun j hj => (he j hj).containment),
    (fun j hj => (he j hj).buffer), (fun j hj => (he j hj).count),
    (fun j hj => (he j hj).slab), ?_⟩
  · change (insertedLayer k M T.layer 0).radius = 1
    simpa only [insertedLayer, ite_eq_left (Nat.zero_le k)] using H.root_radius
  · change (insertedLayer k M T.layer 0).card = 1
    simpa only [insertedLayer, ite_eq_left (Nat.zero_le k)] using H.root_card
  · change (insertedLayer k M T.layer (J + 1)).radius = d
    have E := afterLayerEquiv k M T.layer (J + 1) J (by omega) (by omega)
    exact E.radius.trans H.bottom_radius
  · intro j hj
    by_cases hj' : j < J + 1
    · exact (he j hj').parent_pos
    · have hj' : j = J + 1 := by omega
      subst j
      exact (he J (by omega)).child_pos
  · intro j hj
    exact hierarchyOfPartitions_balanced _ _ _ _ _ (insertedLabels_balanced H hk M a hmid j hj)

lemma insertedLayer_forall {J : ℕ} {T : TubeHierarchy J} {k : ℕ} (hk : k < J) (M : Layer)
    (P : Space → Space → Prop)
    (hT : ∀ j, 0 < j → j ≤ J → ∀ i, P ((T.layer j).position i) ((T.layer j).direction i))
    (hM : ∀ i, P (M.position i) (M.direction i))
    {j : ℕ} (hj : 0 < j) (hjJ : j ≤ J + 1) (i : Fin (insertedLayer k M T.layer j).card) :
    P ((insertedLayer k M T.layer j).position i) ((insertedLayer k M T.layer j).direction i) := by
  by_cases hjk : j ≤ k
  · have E := beforeLayerEquiv k M T.layer j hjk
    rw [E.position, E.direction]
    exact hT j hj (by omega) (E.index i)
  · by_cases he : j = k + 1
    · subst j
      have E := middleLayerEquiv k M T.layer
      rw [E.position, E.direction]
      exact hM (E.index i)
    · have E := afterLayerEquiv k M T.layer j (j - 1) (by omega) rfl
      rw [E.position, E.direction]
      exact hT (j - 1) (by omega) (by omega) (E.index i)

theorem insertHierarchy_alignment {J : ℕ} {T : TubeHierarchy J} {u : Space} {h : ℝ}
    (H : HierarchyAlignment u h T) {k : ℕ} (hk : k < J) (M : Layer)
    (a : Fin (T.layer (k + 1)).card → Fin M.card) (ha : Function.Surjective a)
    (b : Fin M.card → Fin (T.layer k).card) (hab : ∀ i, b (a i) = T.parent k i)
    (hM : ∀ i, ‖M.direction i - u‖ ≤ 1 / 10 ∧
      inner ℝ (M.direction i) (axisMidpoint (M.position i) (M.direction i)) = h ∧
      ‖axisMidpoint (M.position i) (M.direction i)‖ ≤ 7 / 8) :
    HierarchyAlignment u h (insertHierarchy T hk M a ha b hab) := by
  have hall (j : ℕ) (hj : 0 < j) (hjJ : j ≤ J + 1)
      (i : Fin (insertedLayer k M T.layer j).card) := insertedLayer_forall hk M
    (fun x v => ‖v - u‖ ≤ 1 / 10 ∧ inner ℝ v (axisMidpoint x v) = h ∧ ‖axisMidpoint x v‖ ≤ 7 / 8)
    (fun j hj hjJ i => ⟨H.direction_cap j hj hjJ i, H.aligned j hj hjJ i, H.midpoint j hj hjJ i⟩) hM hj hjJ i
  refine ⟨?_, (fun j hj hjJ i => (hall j hj hjJ i).1),
    (fun j hj hjJ i => (hall j hj hjJ i).2.1), (fun j hj hjJ i => (hall j hj hjJ i).2.2)⟩
  intro i
  change Fin (insertedLayer k M T.layer 0).card at i
  have E := beforeLayerEquiv k M T.layer 0 (Nat.zero_le k)
  change (insertedLayer k M T.layer 0).position i = _ ∧
    (insertedLayer k M T.layer 0).direction i = _
  rw [E.position, E.direction]
  exact H.root (E.index i)

lemma AlignedFamily.layer_equiv {d lam K L h : ℝ} {u : Space} {p q : Layer}
    {Y : Fin p.card → Set Space} (E : LayerEquiv q p)
    (F : AlignedFamily d lam K L u h p.card p.position p.direction Y) :
    AlignedFamily d lam K L u h q.card q.position q.direction (Y ∘ E.index) := by
  have hc : q.card = p.card := by simpa only [Fintype.card_fin] using Fintype.card_congr E.index
  have hh := F.reindex E.index E.index.injective q.card_pos (Y ∘ E.index)
    (fun i => F.measurable _) (fun _ => Subset.rfl) (fun i => F.density _) (by rw [hc])
  have hx : q.position = p.position ∘ E.index := funext E.position
  have hv : q.direction = p.direction ∘ E.index := funext E.direction
  rw [hx, hv]
  exact hh

end WangZahlLot.Obl.wz_multiscale_finite_tower
