-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.InsertEdges.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.InsertPartitions
import Submission.WZ.Obl.wz_multiscale_finite_tower.EdgeControl

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

def beforeLayerEquiv (k : ℕ) (M : Layer) (L : ℕ → Layer) (j : ℕ) (hj : j ≤ k) :
    LayerEquiv (insertedLayer k M L j) (L j) :=
  LayerEquiv.of_eq (by simp only [insertedLayer, ite_eq_left hj])

def middleLayerEquiv (k : ℕ) (M : Layer) (L : ℕ → Layer) :
    LayerEquiv (insertedLayer k M L (k + 1)) M :=
  LayerEquiv.of_eq (by simp [insertedLayer])

def afterLayerEquiv (k : ℕ) (M : Layer) (L : ℕ → Layer) (j l : ℕ)
    (hj : k + 1 < j) (hl : j - 1 = l) : LayerEquiv (insertedLayer k M L j) (L l) :=
  LayerEquiv.of_eq (by
    have hjk : ¬j ≤ k := by omega
    have hjk' : j ≠ k + 1 := by omega
    simp only [insertedLayer, ite_eq_right hjk, ite_eq_right hjk', hl])

lemma beforeLayerEquiv_label {J : ℕ} (T : TubeHierarchy J) (k : ℕ) (M : Layer)
    (a : Fin (T.layer (k + 1)).card → Fin M.card) (j : ℕ) (hj : j ≤ k)
    (i : Fin (T.layer J).card) :
    (beforeLayerEquiv k M T.layer j hj).index (insertedLabels T k M a j i) = T.ancestor j i := by
  apply Fin.ext
  simp only [beforeLayerEquiv, LayerEquiv.of_eq_val, insertedLabels, ite_eq_left hj]

lemma middleLayerEquiv_label {J : ℕ} (T : TubeHierarchy J) (k : ℕ) (M : Layer)
    (a : Fin (T.layer (k + 1)).card → Fin M.card) (i : Fin (T.layer J).card) :
    (middleLayerEquiv k M T.layer).index (insertedLabels T k M a (k + 1) i) = a (T.ancestor (k + 1) i) := by
  apply Fin.ext
  have hk : ¬k + 1 ≤ k := by omega
  simp only [middleLayerEquiv, LayerEquiv.of_eq_val, insertedLabels, ite_eq_right hk, ↓reduceIte]

lemma afterLayerEquiv_label {J : ℕ} (T : TubeHierarchy J) (k : ℕ) (M : Layer)
    (a : Fin (T.layer (k + 1)).card → Fin M.card) (j l : ℕ)
    (hj : k + 1 < j) (hl : j - 1 = l) (i : Fin (T.layer J).card) :
    (afterLayerEquiv k M T.layer j l hj hl).index (insertedLabels T k M a j i) = T.ancestor l i := by
  apply Fin.ext
  have hjk : ¬j ≤ k := by omega
  have hjk' : j ≠ k + 1 := by omega
  simp only [afterLayerEquiv, LayerEquiv.of_eq_val, insertedLabels, ite_eq_right hjk, ite_eq_right hjk']
  rw [hl]

lemma insertHierarchy_parent_label {J : ℕ} (T : TubeHierarchy J) {k : ℕ} (hk : k < J) (M : Layer)
    (a : Fin (T.layer (k + 1)).card → Fin M.card) (ha : Function.Surjective a)
    (b : Fin M.card → Fin (T.layer k).card) (hab : ∀ i, b (a i) = T.parent k i)
    {j : ℕ} (hj : j < J + 1) (i : Fin (T.layer J).card) :
    (insertHierarchy T hk M a ha b hab).parent j (insertedLabels T k M a (j + 1) i) =
      insertedLabels T k M a j i :=
  hierarchyOfPartitions_parent _ _ _ _ _ hj i

lemma insertHierarchy_parent_transport {J : ℕ} (T : TubeHierarchy J) {k : ℕ} (hk : k < J) (M : Layer)
    (a : Fin (T.layer (k + 1)).card → Fin M.card) (ha : Function.Surjective a)
    (b : Fin M.card → Fin (T.layer k).card) (hab : ∀ i, b (a i) = T.parent k i)
    {j : ℕ} (hj : j < J + 1) {p c : Layer}
    (P : LayerEquiv (insertedLayer k M T.layer j) p)
    (C : LayerEquiv (insertedLayer k M T.layer (j + 1)) c) (f : Fin c.card → Fin p.card)
    (hcompat : ∀ i, f (C.index (insertedLabels T k M a (j + 1) i)) =
      P.index (insertedLabels T k M a j i))
    (i : Fin (insertedLayer k M T.layer (j + 1)).card) :
    P.index ((insertHierarchy T hk M a ha b hab).parent j i) = f (C.index i) := by
  obtain ⟨v, rfl⟩ := insertedLabels_full T hk M a ha (j + 1) (by omega) i
  rw [insertHierarchy_parent_label T hk M a ha b hab hj]
  exact (hcompat v).symm

/-- Existing edges are merely reindexed; the two supplied edges replace the
chosen edge with no other analytic changes. -/
theorem insertHierarchy_edges {d θ g gap : ℝ} {J : ℕ} {T : TubeHierarchy J}
    (H : HierarchyControl d θ g gap T) {k : ℕ} (hk : k < J) (M : Layer)
    (a : Fin (T.layer (k + 1)).card → Fin M.card) (ha : Function.Surjective a)
    (b : Fin M.card → Fin (T.layer k).card) (hab : ∀ i, b (a i) = T.parent k i)
    (Hupper : EdgeControl d θ g gap (T.layer k) M b)
    (Hlower : EdgeControl d θ g gap M (T.layer (k + 1)) a)
    (j : ℕ) (hj : j < J + 1) :
    EdgeControl d θ g gap ((insertHierarchy T hk M a ha b hab).layer j)
      ((insertHierarchy T hk M a ha b hab).layer (j + 1))
      ((insertHierarchy T hk M a ha b hab).parent j) := by
  by_cases hjk : j < k
  · let P := beforeLayerEquiv k M T.layer j (by omega)
    let C := beforeLayerEquiv k M T.layer (j + 1) (by omega)
    apply EdgeControl.transport P C (H.edge (by omega))
    apply insertHierarchy_parent_transport T hk M a ha b hab hj P C (T.parent j)
    intro i
    rw [beforeLayerEquiv_label, beforeLayerEquiv_label, T.coherent j (by omega)]
  · by_cases he : j = k
    · subst j
      let P := beforeLayerEquiv k M T.layer k le_rfl
      let C := middleLayerEquiv k M T.layer
      apply EdgeControl.transport P C Hupper
      apply insertHierarchy_parent_transport T hk M a ha b hab hj P C b
      intro i
      rw [middleLayerEquiv_label, beforeLayerEquiv_label, hab, T.coherent k hk]
    · by_cases he' : j = k + 1
      · subst j
        let P := middleLayerEquiv k M T.layer
        let C := afterLayerEquiv k M T.layer (k + 1 + 1) (k + 1) (by omega) (by omega)
        apply EdgeControl.transport P C Hlower
        apply insertHierarchy_parent_transport T hk M a ha b hab hj P C a
        intro i
        rw [afterLayerEquiv_label, middleLayerEquiv_label]
      · let P := afterLayerEquiv k M T.layer j (j - 1) (by omega) rfl
        let C := afterLayerEquiv k M T.layer (j + 1) (j - 1 + 1) (by omega) (by omega)
        apply EdgeControl.transport P C (H.edge (by omega : j - 1 < J))
        apply insertHierarchy_parent_transport T hk M a ha b hab hj P C (T.parent (j - 1))
        intro i
        rw [afterLayerEquiv_label, afterLayerEquiv_label, T.coherent (j - 1) (by omega)]

end WangZahlLot.Obl.wz_multiscale_finite_tower
