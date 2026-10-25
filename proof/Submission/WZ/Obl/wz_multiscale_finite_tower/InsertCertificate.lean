-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.InsertCertificate.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.InsertControl

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory Set LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_tower_balanced_refinement (Balanced)

noncomputable def insertCertificate {d θ g gap : ℝ} {J : ℕ}
    (C : HierarchyCertificate d θ g gap J) {k : ℕ} (hk : k < J) (M : Layer)
    (a : Fin (C.tree.layer (k + 1)).card → Fin M.card) (ha : Function.Surjective a)
    (b : Fin M.card → Fin (C.tree.layer k).card) (hab : ∀ i, b (a i) = C.tree.parent k i)
    (Hupper : EdgeControl d θ g gap (C.tree.layer k) M b)
    (Hlower : EdgeControl d θ g gap M (C.tree.layer (k + 1)) a)
    (hmid : Balanced Finset.univ (a ∘ C.tree.ancestor (k + 1)) (d ^ (-θ)))
    (hM : ∀ i, ‖M.direction i - C.root_axis‖ ≤ 1 / 10 ∧
      inner ℝ (M.direction i) (axisMidpoint (M.position i) (M.direction i)) = C.scalar ∧
      ‖axisMidpoint (M.position i) (M.direction i)‖ ≤ 7 / 8) :
    HierarchyCertificate d θ g gap (J + 1) where
  tree := insertHierarchy C.tree hk M a ha b hab
  shading := C.shading ∘ (afterLayerEquiv k M C.tree.layer (J + 1) J (by omega) (by omega)).index
  root_axis := C.root_axis
  scalar := C.scalar
  control := insertHierarchy_control C.control hk M a ha b hab Hupper Hlower hmid
  alignment := insertHierarchy_alignment C.alignment hk M a ha b hab hM
  family := C.family.layer_equiv (afterLayerEquiv k M C.tree.layer (J + 1) J (by omega) (by omega))

lemma equiv_iUnion {α β : Type*} (e : α ≃ β) (Y : β → Set Space) :
    (⋃ i, Y (e i)) = ⋃ i, Y i := by
  ext p
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨e i, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨e.symm i, by simpa using hi⟩

end WangZahlLot.Obl.wz_multiscale_finite_tower
