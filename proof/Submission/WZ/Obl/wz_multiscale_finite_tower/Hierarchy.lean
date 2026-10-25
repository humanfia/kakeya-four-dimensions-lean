-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.Hierarchy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.AlignedInitialization
import Submission.WZ.Obl.wz_multiscale_finite_tower.Chains
import Submission.WZ.Obl.wz_multiscale_finite_tower.BalancedPruning

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory Set LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_tower_balanced_refinement (Balanced leafFiber)
open WangZahlLot.Obl.wz_nsp_full_counted_hierarchy (branchFiber)
open WangZahlLot.Obl.wz_rescaled_fibre_alternatives (ConvexCount SlabBound doubled)

/-- A finite hierarchy whose every node is occupied by a bottom leaf. -/
structure TubeHierarchy (J : ℕ) where
  layer : ℕ → Layer
  parent : ∀ j, Fin (layer (j + 1)).card → Fin (layer j).card
  ancestor : ∀ j, Fin (layer J).card → Fin (layer j).card
  terminal : ancestor J = id
  coherent : ∀ j, j < J → ∀ i, parent j (ancestor (j + 1) i) = ancestor j i
  active : ∀ j, j ≤ J → Function.Surjective (ancestor j)

lemma TubeHierarchy.nested {J : ℕ} (T : TubeHierarchy J) {j k : ℕ}
    (hjk : j ≤ k) (hk : k ≤ J) {a b : Fin (T.layer J).card}
    (he : T.ancestor k a = T.ancestor k b) : T.ancestor j a = T.ancestor j b := by
  induction k, hjk using Nat.le_induction with
  | base => exact he
  | succ k hjk ih =>
    apply ih (by omega)
    rw [← T.coherent k (by omega) a, ← T.coherent k (by omega) b, he]

lemma TubeHierarchy.parent_surjective {J : ℕ} (T : TubeHierarchy J)
    {j : ℕ} (hj : j < J) : Function.Surjective (T.parent j) := by
  intro k
  obtain ⟨i, hi⟩ := T.active j hj.le k
  exact ⟨T.ancestor (j + 1) i, (T.coherent j hj i).trans hi⟩

lemma TubeHierarchy.branch_eq_fibre {J : ℕ} (T : TubeHierarchy J)
    {j : ℕ} (hj : j < J) (i : Fin (T.layer J).card) :
    (branchFiber Finset.univ (T.ancestor j) (T.ancestor (j + 1)) i : Set (Fin (T.layer (j + 1)).card)) =
      {k | T.parent j k = T.ancestor j i} := by
  classical
  ext k
  constructor
  · intro hk
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
    have hpa : T.ancestor j a = T.ancestor j i := by
      simpa only [leafFiber, Finset.mem_filter, Finset.mem_univ, true_and] using ha
    exact (T.coherent j hj a).trans hpa
  · intro hk
    obtain ⟨a, rfl⟩ := T.active (j + 1) (by omega) k
    refine Finset.mem_image.mpr ⟨a, ?_, rfl⟩
    simpa only [leafFiber, Finset.mem_filter, Finset.mem_univ, true_and] using
      (T.coherent j hj a).symm.trans hk

lemma TubeHierarchy.branch_balance {J : ℕ} (T : TubeHierarchy J) {R : ℝ}
    (hR : 0 ≤ R) (hbal : ∀ j, j ≤ J → Balanced Finset.univ (T.ancestor j) R)
    {j : ℕ} (hj : j < J) (k l : Fin (T.layer j).card) :
    ({i | T.parent j i = k}.ncard : ℝ) ≤ R ^ 2 * {i | T.parent j i = l}.ncard := by
  classical
  obtain ⟨a, rfl⟩ := T.active j hj.le k
  obtain ⟨b, rfl⟩ := T.active j hj.le l
  have hh := WangZahlLot.Obl.wz_nsp_full_counted_hierarchy.branch_balance_of_leaf_balance
    Finset.univ (T.ancestor j) (T.ancestor (j + 1)) hR
    (fun a b he => T.nested (by omega) (by omega) he)
    (hbal j hj.le) (hbal (j + 1) (by omega)) a (Finset.mem_univ _) b (Finset.mem_univ _)
  rw [← T.branch_eq_fibre hj a, ← T.branch_eq_fibre hj b, Set.ncard_coe_finset, Set.ncard_coe_finset]
  exact hh

/-- The numerical and analytic invariant on consecutive levels. -/
structure HierarchyControl (d θ g gap : ℝ) {J : ℕ} (T : TubeHierarchy J) : Prop where
  length_pos : 0 < J
  root_radius : (T.layer 0).radius = 1
  root_card : (T.layer 0).card = 1
  bottom_radius : (T.layer J).radius = d
  positive : ∀ j, j ≤ J → 0 < (T.layer j).radius
  decreasing : ∀ j, j < J → (T.layer (j + 1)).radius < (T.layer j).radius
  lower_gap : ∀ j, j < J → d ^ g * (T.layer j).radius ≤ (T.layer (j + 1)).radius
  upper_gap : ∀ j, j < J → (T.layer (j + 1)).radius ≤ d ^ gap * (T.layer j).radius
  containment : ∀ j, j < J → ∀ i,
    Tube (T.layer (j + 1)).radius ((T.layer (j + 1)).position i) ((T.layer (j + 1)).direction i) ⊆
      Tube (T.layer j).radius ((T.layer j).position (T.parent j i)) ((T.layer j).direction (T.parent j i))
  axis_buffer : ∀ j, j < J → ∀ i,
    Tube d ((T.layer (j + 1)).position i) ((T.layer (j + 1)).direction i) ⊆
      Tube ((31 / 32) * (T.layer j).radius)
        ((T.layer j).position (T.parent j i)) ((T.layer j).direction (T.parent j i))
  count : ∀ j, j < J → ∀ k, ConvexCount (T.layer (j + 1)).radius (d ^ (-θ))
    (fun i => T.parent j i = k)
    (fun i => Tube (T.layer (j + 1)).radius ((T.layer (j + 1)).position i) ((T.layer (j + 1)).direction i))
  slab : ∀ j, j < J → ∀ k,
    SlabBound (doubled (T.layer j).radius ((T.layer j).position k) ((T.layer j).direction k))
      (d ^ (-θ)) (fun i => T.parent j i = k)
      (fun i => Tube (T.layer (j + 1)).radius ((T.layer (j + 1)).position i) ((T.layer (j + 1)).direction i))
  balanced : ∀ j, j ≤ J → Balanced Finset.univ (T.ancestor j) (d ^ (-θ))

structure HierarchyAlignment (u : Space) (h : ℝ) {J : ℕ} (T : TubeHierarchy J) : Prop where
  root : ∀ k, (T.layer 0).position k = - (1 / 2 : ℝ) • u ∧ (T.layer 0).direction k = u
  direction_cap : ∀ j, 0 < j → j ≤ J → ∀ i, ‖(T.layer j).direction i - u‖ ≤ 1 / 10
  aligned : ∀ j, 0 < j → j ≤ J → ∀ i,
    inner ℝ ((T.layer j).direction i) (axisMidpoint ((T.layer j).position i) ((T.layer j).direction i)) = h
  midpoint : ∀ j, 0 < j → j ≤ J → ∀ i,
    ‖axisMidpoint ((T.layer j).position i) ((T.layer j).direction i)‖ ≤ 7 / 8

structure HierarchyCertificate (d θ g gap : ℝ) (J : ℕ) where
  tree : TubeHierarchy J
  shading : Fin (tree.layer J).card → Set Space
  root_axis : Space
  scalar : ℝ
  control : HierarchyControl d θ g gap tree
  alignment : HierarchyAlignment root_axis scalar tree
  family : AlignedFamily d (d ^ θ) (d ^ (-θ)) (d ^ (-θ)) root_axis scalar
    (tree.layer J).card (tree.layer J).position (tree.layer J).direction shading

theorem HierarchyControl.tower {d θ g gap : ℝ} {J : ℕ} {T : TubeHierarchy J}
    (H : HierarchyControl d θ g gap T) :
    Tower false d (d ^ (-θ)) g J (T.layer J).card (T.layer J).position (T.layer J).direction := by
  refine ⟨J, H.length_pos, le_rfl, (fun j => (T.layer j).radius), (fun j => (T.layer j).card),
    (fun j => (T.layer j).position), (fun j => (T.layer j).direction), T.parent,
    H.root_radius, H.bottom_radius, H.root_card, ⟨Equiv.refl _, fun _ => ⟨rfl, rfl⟩⟩,
    (fun j _ => (T.layer j).unit), ?_, ?_⟩
  · intro j hj
    exact ⟨H.positive (j + 1) (by omega), H.decreasing j hj, H.lower_gap j hj, H.containment j hj⟩
  · exact H.count

end WangZahlLot.Obl.wz_multiscale_finite_tower
