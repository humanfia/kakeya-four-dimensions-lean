-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.HierarchyCounts.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.BufferedGeometry

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya

lemma sum_fibre_ncard {n m : ℕ} (f : Fin n → Fin m) :
    (∑ k : Fin m, {i | f i = k}.ncard) = n := by
  classical
  have he (k : Fin m) : {i | f i = k} =
      (Finset.univ.filter (fun i => f i = k) : Set (Fin n)) := by ext i; simp
  simp_rw [he, Set.ncard_coe_finset]
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_id, Finset.card_univ, Fintype.card_fin] using
    Finset.sum_fiberwise (M := ℕ) Finset.univ f (fun _ => 1)

lemma fibre_average_lower {n m : ℕ} (hm : 0 < m) (f : Fin n → Fin m) {R : ℝ}
    (hbal : ∀ k l, ({i | f i = k}.ncard : ℝ) ≤ R * {i | f i = l}.ncard)
    (k : Fin m) : (n : ℝ) / m ≤ R * {i | f i = k}.ncard := by
  have hsum := Finset.sum_le_sum (fun l (_ : l ∈ Finset.univ) => hbal l k)
  have hreal : (∑ l : Fin m, ({i | f i = l}.ncard : ℝ)) = n := by
    exact_mod_cast sum_fibre_ncard f
  rw [hreal] at hsum
  apply (div_le_iff₀ (Nat.cast_pos.mpr hm)).mpr
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm] using hsum

lemma TubeHierarchy.branch_average_lower {d θ g gap : ℝ} {J : ℕ} {T : TubeHierarchy J}
    (H : HierarchyControl d θ g gap T) (hd : 0 ≤ d) {j : ℕ} (hj : j < J)
    (k : Fin (T.layer j).card) :
    ((T.layer (j + 1)).card : ℝ) / (T.layer j).card ≤
      (d ^ (-θ)) ^ 2 * {i | T.parent j i = k}.ncard :=
  fibre_average_lower (T.layer j).card_pos (T.parent j)
    (T.branch_balance (Real.rpow_nonneg hd _) H.balanced hj) k

lemma TubeHierarchy.card_le_bottom {J : ℕ} (T : TubeHierarchy J) {j : ℕ} (hj : j ≤ J) :
    (T.layer j).card ≤ (T.layer J).card := by
  simpa using Fintype.card_le_of_surjective (T.ancestor j) (T.active j hj)

lemma HierarchyControl.radius_antitone {d θ g gap : ℝ} {J : ℕ} {T : TubeHierarchy J}
    (H : HierarchyControl d θ g gap T) {j k : ℕ} (hjk : j ≤ k) (hk : k ≤ J) :
    (T.layer k).radius ≤ (T.layer j).radius := by
  induction k, hjk using Nat.le_induction with
  | base => exact le_rfl
  | succ k hjk ih => exact (H.decreasing k (by omega)).le.trans (ih (by omega))

lemma HierarchyControl.radius_bounds {d θ g gap : ℝ} {J : ℕ} {T : TubeHierarchy J}
    (H : HierarchyControl d θ g gap T) {j : ℕ} (hj : j ≤ J) :
    d ≤ (T.layer j).radius ∧ (T.layer j).radius ≤ 1 := by
  constructor
  · simpa only [H.bottom_radius] using H.radius_antitone hj le_rfl
  · simpa only [H.root_radius] using H.radius_antitone (Nat.zero_le j) hj

lemma HierarchyControl.ancestor_containment {d θ g gap : ℝ} {J : ℕ} {T : TubeHierarchy J}
    (H : HierarchyControl d θ g gap T) {j k : ℕ} (hjk : j ≤ k) (hk : k ≤ J)
    (i : Fin (T.layer J).card) :
    Tube (T.layer k).radius ((T.layer k).position (T.ancestor k i))
        ((T.layer k).direction (T.ancestor k i)) ⊆
      Tube (T.layer j).radius ((T.layer j).position (T.ancestor j i))
        ((T.layer j).direction (T.ancestor j i)) := by
  induction k, hjk using Nat.le_induction with
  | base => exact Subset.rfl
  | succ k hjk ih =>
    have hh := H.containment k (by omega) (T.ancestor (k + 1) i)
    rw [T.coherent k (by omega) i] at hh
    exact hh.trans (ih (by omega))

lemma HierarchyControl.leaf_containment {d θ g gap : ℝ} {J : ℕ} {T : TubeHierarchy J}
    (H : HierarchyControl d θ g gap T) {j : ℕ} (hj : j ≤ J)
    (i : Fin (T.layer J).card) :
    Tube d ((T.layer J).position i) ((T.layer J).direction i) ⊆
      Tube (T.layer j).radius ((T.layer j).position (T.ancestor j i))
        ((T.layer j).direction (T.ancestor j i)) := by
  simpa only [H.bottom_radius, T.terminal, id_eq] using H.ancestor_containment hj le_rfl i

lemma HierarchyControl.leaf_buffer {d θ g gap : ℝ} {J : ℕ} {T : TubeHierarchy J}
    (H : HierarchyControl d θ g gap T) (hd : 0 < d) (hgap : d ^ gap ≤ 1 / 64)
    {j : ℕ} (hj : j < J) (i : Fin (T.layer J).card) :
    Tube d ((T.layer J).position i) ((T.layer J).direction i) ⊆
      Tube ((63 / 64) * (T.layer j).radius) ((T.layer j).position (T.ancestor j i))
        ((T.layer j).direction (T.ancestor j i)) := by
  have hr : (T.layer (j + 1)).radius ≤ (T.layer j).radius / 64 := by
    calc
      _ ≤ d ^ gap * (T.layer j).radius := H.upper_gap j hj
      _ ≤ (1 / 64) * (T.layer j).radius :=
        mul_le_mul_of_nonneg_right hgap (H.positive j hj.le).le
      _ = _ := by ring
  have hbuf := buffered_tube_containment hd hr (H.axis_buffer j hj (T.ancestor (j + 1) i))
  rw [T.coherent j hj i] at hbuf
  exact (H.leaf_containment (by omega) i).trans hbuf

lemma HierarchyControl.ratio_bounds {d θ g gap : ℝ} {J : ℕ} {T : TubeHierarchy J}
    (H : HierarchyControl d θ g gap T) (hd : 0 ≤ d) {j : ℕ} (hj : j < J) :
    d ≤ (T.layer (j + 1)).radius / (T.layer j).radius ∧
      (T.layer (j + 1)).radius / (T.layer j).radius < 1 := by
  have hr := H.positive j hj.le
  constructor
  · apply (le_div_iff₀ hr).mpr
    calc
      _ ≤ d * 1 := mul_le_mul_of_nonneg_left (H.radius_bounds hj.le).2 hd
      _ ≤ (T.layer (j + 1)).radius := by simpa using (H.radius_bounds (by omega : j + 1 ≤ J)).1
  · exact (div_lt_one hr).mpr (H.decreasing j hj)

end WangZahlLot.Obl.wz_multiscale_finite_tower
