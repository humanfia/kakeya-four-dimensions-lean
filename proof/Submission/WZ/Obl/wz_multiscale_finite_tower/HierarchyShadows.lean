-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.HierarchyShadows.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.HierarchyCounts
import Submission.WZ.Obl.wz_multiscale_finite_tower.NestedGrid

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_nonflat_factored_improvement (gridCell gridUnion)
open WangZahlLot.Obl.wz_flat_factored_improvement (gridHull gridHull_measurable)

def descendantUnion {J : ℕ} (T : TubeHierarchy J)
    (Z : Fin (T.layer J).card → Set Space) (j : ℕ) (k : Fin (T.layer j).card) : Set Space :=
  ⋃ i, ⋃ (_ : T.ancestor j i = k), Z i

lemma descendantUnion_measurable {J : ℕ} (T : TubeHierarchy J)
    {Z : Fin (T.layer J).card → Set Space} (hZ : ∀ i, MeasurableSet (Z i))
    (j : ℕ) (k : Fin (T.layer j).card) : MeasurableSet (descendantUnion T Z j k) :=
  MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hZ i

lemma descendantUnion_subset {J : ℕ} (T : TubeHierarchy J)
    {Z : Fin (T.layer J).card → Set Space} {W : Set Space} (hZ : ∀ i, Z i ⊆ W)
    (j : ℕ) (k : Fin (T.layer j).card) : descendantUnion T Z j k ⊆ W :=
  iUnion_subset fun i => iUnion_subset fun _ => hZ i

lemma subset_descendantUnion {J : ℕ} (T : TubeHierarchy J)
    (Z : Fin (T.layer J).card → Set Space) (j : ℕ) (i : Fin (T.layer J).card) :
    Z i ⊆ descendantUnion T Z j (T.ancestor j i) :=
  (subset_iUnion (fun _ : T.ancestor j i = T.ancestor j i => Z i) rfl).trans
    (subset_iUnion (fun b => ⋃ (_ : T.ancestor j b = T.ancestor j i), Z b) i)

lemma descendantUnion_terminal {J : ℕ} (T : TubeHierarchy J)
    (Z : Fin (T.layer J).card → Set Space) (i : Fin (T.layer J).card) :
    descendantUnion T Z J i = Z i := by
  simp [descendantUnion, T.terminal]

lemma descendantUnion_buffer {d θ g gap : ℝ} {J : ℕ} {T : TubeHierarchy J}
    (H : HierarchyControl d θ g gap T) (hd : 0 < d) (hgap : d ^ gap ≤ 1 / 64)
    {Z : Fin (T.layer J).card → Set Space}
    (hZ : ∀ i, Z i ⊆ Tube d ((T.layer J).position i) ((T.layer J).direction i))
    {j : ℕ} (hj : j < J) (k : Fin (T.layer j).card) :
    descendantUnion T Z j k ⊆ Tube ((63 / 64) * (T.layer j).radius)
      ((T.layer j).position k) ((T.layer j).direction k) := by
  apply iUnion_subset
  intro i
  apply iUnion_subset
  intro hi
  simpa only [hi] using (hZ i).trans (H.leaf_buffer hd hgap hj i)

lemma single_gridHull_density {a d lam : ℝ} (ha : 0 < a) (hd : 0 < d)
    {x v : Space} {Z : Set Space} (hv : ‖v‖ = 1) (hZT : Z ⊆ Tube d x v)
    (S : Finset (Fin 3 → ℤ)) (hgrid : Z ⊆ gridUnion a S)
    (hden : ENNReal.ofReal (lam * d ^ 2) ≤ volume Z) :
    ENNReal.ofReal (lam * a ^ 2 / 16) ≤ volume (gridHull a S Z) := by
  have hh := fibre_gridHull_density ha hd (n := 1) (by omega) (fun _ => x) (fun _ => v)
    (fun _ => Z) (fun _ => hv) (fun _ => hZT) S (fun _ => hgrid)
    (by simpa using hden)
  have he : (⋃ _i : Fin 1, Z) = Z := Set.iUnion_const Z
  rw [he] at hh
  exact hh

lemma descendant_shadow_density {d lam density : ℝ} {J : ℕ} {T : TubeHierarchy J}
    (hd : 0 < d) {Z : Fin (T.layer J).card → Set Space}
    (hZT : ∀ i, Z i ⊆ Tube d ((T.layer J).position i) ((T.layer J).direction i))
    (hden : ∀ i, ENNReal.ofReal (lam * d ^ 2) ≤ volume (Z i))
    {j : ℕ} (hj : j ≤ J) {a : ℝ} (ha : 0 < a) (S : Finset (Fin 3 → ℤ))
    (hgrid : ∀ i, Z i ⊆ gridUnion a S)
    (hsize : density * (T.layer j).radius ^ 2 ≤ lam * a ^ 2 / 16)
    (k : Fin (T.layer j).card) :
    ENNReal.ofReal (density * (T.layer j).radius ^ 2) ≤
      volume (gridHull a S (descendantUnion T Z j k)) := by
  obtain ⟨i, rfl⟩ := T.active j hj k
  exact (ENNReal.ofReal_le_ofReal hsize).trans
    ((single_gridHull_density ha hd ((T.layer J).unit i) (hZT i) S (hgrid i) (hden i)).trans
      (measure_mono (gridHull_mono_set S (subset_descendantUnion T Z j i))))

noncomputable def hierarchyShading {J : ℕ} (T : TubeHierarchy J)
    (Z : Fin (T.layer J).card → Set Space) (a : ℕ → ℝ)
    (S : ℕ → Finset (Fin 3 → ℤ)) (j : ℕ) (k : Fin (T.layer j).card) : Set Space :=
  if j < J then gridHull (a j) (S j) (descendantUnion T Z j k) else descendantUnion T Z j k

lemma hierarchyShading_measurable {J : ℕ} (T : TubeHierarchy J)
    {Z : Fin (T.layer J).card → Set Space} (hZ : ∀ i, MeasurableSet (Z i))
    (a : ℕ → ℝ) (S : ℕ → Finset (Fin 3 → ℤ)) (j : ℕ) (k : Fin (T.layer j).card) :
    MeasurableSet (hierarchyShading T Z a S j k) := by
  unfold hierarchyShading
  split_ifs
  · exact gridHull_measurable _ _ _
  · exact descendantUnion_measurable T hZ j k

lemma hierarchyShading_terminal {J : ℕ} (T : TubeHierarchy J)
    (Z : Fin (T.layer J).card → Set Space) (a : ℕ → ℝ)
    (S : ℕ → Finset (Fin 3 → ℤ)) (k : Fin (T.layer J).card) :
    hierarchyShading T Z a S J k = Z k := by
  simp only [hierarchyShading, lt_self_iff_false, ↓reduceIte, descendantUnion_terminal]

lemma hierarchyShading_containment {d θ g gap : ℝ} {J : ℕ} {T : TubeHierarchy J}
    (H : HierarchyControl d θ g gap T) (hd : 0 < d) (hgap : d ^ gap ≤ 1 / 64)
    {Z : Fin (T.layer J).card → Set Space}
    (hZT : ∀ i, Z i ⊆ Tube d ((T.layer J).position i) ((T.layer J).direction i))
    {a : ℕ → ℝ} (ha : ∀ j, j < J → 0 < a j ∧ 2 * a j ≤ (T.layer j).radius / 64)
    (S : ℕ → Finset (Fin 3 → ℤ)) {j : ℕ} (hj : j ≤ J) (k : Fin (T.layer j).card) :
    hierarchyShading T Z a S j k ⊆ Tube (T.layer j).radius
      ((T.layer j).position k) ((T.layer j).direction k) := by
  by_cases hjJ : j < J
  · rw [hierarchyShading, if_pos hjJ]
    exact buffered_gridHull_containment (ha j hjJ).1 (ha j hjJ).2 _
      (descendantUnion_buffer H hd hgap hZT hjJ k)
  · have he : j = J := by omega
    subst j
    simpa only [hierarchyShading_terminal, H.bottom_radius] using hZT k

end WangZahlLot.Obl.wz_multiscale_finite_tower
