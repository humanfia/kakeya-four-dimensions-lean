-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_cover_refinement.Geometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_convex_container_tube_packing
import Submission.WZ.Obl.wz_balanced_cluster_cover
import Submission.WZ.Obl.wz_affine_robust_cluster_estimate

namespace WangZahlLot.Obl.wz_separated_cover_refinement

open Set Metric MeasureTheory LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal Classical

abbrev Tube (r : ℝ) (x v : Space) : Set Space :=
  thickening r (segment ℝ x (x + v))

abbrev Dilate (r : ℝ) (z w : Space) : Set Space :=
  thickening (10 * r) (segment ℝ (z - (9 / 2 : ℝ) • w) (z + (11 / 2 : ℝ) • w))

/-- Coordinates of a point in the tenfold concentric dilation. -/
theorem dilate_param {r : ℝ} {z w p : Space} (hp : p ∈ Dilate r z w) :
    ∃ t : ℝ, |t| ≤ 6 ∧ ‖p - (z + t • w)‖ < 10 * r := by
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  rw [segment_eq_image'] at hq
  obtain ⟨s, hs, rfl⟩ := hq
  refine ⟨10 * s - 9 / 2, ?_, ?_⟩
  · rw [abs_le]
    constructor <;> linarith [hs.1, hs.2]
  · have he : z - (9 / 2 : ℝ) • w + s •
        (z + (11 / 2 : ℝ) • w - (z - (9 / 2 : ℝ) • w)) =
        z + (10 * s - 9 / 2) • w := by module
    simpa only [he, dist_eq_norm] using hpq

/-- Containment of a unit fine tube controls its unoriented direction. -/
theorem direction_close {δ r : ℝ} (hδ : 0 < δ) {x v z w : Space}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hT : Tube δ x v ⊆ Dilate r z w) :
    min ‖v - w‖ ‖v + w‖ ≤ 40 * r := by
  have hx := hT (self_subset_thickening hδ _ (left_mem_segment ℝ x (x + v)))
  have hxv := hT (self_subset_thickening hδ _ (right_mem_segment ℝ x (x + v)))
  obtain ⟨a, ha, hxa⟩ := dilate_param hx
  obtain ⟨b, hb, hxb⟩ := dilate_param hxv
  have hn : ‖v - (b - a) • w‖ < 20 * r := by
    have he : v - (b - a) • w = (x + v - (z + b • w)) - (x - (z + a • w)) := by
      module
    rw [he]
    exact (norm_sub_le _ _).trans_lt (by linarith)
  have hd := WangZahlLot.Obl.wz_direction_density_transfer.scale_sep
    (a := 1) (b := b - a) hv hw (min_le_left _ _) (min_le_right _ _)
  simp only [abs_one, mul_one, one_smul] at hd
  linarith

/-- A convenient cylinder, expressed as the image of a unit tube. -/
def Container (r : ℝ) (z w : Space) : Set Space :=
  AffineMap.homothety (z - (50 : ℝ) • w) (100 : ℝ) ''
    Tube (10 * r) (z - (50 : ℝ) • w) w

theorem mem_container {r : ℝ} {z w p : Space} {t : ℝ}
    (ht : |t| ≤ 50) (hp : ‖p - (z + t • w)‖ < 1000 * r) :
    p ∈ Container r z w := by
  let b := z - (50 : ℝ) • w
  let q := b + (1 / 100 : ℝ) • (p - b)
  have hq : q ∈ Tube (10 * r) b w := by
    apply mem_thickening_iff.mpr
    refine ⟨b + ((t + 50) / 100) • w, ?_, ?_⟩
    · rw [segment_eq_image']
      refine ⟨(t + 50) / 100, ?_, by simp⟩
      obtain ⟨ht0, ht1⟩ := abs_le.mp ht
      constructor <;> linarith
    · rw [dist_eq_norm]
      have he : q - (b + ((t + 50) / 100) • w) =
          (1 / 100 : ℝ) • (p - (z + t • w)) := by
        dsimp [q, b]
        module
      rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
      linarith
  refine ⟨q, hq, ?_⟩
  rw [AffineMap.homothety_apply]
  simp only [vsub_eq_sub, vadd_eq_add]
  dsimp [q, b]
  module

/-- Conflicting coarse tubes all lie in one fixed-length thin cylinder. -/
theorem conflict_subset {δ r : ℝ} (hδ : 0 < δ) {x v z w z' w' : Space}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hw' : ‖w'‖ = 1)
    (hT : Tube δ x v ⊆ Dilate r z w) (hT' : Tube δ x v ⊆ Dilate r z' w') :
    Tube r z' w' ⊆ Container r z w := by
  have hd := direction_close hδ hv hw hT
  have hd' := direction_close hδ hv hw' hT'
  have hww : min ‖w' - w‖ ‖w' + w‖ ≤ 80 * r := by
    have h := WangZahlLot.Obl.wz_affine_robust_cluster_estimate.pd_triangle w' v w
    have hsym : min ‖w' - v‖ ‖w' + v‖ = min ‖v - w'‖ ‖v + w'‖ := by
      rw [norm_sub_rev, add_comm w' v]
    dsimp [WangZahlLot.Obl.wz_affine_robust_cluster_estimate.pd] at h
    rw [hsym] at h
    linarith
  obtain ⟨σ, hσ, hwσ⟩ := WangZahlLot.Obl.wz_balanced_cluster_cover.exists_sign hww
  obtain ⟨s, hs, hxs⟩ := dilate_param
    (hT (self_subset_thickening hδ _ (left_mem_segment ℝ x (x + v))))
  obtain ⟨t, ht, hxt⟩ := dilate_param
    (hT' (self_subset_thickening hδ _ (left_mem_segment ℝ x (x + v))))
  intro p hp
  obtain ⟨u, hu, hpu⟩ := WangZahlLot.Obl.wz_balanced_cluster_cover.exists_param_of_mem_tube hp
  have hut : |u - t| ≤ 7 := by
    have hu' : |u| ≤ 1 := by rw [abs_of_nonneg hu.1]; exact hu.2
    have hab := abs_sub u t
    linarith
  have hpar : |s + (u - t) * σ| ≤ 50 := by
    calc |s + (u - t) * σ| ≤ |s| + |u - t| * |σ| := by
          simpa only [abs_mul] using abs_add_le s ((u - t) * σ)
      _ ≤ 6 + 7 * 1 := add_le_add hs (mul_le_mul hut hσ (abs_nonneg _) (by norm_num))
      _ ≤ 50 := by norm_num
  apply mem_container hpar
  have he : p - (z + (s + (u - t) * σ) • w) =
      (p - (z' + u • w')) + (x - (z + s • w)) - (x - (z' + t • w')) +
        (u - t) • (w' - σ • w) := by module
  have hr : 0 < r := by linarith [norm_nonneg (x - (z + s • w))]
  rw [he]
  calc
    ‖(p - (z' + u • w')) + (x - (z + s • w)) - (x - (z' + t • w')) +
        (u - t) • (w' - σ • w)‖
      ≤ (‖p - (z' + u • w')‖ + ‖x - (z + s • w)‖) +
        ‖x - (z' + t • w')‖ + ‖(u - t) • (w' - σ • w)‖ := by
          calc _ ≤ ‖(p - (z' + u • w')) + (x - (z + s • w)) - (x - (z' + t • w'))‖ +
              ‖(u - t) • (w' - σ • w)‖ := norm_add_le _ _
            _ ≤ _ := by gcongr; exact (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ (‖p - (z' + u • w')‖ + ‖x - (z + s • w)‖) +
        ‖x - (z' + t • w')‖ + 7 * (80 * r) := by
          rw [norm_smul, Real.norm_eq_abs]
          gcongr
    _ < 1000 * r := by linarith

theorem container_volume {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (z w : Space) (hw : ‖w‖ = 1) :
    volume (Container r z w) ≤ ENNReal.ofReal (200000000000 * r ^ 2) := by
  have h := WangZahlLot.Obl.wz_direction_density_transfer.segment_piece_volume_upper
    (z - (50 : ℝ) • w) w hw (T := Icc 0 1) subset_rfl (r := 10 * r) (A := 1)
    (by positivity) zero_le_one (by
      intro s hs t ht
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith [hs.1, hs.2, ht.1, ht.2])
  have he : (fun t : ℝ => z - (50 : ℝ) • w + t • w) '' Icc 0 1 =
      segment ℝ (z - (50 : ℝ) • w) (z - (50 : ℝ) • w + w) := by
    rw [segment_eq_image']
    simp
  rw [he] at h
  rw [Container, Measure.addHaar_image_homothety, finrank_euclideanSpace_fin]
  calc _ ≤ ENNReal.ofReal (|(100 : ℝ) ^ 3|) *
        ENNReal.ofReal (128 * (2 * 1 + 10 * r) * (10 * r) ^ 2) := mul_le_mul' le_rfl h
    _ ≤ _ := by
      rw [← ENNReal.ofReal_mul (abs_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      norm_num
      nlinarith [mul_le_mul_of_nonneg_right hr1 (sq_nonneg r)]

/-- Conflict means that some original fine tube lies in both enlarged tubes. -/
def Conflict {n k : ℕ} (δ r : ℝ) (x v : Fin n → Space) (z w : Fin k → Space)
    (j j' : Fin k) : Prop :=
  ∃ i, Tube δ (x i) (v i) ⊆ Dilate r (z j) (w j) ∧
    Tube δ (x i) (v i) ⊆ Dilate r (z j') (w j')

def conflictBound : ℕ := 1000000 * 200000000000 ^ 2

/-- There are absolutely boundedly many coarse tubes conflicting with any given one. -/
theorem conflict_card_le {n k : ℕ} {δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r) (hr1 : r ≤ 1)
    (x v : Fin n → Space) (z w : Fin k → Space) (hv : ∀ i, ‖v i‖ = 1)
    (hw : ∀ j, ‖w j‖ = 1)
    (hsep : ∀ j j', j ≠ j' → volume (Tube r (z j) (w j) ∩ Tube r (z j') (w j')) ≤
      (1 / 2 : ENNReal) * volume (Tube r (z j) (w j))) (j : Fin k) :
    (Finset.univ.filter (Conflict δ r x v z w j)).card ≤ conflictBound := by
  classical
  let S := Finset.univ.filter (Conflict δ r x v z w j)
  let e : Fin S.card → Fin k := fun a => (S.equivFin.symm a).val
  have he : Function.Injective e := Subtype.val_injective.comp S.equivFin.symm.injective
  have hTW : ∀ a, Tube r (z (e a)) (w (e a)) ⊆ Container r (z j) (w j) := by
    intro a
    obtain ⟨i, hi, hi'⟩ := (Finset.mem_filter.mp (S.equivFin.symm a).property).2
    exact conflict_subset hδ (hv i) (hw j) (hw (e a)) hi hi'
  have hvol := container_volume hr hr1 (z j) (w j) (hw j)
  have hpack := WangZahlLot.Obl.wz_convex_container_tube_packing.packing hr
    (fun a => z (e a)) (fun a => w (e a))
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvol) (fun a => hw (e a)) hTW
    (fun a b hab => hsep (e a) (e b) (he.ne hab))
  have hle : ENNReal.ofReal ((S.card : ℝ) * r ^ 4) ≤
      ENNReal.ofReal ((conflictBound : ℝ) * r ^ 4) := by
    calc _ ≤ ENNReal.ofReal 1000000 * (volume (Container r (z j) (w j))) ^ 2 := hpack
      _ ≤ ENNReal.ofReal 1000000 * (ENNReal.ofReal (200000000000 * r ^ 2)) ^ 2 := by
        gcongr
      _ = _ := by
        rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        norm_num [conflictBound]
        ring
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle
  have hcard : (S.card : ℝ) ≤ conflictBound :=
    (mul_le_mul_iff_left₀ (show 0 < r ^ 4 by positivity)).mp hreal
  exact_mod_cast hcard

end WangZahlLot.Obl.wz_separated_cover_refinement
