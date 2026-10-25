-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.Grid.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.Regularize
import Submission.WZ.Obl.wz_balanced_cluster_cover.Basic

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

open MeasureTheory Set Metric
open scoped ENNReal

namespace Grid

open WangZahlLot.Obl.wz_balanced_cluster_cover

/-- A cubic lattice point at spacing `ρ`. -/
def point (ρ : ℝ) (g : Fin 3 → ℤ) : E := WithLp.toLp 2 (fun k => ρ * g k)

lemma point_cell {ρ : ℝ} (hρ : 0 < ρ) (g : Fin 3 → ℤ) : cell ρ (point ρ g) = g := by
  funext k
  simp [cell, point, hρ.ne']

lemma dist_point_cell_le {ρ : ℝ} (hρ : 0 < ρ) (p : E) :
    dist p (point ρ (cell ρ p)) ≤ 2 * ρ := by
  rw [dist_eq_norm]
  apply norm_sub_le_of_cell_eq hρ
  rw [point_cell hρ]

open Classical in
/-- Radius-`4ρ` lattice balls have overlap at most one thousand in dimension three. -/
lemma ball_overlap {ρ : ℝ} (hρ : 0 < ρ) (G : Finset (Fin 3 → ℤ)) (p : E) :
    (G.filter (fun g => p ∈ ball (point ρ g) (4 * ρ))).card ≤ 1000 := by
  classical
  have hsub : G.filter (fun g => p ∈ ball (point ρ g) (4 * ρ)) ⊆ box ρ p (4 * ρ) := by
    intro g hg
    have hd : ‖point ρ g - p‖ ≤ 4 * ρ := by
      have h := (Finset.mem_filter.mp hg).2
      simpa only [mem_ball, dist_eq_norm, norm_sub_rev] using h.le
    have hmem := cell_mem_box hρ hd
    rwa [point_cell hρ] at hmem
  have hcard := Finset.card_le_card hsub
  have hbox := card_box_le hρ p (show 0 ≤ 4 * ρ by positivity)
  have he : 2 * (4 * ρ) / ρ + 2 = (10 : ℝ) := by field_simp; ring
  rw [he] at hbox
  have hbox' : (box ρ p (4 * ρ)).card ≤ 1000 := by exact_mod_cast hbox
  exact hcard.trans hbox'

lemma sum_inter_ball_le {ρ : ℝ} (hρ : 0 < ρ) (G : Finset (Fin 3 → ℤ))
    (P : Set E) (hP : MeasurableSet P) :
    ∑ g ∈ G, volume (P ∩ ball (point ρ g) (4 * ρ)) ≤ 1000 * volume P := by
  simpa using sum_inter_measure_le_of_overlap volume P hP
    (fun g => ball (point ρ g) (4 * ρ)) G (by intro g _; exact measurableSet_ball)
    1000 (fun p _ => ball_overlap hρ G p)

/-- Convexity compares intersections with concentric balls without an aspect ratio loss. -/
lemma homothety_ball_subset {P : Set E} (hP : Convex ℝ P) {p : E} (hp : p ∈ P)
    {r t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    AffineMap.homothety p t '' (P ∩ ball p r) ⊆ P ∩ ball p (t * r) := by
  rintro _ ⟨q, hq, rfl⟩
  have he : AffineMap.homothety p t q = (1 - t) • p + t • q := by
    simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
    module
  refine ⟨?_, ?_⟩
  · rw [he]
    exact hP hp hq.1 (by linarith) ht.le (by ring)
  · rw [mem_ball, dist_eq_norm, AffineMap.homothety_apply]
    simp only [vsub_eq_sub, vadd_eq_add, add_sub_cancel_right, norm_smul,
      Real.norm_eq_abs, abs_of_pos ht]
    exact mul_lt_mul_of_pos_left (by simpa [mem_ball, dist_eq_norm] using hq.2) ht

/-- A ball from the lattice cover lies inside the desired ball and captures at least
one five-hundred-and-twelfth of its relative convex volume. -/
lemma ball_comparison {P : Set E} (hP : Convex ℝ P) {p : E} (hp : p ∈ P)
    {r ρ : ℝ} (hρ : 0 < ρ) (hrlo : r / 16 ≤ ρ) (hrhi : ρ < r / 8) :
    p ∈ ball (point ρ (cell ρ p)) (4 * ρ) ∧
    ball (point ρ (cell ρ p)) (4 * ρ) ⊆ ball p r ∧
    ENNReal.ofReal (1 / 512 : ℝ) * volume (P ∩ ball p r) ≤
      volume (P ∩ ball (point ρ (cell ρ p)) (4 * ρ)) := by
  have hd := dist_point_cell_le hρ p
  have hsub : ball p (r / 8) ⊆ ball (point ρ (cell ρ p)) (4 * ρ) := by
    intro q hq
    have hq' : dist q p < r / 8 := hq
    have htri := dist_triangle q p (point ρ (cell ρ p))
    show dist q (point ρ (cell ρ p)) < 4 * ρ
    linarith
  refine ⟨by show dist p _ < 4 * ρ; linarith, ?_, ?_⟩
  · intro q hq
    have hq' : dist q (point ρ (cell ρ p)) < 4 * ρ := hq
    have htri := dist_triangle_right q p (point ρ (cell ρ p))
    show dist q p < r
    linarith
  · have hhom := homothety_ball_subset hP hp (r := r)
      (show (0 : ℝ) < 1 / 8 by norm_num) (show (1 / 8 : ℝ) ≤ 1 by norm_num)
    have he : (1 / 8 : ℝ) * r = r / 8 := by ring
    rw [he] at hhom
    calc ENNReal.ofReal (1 / 512 : ℝ) * volume (P ∩ ball p r)
        = volume (AffineMap.homothety p (1 / 8 : ℝ) '' (P ∩ ball p r)) := by
          rw [Measure.addHaar_image_homothety, finrank_euclideanSpace_fin]
          norm_num
      _ ≤ volume (P ∩ ball (point ρ (cell ρ p)) (4 * ρ)) :=
        measure_mono (hhom.trans (inter_subset_inter_right P hsub))

end Grid

end WangZahlLot.Obl.wz_regular_transverse_affine_cells
