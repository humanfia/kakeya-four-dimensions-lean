-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_essentially_distinct_tube_count.Geometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
open Set Metric MeasureTheory
open LeanEval.Analysis.WangZahlKakeya

namespace WangZahlLot.Obl.wz_essentially_distinct_tube_count

/-- A tube, with its left endpoint and direction recorded separately. -/
def tube (δ : ℝ) (x v : Space) : Set Space :=
  thickening δ (segment ℝ x (x + v))

lemma segment_param (x v : Space) :
    segment ℝ x (x + v) = (fun t : ℝ => x + t • v) '' Icc 0 1 := by
  simpa only [add_sub_cancel_left] using segment_eq_image' ℝ x (x + v)

/-- Contracting by four fifths leaves room for small changes in both parameters. -/
lemma contraction_subset {δ : ℝ} (hδ : 0 < δ) {x v y w : Space}
    (hx : dist x y ≤ δ / 20) (hv : dist v w ≤ δ / 20) :
    AffineMap.homothety x (4 / 5 : ℝ) '' tube δ x v ⊆ tube δ y w := by
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨z, hz, hpz⟩ := mem_thickening_iff.mp hp
  rw [segment_param] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  let q : ℝ := (4 / 5) * t
  have hq : q ∈ Icc (0 : ℝ) 1 := by
    dsimp [q]
    constructor <;> nlinarith [ht.1, ht.2]
  have hmap : AffineMap.homothety x (4 / 5 : ℝ) (x + t • v) = x + q • v := by
    simp [AffineMap.homothety_apply, q, smul_smul, add_comm]
  have hdist : dist (AffineMap.homothety x (4 / 5 : ℝ) p) (x + q • v) =
      (4 / 5 : ℝ) * dist p (x + t • v) := by
    rw [← hmap, dist_homothety]
    norm_num
  have hseg : dist (x + q • v) (y + q • w) ≤ δ / 10 := by
    calc
      _ ≤ dist x y + dist (q • v) (q • w) := dist_add_add_le ..
      _ = dist x y + q * dist v w := by
        rw [dist_smul₀, Real.norm_eq_abs, abs_of_nonneg hq.1]
      _ ≤ dist x y + dist v w := by
        nlinarith [dist_nonneg (x := v) (y := w), hq.2]
      _ ≤ δ / 10 := by linarith
  apply mem_thickening_iff.mpr
  refine ⟨y + q • w, ?_, ?_⟩
  · rw [segment_param]
    exact ⟨q, hq, rfl⟩
  · have := dist_triangle (AffineMap.homothety x (4 / 5 : ℝ) p)
        (x + q • v) (y + q • w)
    rw [hdist] at this
    linarith

/-- A positive-radius tube has positive volume. -/
lemma tube_volume_pos {δ : ℝ} (hδ : 0 < δ) (x v : Space) :
    0 < volume (tube δ x v) :=
  (measure_ball_pos volume x hδ).trans_le
    (measure_mono (ball_subset_thickening (left_mem_segment ℝ x (x + v)) δ))

/-- Nearby parameters contradict the half-overlap condition. -/
lemma not_close_of_half_overlap {δ : ℝ} (hδ : 0 < δ) {x v y w : Space}
    (hbound : tube δ x v ⊆ ball 0 1)
    (hhalf : volume (tube δ x v ∩ tube δ y w) ≤
      (1 / 2 : ENNReal) * volume (tube δ x v)) :
    ¬ (dist x y ≤ δ / 20 ∧ dist v w ≤ δ / 20) := by
  rintro ⟨hx, hv⟩
  have hself : AffineMap.homothety x (4 / 5 : ℝ) '' tube δ x v ⊆ tube δ x v :=
    contraction_subset hδ (by simpa using (by positivity : (0 : ℝ) ≤ δ / 20))
      (by simpa using (by positivity : (0 : ℝ) ≤ δ / 20))
  have hboth := Set.subset_inter hself (contraction_subset hδ hx hv)
  have hm := (measure_mono hboth).trans hhalf
  rw [Measure.addHaar_image_homothety] at hm
  have hpos := tube_volume_pos hδ x v
  have hfin : volume (tube δ x v) ≠ ⊤ :=
    ((measure_mono hbound).trans_lt measure_ball_lt_top).ne
  have h := (ENNReal.mul_le_mul_iff_left hpos.ne' hfin).mp hm
  have hreal := ENNReal.toReal_mono (by finiteness) h
  norm_num [Space, finrank_euclideanSpace] at hreal

end WangZahlLot.Obl.wz_essentially_distinct_tube_count
