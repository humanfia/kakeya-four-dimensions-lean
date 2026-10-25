-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_fibre_multiplicity_gain.CoarseCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_fibre_multiplicity_gain.Defs
import Submission.WZ.Obl.wz_tube_packing_bound

set_option autoImplicit false

/-!
# Essentially distinct coarse tubes: the basic tools

Ported from x0418's and x0449's `CoarseCount.lean` on o152's branches (namespace renamed;
only the lemmas used by the quadratic count are kept).

Write a point `p` of a `ρ`-tube as `p = y k + t_k w k + q_k` with `t_k ∈ [0, 1]` and
`‖q_k‖ < ρ` (`coarse_decomp`). If two tubes have `t_k`, `w k` and `q_k` close, then
`y k' = y k + s w k + q` with `|s| ≤ 1/20` and `‖q‖ ≤ ρ/20`, and the homothety argument of
`WangZahlLot.Obl.wz_tube_packing_bound` (`coarse_not_close`) contradicts the half-overlap
condition.
-/

namespace WangZahlLot.Obl.wz_move_two_fibre_multiplicity_gain

open MeasureTheory Metric Set LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

/-- Two tubes of a family with the half-overlap condition are never close (a variant of
`WangZahlLot.Obl.wz_tube_packing_bound.not_close` for tubes anywhere in space: a tube is
bounded, so its volume is finite). -/
theorem coarse_not_close {δ s : ℝ} {x v y w q : Space} (hδ : 0 < δ)
    (hover : volume (thickening δ (segment ℝ x (x + v)) ∩ thickening δ (segment ℝ y (y + w)))
      ≤ (1 / 2 : ℝ≥0∞) * volume (thickening δ (segment ℝ x (x + v))))
    (hs : |s| ≤ 1 / 20) (hvw : ‖v - w‖ ≤ δ / 20) (hq : ‖q‖ ≤ δ / 20)
    (hy : y = x + s • v + q) : False := by
  set T := thickening δ (segment ℝ x (x + v)) with hT
  have hpos : volume T ≠ 0 :=
    (WangZahlLot.Obl.wz_tube_packing_bound.tube_volume_pos hδ x v).ne'
  have hfin : volume T ≠ ∞ :=
    ((isBounded_closedBall.subset
      (segment_subset_closedBall_left x (x + v))).thickening.measure_lt_top).ne
  have h1 : ENNReal.ofReal ((9 / 10 : ℝ) ^ 3) * volume T
      ≤ volume (T ∩ thickening δ (segment ℝ y (y + w))) := by
    calc ENNReal.ofReal ((9 / 10 : ℝ) ^ 3) * volume T
        = volume (AffineMap.homothety (x + (10 * s + 1 / 2) • v) (9 / 10 : ℝ) '' T) := by
          rw [Measure.addHaar_image_homothety, finrank_euclideanSpace_fin]
          congr 2
          rw [abs_of_pos (by norm_num)]
      _ ≤ _ := measure_mono
          (WangZahlLot.Obl.wz_tube_packing_bound.homothety_image_subset hs hvw hq hy)
  have h2 := (ENNReal.mul_le_mul_iff_left hpos hfin).mp (h1.trans hover)
  have h3 : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
  rw [h3, ENNReal.ofReal_le_ofReal_iff (by norm_num)] at h2
  norm_num at h2

/-- A point of a tube is `x + t v + q` with `t ∈ [0, 1]` and `‖q‖ < ρ`. -/
theorem coarse_decomp {ρ : ℝ} {p x v : Space} (hp : p ∈ Tube ρ x v) :
    ∃ t : ℝ, ∃ q : Space, 0 ≤ t ∧ t ≤ 1 ∧ ‖q‖ < ρ ∧ p = x + t • v + q := by
  obtain ⟨z, hz, hpz⟩ := mem_thickening_iff.mp hp
  rw [segment_eq_image'] at hz
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hz
  refine ⟨t, p - (x + t • (x + v - x)), ht0, ht1, ?_, ?_⟩
  · rw [← dist_eq_norm]; exact hpz
  · rw [add_sub_cancel_left]; abel

/-- Two vectors whose three coordinates differ by less than `ε` are `2 ε`-close. -/
theorem coarse_norm_sub_le {ε : ℝ} {u u' : Space} (h0 : |u 0 - u' 0| < ε)
    (h1 : |u 1 - u' 1| < ε) (h2 : |u 2 - u' 2| < ε) : ‖u - u'‖ ≤ 2 * ε := by
  have hε : 0 < ε := (abs_nonneg _).trans_lt h0
  have n : ‖u - u'‖ ^ 2 = (u 0 - u' 0) ^ 2 + (u 1 - u' 1) ^ 2 + (u 2 - u' 2) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    simp only [PiLp.sub_apply]
  have g0 : (u 0 - u' 0) ^ 2 ≤ ε ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h0.le 2
  have g1 : (u 1 - u' 1) ^ 2 ≤ ε ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1.le 2
  have g2 : (u 2 - u' 2) ^ 2 ≤ ε ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2.le 2
  have h : ‖u - u'‖ ^ 2 ≤ (2 * ε) ^ 2 := by
    rw [n]; nlinarith [sq_nonneg ε]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h

end WangZahlLot.Obl.wz_move_two_fibre_multiplicity_gain
