-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.RegularCells.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.RegularPruning
import Submission.WZ.Obl.kakeya_three_le_dimH_of_tube_estimate.Packing

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric
open scoped ENNReal Classical

/-- Radius-`2r` balls about an `r`-separated family in three dimensions have
multiplicity at most `125`. -/
theorem separated_ball_overlap (F : Finset Space) {r : ℝ} (hr : 0 < r)
    (hsep : ∀ x ∈ F, ∀ y ∈ F, x ≠ y → r < dist x y) (p : Space) :
    (F.filter fun q => p ∈ closedBall q (2 * r)).card ≤ 125 := by
  classical
  let S := F.filter fun q => p ∈ closedBall q (2 * r)
  let f : Space → Space := fun q => r⁻¹ • (q - p)
  have hinj : Function.Injective f := by
    intro x y hxy
    have hh := congrArg (fun z : Space => r • z) hxy
    simpa [f, smul_smul, hr.ne'] using hh
  have hnorm : ∀ q ∈ S.image f, ‖q‖ ≤ 2 := by
    intro q hq
    obtain ⟨q, hqS, rfl⟩ := Finset.mem_image.mp hq
    have hd : dist q p ≤ 2 * r := by
      simpa only [mem_closedBall, dist_comm] using (Finset.mem_filter.mp hqS).2
    dsimp only [f]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), ← dist_eq_norm]
    exact (inv_mul_le_iff₀ hr).mpr (by linarith)
  have hsep' : ∀ x ∈ S.image f, ∀ y ∈ S.image f, x ≠ y → 1 ≤ ‖x - y‖ := by
    intro x hx y hy hxy
    obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y, hyS, rfl⟩ := Finset.mem_image.mp hy
    have hne : x ≠ y := fun he => hxy (congrArg f he)
    have hd := (hsep x (Finset.mem_filter.mp hxS).1 y (Finset.mem_filter.mp hyS).1 hne).le
    change 1 ≤ ‖r⁻¹ • (x - p) - r⁻¹ • (y - p)‖
    rw [← smul_sub, show (x - p) - (y - p) = x - y by abel,
      norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), ← dist_eq_norm]
    exact (le_inv_mul_iff₀ hr).mpr (by simpa using hd)
  have hc := Besicovitch.card_le_of_separated (S.image f) hnorm hsep'
  rw [Finset.card_image_of_injective S hinj] at hc
  simpa only [finrank_euclideanSpace_fin, show 5 ^ 3 = (125 : ℕ) by norm_num] using hc

/-- The intersections of the preceding balls with any reference body have
bounded total volume, with no assumption on its shape. -/
theorem separated_cell_sum {W : Set Space} (hW : MeasurableSet W)
    (F : Finset Space) {r : ℝ} (hr : 0 < r)
    (hsep : ∀ x ∈ F, ∀ y ∈ F, x ≠ y → r < dist x y) :
    ∑ q ∈ F, volume (W ∩ closedBall q (2 * r)) ≤ 125 * volume W := by
  exact sum_measure_inter_le_of_overlap volume F (fun q => closedBall q (2 * r))
    (fun _ _ => measurableSet_closedBall) W hW 125 (fun p _ => separated_ball_overlap F hr hsep p)

/-- Convexity compares a nearby smaller cell to the intersection of the body
with the larger ball. A homothety of ratio `1/4` proves the comparison. -/
theorem convex_cell_volume_comparison {W : Set Space} (hW : Convex ℝ W)
    {p q : Space} (hq : q ∈ W) {r : ℝ} (hr : 0 < r) (hpq : dist p q ≤ r) :
    ENNReal.ofReal (1 / 64 : ℝ) * volume (W ∩ ball p (4 * r)) ≤
      volume (W ∩ closedBall q (2 * r)) := by
  have hsub : AffineMap.homothety q (1 / 4 : ℝ) '' (W ∩ ball p (4 * r)) ⊆
      W ∩ closedBall q (2 * r) := by
    rintro _ ⟨x, hx, rfl⟩
    constructor
    · simpa only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, add_comm] using
        hW.add_smul_sub_mem hq hx.1 (by norm_num : (1 / 4 : ℝ) ∈ Icc 0 1)
    · rw [mem_closedBall, AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add,
        dist_eq_norm, add_sub_cancel_right, norm_smul, Real.norm_eq_abs]
      have hxp : dist x p < 4 * r := hx.2
      have hd : dist x q ≤ 5 * r :=
        (dist_triangle x p q).trans (by linarith)
      rw [dist_eq_norm] at hd
      norm_num
      linarith
  have hh := measure_mono (μ := volume) hsub
  rw [Measure.addHaar_image_homothety, finrank_euclideanSpace_fin] at hh
  norm_num at hh ⊢
  exact hh

/-- Shrinking a ball by at most a factor of two preserves at least one eighth
of its intersection with a convex body, when the centre belongs to that body. -/
theorem convex_ball_half_volume {W : Set Space} (hW : Convex ℝ W)
    {p : Space} (hp : p ∈ W) {r s : ℝ} (hsmall : r ≤ 2 * s) :
    ENNReal.ofReal (1 / 8 : ℝ) * volume (W ∩ ball p r) ≤ volume (W ∩ ball p s) := by
  have hsub : AffineMap.homothety p (1 / 2 : ℝ) '' (W ∩ ball p r) ⊆ W ∩ ball p s := by
    rintro _ ⟨x, hx, rfl⟩
    constructor
    · simpa only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, add_comm] using
        hW.add_smul_sub_mem hp hx.1 (by norm_num : (1 / 2 : ℝ) ∈ Icc 0 1)
    · rw [mem_ball, AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add,
        dist_eq_norm, add_sub_cancel_right, norm_smul, Real.norm_eq_abs]
      have hd : ‖x - p‖ < r := by simpa only [mem_ball, dist_eq_norm] using hx.2
      norm_num
      linarith
  have hh := measure_mono (μ := volume) hsub
  rw [Measure.addHaar_image_homothety, finrank_euclideanSpace_fin] at hh
  norm_num at hh ⊢
  exact hh

/-- At any fixed radius, a bounded convex body admits finitely many cells with
controlled total volume, covering every point by a quantitatively substantial cell. -/
theorem convex_regular_cells {W : Set Space} (hW : Convex ℝ W)
    (hWm : MeasurableSet W) (hWt : TotallyBounded W) {r : ℝ} (hr : 0 < r) :
    ∃ F : Finset Space, (↑F : Set Space) ⊆ W ∧
      (∑ q ∈ F, volume (W ∩ closedBall q (2 * r)) ≤ 125 * volume W) ∧
      ∀ p ∈ W, ∃ q ∈ F, p ∈ W ∩ closedBall q (2 * r) ∧
        W ∩ closedBall q (2 * r) ⊆ W ∩ ball p (4 * r) ∧
        ENNReal.ofReal (1 / 64 : ℝ) * volume (W ∩ ball p (4 * r)) ≤
          volume (W ∩ closedBall q (2 * r)) := by
  obtain ⟨F, hFW, hsep, hcover⟩ :=
    WangZahlLot.Obl.kakeya_three_le_dimH_of_tube_estimate.exists_finset_separated_cover hWt hr
  refine ⟨F, hFW, separated_cell_sum hWm F hr hsep, ?_⟩
  intro p hp
  obtain ⟨q, hq, hpq⟩ := mem_iUnion₂.mp (hcover hp)
  have hd : dist p q ≤ r := hpq
  refine ⟨q, hq, ⟨hp, ?_⟩, ?_, convex_cell_volume_comparison hW (hFW hq) hr hd⟩
  · exact hd.trans (by linarith)
  · intro x hx
    refine ⟨hx.1, ?_⟩
    have hxp := dist_triangle x q p
    rw [dist_comm q p] at hxp
    have hxq : dist x q ≤ 2 * r := hx.2
    exact hxp.trans_lt (by linarith)

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
