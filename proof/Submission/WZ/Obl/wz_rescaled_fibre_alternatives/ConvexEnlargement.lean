-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_rescaled_fibre_alternatives.ConvexEnlargement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.PullbackGeometry
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.ConvexBox

namespace WangZahlLot.Obl.wz_rescaled_fibre_alternatives

open MeasureTheory Set Metric
open scoped ENNReal

noncomputable section

def convexExpansionLoss (C : ℝ) : ℝ := 512 * (4 * C + 2) ^ 3

lemma convexExpansionLoss_pos {C : ℝ} (hC : 0 ≤ C) : 0 < convexExpansionLoss C := by
  unfold convexExpansionLoss
  positivity

/-- A bounded open convex set has a controlled convex enlargement containing
all fixed-factor dilations about all of its points. -/
lemma convex_enlargement {W : Set Space} (hW : Convex ℝ W) (hWo : IsOpen W)
    (hWb : Bornology.IsBounded W) (hWne : W.Nonempty) {C : ℝ} (hC : 0 ≤ C) :
    ∃ V : Set Space, Convex ℝ V ∧
      (∀ p ∈ W, AffineMap.homothety p C '' W ⊆ V) ∧
      volume V ≤ ENNReal.ofReal (convexExpansionLoss C) * volume W := by
  obtain ⟨x, hx⟩ := hWne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hWo x hx
  obtain ⟨g, J, hJ, hg0, hinner, houter, hvol⟩ :=
    WangZahlLot.Obl.wz_regular_transverse_affine_cells.exists_affine_normalization
      hWb.isCompact_closure hW.closure hr (hball.trans subset_closure)
  let R := 4 * C + 2
  have hR : 0 < R := by dsimp [R]; positivity
  let V := g '' closedBall (0 : Space) R
  refine ⟨V, (convex_closedBall (0 : Space) R).affine_image g.toAffineMap, ?_, ?_⟩
  · intro p hp q hq
    obtain ⟨q₀, hq₀, rfl⟩ := hq
    obtain ⟨p', hp', hp'e⟩ := houter (subset_closure hp)
    obtain ⟨q', hq', hq'e⟩ := houter (subset_closure hq₀)
    subst p q₀
    refine ⟨AffineMap.homothety p' C q', ?_, ?_⟩
    · rw [mem_closedBall_zero_iff, AffineMap.homothety_apply]
      simp only [vsub_eq_sub, vadd_eq_add]
      have hp'n : ‖p'‖ ≤ 2 := by simpa using hp'
      have hq'n : ‖q'‖ ≤ 2 := by simpa using hq'
      calc
        _ ≤ ‖C • (q' - p')‖ + ‖p'‖ := norm_add_le _ _
        _ = C * ‖q' - p'‖ + ‖p'‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC]
        _ ≤ C * (‖q'‖ + ‖p'‖) + ‖p'‖ := by gcongr; exact norm_sub_le _ _
        _ ≤ R := by dsimp [R]; nlinarith
    · exact g.toAffineMap.apply_lineMap p' q' C
  · have hinner' : ENNReal.ofReal J * ENNReal.ofReal (1 / 64 : ℝ) ≤ volume W := by
      rw [← WangZahlLot.Obl.wz_regular_transverse_affine_cells.volume_quarter_cube, ← hvol]
      exact (measure_mono hinner).trans_eq
        (measure_closure_of_null_frontier (hW.addHaar_frontier volume))
    have hballvol : volume (closedBall (0 : Space) R) ≤ ENNReal.ofReal (8 * R ^ 3) := by
      rw [EuclideanSpace.volume_closedBall_fin_three,
        ← ENNReal.ofReal_pow hR.le, ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hpi := Real.pi_lt_four
      nlinarith [mul_pos hR (sq_pos_of_pos hR)]
    calc
      volume V = ENNReal.ofReal J * volume (closedBall (0 : Space) R) := hvol _
      _ ≤ ENNReal.ofReal J * ENNReal.ofReal (8 * R ^ 3) := mul_le_mul_right hballvol _
      _ = ENNReal.ofReal (convexExpansionLoss C) *
          (ENNReal.ofReal J * ENNReal.ofReal (1 / 64 : ℝ)) := by
        rw [← ENNReal.ofReal_mul hJ.le, ← ENNReal.ofReal_mul hJ.le,
          ← ENNReal.ofReal_mul (convexExpansionLoss_pos hC).le]
        congr 1
        dsimp [convexExpansionLoss, R]
        ring
      _ ≤ _ := mul_le_mul_right hinner' _

end
end WangZahlLot.Obl.wz_rescaled_fibre_alternatives
