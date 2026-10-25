-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.AffineVolume.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.Types

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

open MeasureTheory Set
open scoped ENNReal

lemma affineEquiv_apply (f : E ≃ᵃ[ℝ] E) (q : E) : f q = f.linear q + f 0 := by
  simpa only [vadd_eq_add, add_zero] using f.map_vadd (0 : E) q

lemma affineEquiv_volume (f : E ≃ᵃ[ℝ] E) (Q : Set E) :
    volume (f '' Q) = ENNReal.ofReal |LinearMap.det (f.linear : E →ₗ[ℝ] E)| * volume Q := by
  have he : f '' Q = (fun y : E => y + f 0) '' ((f.linear : E →ₗ[ℝ] E) '' Q) := by
    rw [Set.image_image]
    exact congrArg (fun g : E → E => g '' Q) (funext (affineEquiv_apply f))
  rw [he, Set.image_add_right, measure_preimage_add_right, Measure.addHaar_image_linearMap]

lemma affineEquiv_jacobian_pos (f : E ≃ᵃ[ℝ] E) :
    0 < |LinearMap.det (f.linear : E →ₗ[ℝ] E)| :=
  abs_pos.mpr (isUnit_iff_ne_zero.mp f.linear.isUnit_det')

lemma affineEquiv_dist_bound (f : E ≃ᵃ[ℝ] E) {C : ℝ}
    (hlinear : ∀ q : E, ‖f.linear q‖ ≤ C * ‖q‖) (p q : E) :
    dist (f p) (f q) ≤ C * dist p q := by
  rw [dist_eq_norm, dist_eq_norm]
  have he : f p - f q = f.linear (p - q) := by
    rw [affineEquiv_apply f p, affineEquiv_apply f q, map_sub]
    abel
  rw [he]
  exact hlinear _

lemma ball_subset_affine_preimage (f : E ≃ᵃ[ℝ] E) {C r : ℝ} (hC : 0 < C)
    (hbound : ∀ p q, dist (f p) (f q) ≤ C * dist p q) (x : E) :
    Metric.ball (f.symm x) (r / C) ⊆ f ⁻¹' Metric.ball x r := by
  intro p hp
  have h := hbound p (f.symm x)
  rw [f.apply_symm_apply] at h
  apply lt_of_le_of_lt h
  rw [Metric.mem_ball, lt_div_iff₀ hC] at hp
  nlinarith

/-- Comparing an inner physical ball and an outer normalized ball gives a lower
bound for the affine Jacobian. -/
lemma jacobian_lower_of_balls (f : E ≃ᵃ[ℝ] E) {D r R : ℝ} (hD : 0 ≤ D)
    (hr : 0 < r) (hR : 0 ≤ R) (x : E)
    (hvol : ∀ Q : Set E, volume (f '' Q) = ENNReal.ofReal D * volume Q)
    (hcontain : Metric.ball x r ⊆ f '' Metric.closedBall (0 : E) R) :
    r ^ 3 ≤ D * R ^ 3 := by
  have h : volume (Metric.ball x r) ≤ volume (f '' Metric.closedBall (0 : E) R) :=
    measure_mono hcontain
  rw [Measure.addHaar_ball_of_pos volume x hr, hvol,
    Measure.addHaar_closedBall volume (0 : E) hR, finrank_euclideanSpace_fin,
    ← mul_assoc] at h
  have hcoeff := (ENNReal.mul_le_mul_iff_left
    (Metric.measure_ball_pos volume (0 : E) (by norm_num : (0 : ℝ) < 1)).ne'
    measure_ball_lt_top.ne).mp h
  rw [← ENNReal.ofReal_mul hD] at hcoeff
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hcoeff

end WangZahlLot.Obl.wz_regular_transverse_affine_cells
