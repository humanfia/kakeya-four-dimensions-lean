-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.QuantitativeNormalization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.ConvexBox
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.AffineVolume

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

open Module MeasureTheory Set
open scoped ENNReal

/-- A scaled frame normalization with uniform control of the physical Lipschitz
constant and a Jacobian comparable to the body's physical volume. -/
lemma quantitative_affine_normalization {U : Set E} (hUc : IsCompact U) (hU : Convex ℝ U)
    {x : E} {r S : ℝ} (hr : 0 < r) (hS : 0 < S)
    (hball : Metric.ball x r ⊆ U) (hbound : U ⊆ Metric.closedBall (0 : E) 1) :
    ∃ (f : E ≃ᵃ[ℝ] E) (D : ℝ), 0 < D ∧ f 0 = x ∧
      (f ⁻¹' U ⊆ Metric.closedBall (0 : E) (2 / S)) ∧
      (∀ p q, dist (f p) (f q) ≤ (6 * S) * dist p q) ∧
      (∀ Q : Set E, volume (f '' Q) = ENNReal.ofReal D * volume Q) ∧
      ENNReal.ofReal D ≤ ENNReal.ofReal (64 * S ^ 3) * volume U ∧
      r ^ 3 ≤ D * (2 / S) ^ 3 := by
  obtain ⟨b, hb, hcoord⟩ := exists_bounded_frame_of_ball hUc hr hball
  have hx : x ∈ U := hball (Metric.mem_ball_self hr)
  have hxnorm : ‖x‖ ≤ 1 := by simpa using hbound hx
  have hb2 : ∀ i, ‖b i‖ ≤ 2 := by
    intro i
    have hbi : ‖x + b i‖ ≤ 1 := by simpa using hbound (hb i)
    calc ‖b i‖ = ‖x + b i - x‖ := by rw [add_sub_cancel_left]
      _ ≤ ‖x + b i‖ + ‖x‖ := norm_sub_le _ _
      _ ≤ 2 := by linarith
  let A := (LinearEquiv.smulOfNeZero ℝ E S hS.ne').trans (frameLinear b)
  let f : E ≃ᵃ[ℝ] E := A.toAffineEquiv.trans (AffineEquiv.vaddConst ℝ x)
  let D₀ : ℝ := |LinearMap.det (frameLinear b : E →ₗ[ℝ] E)|
  let D : ℝ := S ^ 3 * D₀
  have hD₀ : 0 < D₀ := frameAffine_jacobian_pos b
  have hD : 0 < D := by dsimp [D]; positivity
  have hA (q : E) : A q = S • frameLinear b q := by
    simp only [A, LinearEquiv.trans_apply, LinearEquiv.smulOfNeZero_apply, map_smul]
  have hflin : (f.linear : E →ₗ[ℝ] E) = S • (frameLinear b : E →ₗ[ℝ] E) := by
    apply LinearMap.ext
    intro q
    exact hA q
  have hf (q : E) : f q = S • frameLinear b q + x := by
    change A q + x = _
    rw [hA]
  have hdet : |LinearMap.det (f.linear : E →ₗ[ℝ] E)| = D := by
    rw [hflin, LinearMap.det_smul, finrank_euclideanSpace_fin, abs_mul,
      abs_of_pos (pow_pos hS 3)]
  have hvol : ∀ Q : Set E, volume (f '' Q) = ENNReal.ofReal D * volume Q := by
    intro Q
    rw [affineEquiv_volume, hdet]
  have hcover : U ⊆ f '' Metric.closedBall (0 : E) (2 / S) := by
    intro p hp
    obtain ⟨q, hq, hqp⟩ := subset_frameAffine_ball x b hcoord hp
    refine ⟨S⁻¹ • q, ?_, ?_⟩
    · have hqnorm : ‖q‖ ≤ 2 := by simpa using hq
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hS)]
      rw [inv_mul_eq_div]
      exact div_le_div_of_nonneg_right hqnorm hS.le
    · rw [hf, map_smul, smul_smul, mul_inv_cancel₀ hS.ne', one_smul]
      exact hqp
  have hpre : f ⁻¹' U ⊆ Metric.closedBall (0 : E) (2 / S) := by
    intro q hq
    obtain ⟨p, hp, hpq⟩ := hcover hq
    exact (f.injective hpq) ▸ hp
  have hnorm : ∀ q : E, ‖f.linear q‖ ≤ (6 * S) * ‖q‖ := by
    intro q
    change ‖A q‖ ≤ _
    rw [hA, norm_smul, Real.norm_eq_abs, abs_of_pos hS]
    have h := frameLinear_norm_le b hb2 q
    nlinarith [mul_le_mul_of_nonneg_left h hS.le]
  refine ⟨f, D, hD, ?_, hpre, affineEquiv_dist_bound f hnorm, hvol, ?_,
    jacobian_lower_of_balls f hD.le hr (by positivity) x hvol (hball.trans hcover)⟩
  · rw [hf, map_zero, smul_zero, zero_add]
  · have hinner : ENNReal.ofReal D₀ * ENNReal.ofReal (1 / 64 : ℝ) ≤ volume U := by
      rw [← volume_quarter_cube, ← frameAffine_volume]
      exact measure_mono (frameAffine_inner_cube_subset hU x hx b hb)
    calc ENNReal.ofReal D = ENNReal.ofReal (64 * S ^ 3) *
          (ENNReal.ofReal D₀ * ENNReal.ofReal (1 / 64 : ℝ)) := by
            rw [← ENNReal.ofReal_mul hD₀.le, ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            dsimp [D]
            ring
      _ ≤ ENNReal.ofReal (64 * S ^ 3) * volume U := mul_le_mul_right hinner _

end WangZahlLot.Obl.wz_regular_transverse_affine_cells
