import Mathlib

/-!
# Affine complex slices of a thickened real segment
-/

namespace Submission.Obl.k4_quadratic_sheet_continuation

open Set Metric

/-- Moving a segment endpoint by `2r` still leaves a fixed margin for the
complex parameter tube. -/
theorem perturbed_segment_slice_mapsTo
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {p e d : E} {r : ℝ} (hr : 0 < r) (hrhalf : r ≤ (1 : ℝ) / 2)
    (hp : ‖p‖ ≤ 1) (he : ‖e‖ ≤ 1) (hd : d ∈ closedBall e (2 * r)) :
    ‖d - p‖ ≤ 3 ∧
      MapsTo (fun t : ℂ => p + t • (d - p))
        (thickening r (segment ℝ (0 : ℂ) 1))
        (thickening (8 * r) (segment ℝ p e)) := by
  have hde : ‖d - e‖ ≤ 2 * r := by simpa only [mem_closedBall, dist_eq_norm] using hd
  have hdp : ‖d - p‖ ≤ 3 := by
    have ht := dist_triangle d e p
    rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at ht
    have hep := norm_sub_le e p
    linarith
  refine ⟨hdp, ?_⟩
  intro t ht
  obtain ⟨u, hu, htu⟩ := mem_thickening_iff.mp ht
  rw [segment_eq_image_lineMap] at hu
  obtain ⟨θ, hθ, rfl⟩ := hu
  have hθeq : AffineMap.lineMap (0 : ℂ) 1 θ = (θ : ℂ) := by
    simp [AffineMap.lineMap_apply, Complex.real_smul]
  rw [hθeq, dist_eq_norm] at htu
  let y : E := p + (θ : ℂ) • (e - p)
  have hy : y ∈ segment ℝ p e := by
    rw [segment_eq_image_lineMap]
    refine ⟨θ, hθ, ?_⟩
    simp [AffineMap.lineMap_apply, y, Complex.coe_smul, add_comm]
  have hθnorm : ‖(θ : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hθ.1] using hθ.2
  have hdiff : p + t • (d - p) - y =
      (t - (θ : ℂ)) • (d - p) + (θ : ℂ) • (d - e) := by
    dsimp [y]
    module
  apply mem_thickening_iff.mpr
  refine ⟨y, hy, ?_⟩
  calc
    dist (p + t • (d - p)) y =
        ‖(t - (θ : ℂ)) • (d - p) + (θ : ℂ) • (d - e)‖ := by rw [dist_eq_norm, hdiff]
    _ ≤ ‖(t - (θ : ℂ)) • (d - p)‖ + ‖(θ : ℂ) • (d - e)‖ := norm_add_le _ _
    _ = ‖t - (θ : ℂ)‖ * ‖d - p‖ + ‖(θ : ℂ)‖ * ‖d - e‖ := by rw [norm_smul, norm_smul]
    _ ≤ ‖t - (θ : ℂ)‖ * 3 + 1 * (2 * r) := by gcongr
    _ < 8 * r := by nlinarith

end Submission.Obl.k4_quadratic_sheet_continuation
