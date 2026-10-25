import Submission.Obl.k4_quadratic_discriminant_safe_paths.Anchor
import Submission.Obl.k4_quadratic_discriminant_safe_paths.Assembly

/-!
# The real-anchor input of the assembly

`AnchorBound` from `volume_anchor_sublevel_le` with `m = A⁻¹`, `θ = A⁻¹ / 512`
(so `128 θ = A⁻¹ / 4`) and the threshold `η = K (A ^ 3)⁻¹`, `K = 1 / 301989888`,
which makes `576 η = (A ^ 3)⁻¹ / 524288 < m θ² = (A ^ 3)⁻¹ / 262144`.
-/

namespace Submission.Obl.k4_quadratic_discriminant_safe_paths

open Set Metric MeasureTheory

theorem anchorBound : AnchorBound := by
  refine ⟨1 / 301989888, by norm_num, 3, by norm_num, ?_⟩
  intro A hA P hP a ha hs
  have hApos : 0 < A := by linarith
  have hθ : 0 < A⁻¹ / 512 := by positivity
  have hθ1 : A⁻¹ / 512 ≤ 1 := by
    have : A⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    linarith
  have hη : 0 ≤ 1 / 301989888 * (A ^ 3)⁻¹ := by positivity
  have hηθ : 576 * (1 / 301989888 * (A ^ 3)⁻¹) < A⁻¹ * (A⁻¹ / 512) ^ 2 := by
    have hcube : 0 < (A ^ 3)⁻¹ := by positivity
    have heq : A⁻¹ * (A⁻¹ / 512) ^ 2 = (A ^ 3)⁻¹ / 262144 := by
      field_simp
      norm_num
    rw [heq]
    linarith
  have hsub : {x : RealSpace | x ∈ closedBall (0 : RealSpace) (1 / 8) ∧
      |MvPolynomial.eval (fun i => x i) P| < 1 / 301989888 * (A ^ 3)⁻¹} ⊆
      {x : RealSpace | x ∈ closedBall (0 : RealSpace) (1 / 8) ∧
        |MvPolynomial.eval (fun i => x i) P| ≤ 1 / 301989888 * (A ^ 3)⁻¹} :=
    fun x hx => ⟨hx.1, hx.2.le⟩
  calc
    _ ≤ _ := measure_mono hsub
    _ ≤ ENNReal.ofReal (128 * (A⁻¹ / 512)) *
        volume (closedBall (0 : RealSpace) (1 / 8)) :=
      volume_anchor_sublevel_le P hP a ha hθ hθ1 hη hs hηθ
    _ = ENNReal.ofReal (A⁻¹ / 4) * volume (closedBall (0 : RealSpace) (1 / 8)) := by
      congr 2
      ring

end Submission.Obl.k4_quadratic_discriminant_safe_paths
