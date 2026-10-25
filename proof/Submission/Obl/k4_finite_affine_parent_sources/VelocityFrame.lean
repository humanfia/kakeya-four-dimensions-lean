-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
-- Adapted from this LOT tree, o199, session x0695, commit 9dc94f4851c3.
-- Source: Submission/Obl/k4_finite_path_candidate_conversion/DeepStrips.lean.
import Submission.Obl.k4_finite_affine_parent_sources.ParentFrame
import Submission.Obl.k4_finite_affine_parent_sources.StripReturn
import Submission.Obl.k4_finite_positive_mixed_cover_realization.DeepStrips

namespace Submission.Obl.k4_finite_affine_parent_sources

open Submission.Lib.K4XInterface

-- These seven declarations are now part of accepted o234. Keep the existing
-- local names while importing their accepted proofs.
export Submission.Obl.k4_finite_positive_mixed_cover_realization
  (relativeVelocityFrame relativeVelocityFrame_apply relativeVelocityFrame_det
    relativeVelocityFrame_det_ne_zero relativeVelocityFrame_dyadic_det
    relativeVelocityFrame_narrowness_bound relativeVelocityFrame_identity)

/-- The reverse determinant comparison uses the same cumulative widths. -/
theorem relativeVelocityFrame_narrowness_lower
    {N w₀ w₁ error : ℝ} {T₀ T₁ : ℕ} {Q₀ Q₁ : Matrix (Fin 2) (Fin 2) ℝ}
    (hN : 0 < N) (hQ₀ : Q₀.det ≠ 0)
    (h₀ : |Q₀.det| * (4 : ℝ) ^ T₀ ≤ N ^ (-(w₀ - error)))
    (h₁ : N ^ (-(w₁ + error)) ≤ |Q₁.det| * (4 : ℝ) ^ T₁) :
    N ^ (-(w₁ - w₀ + 2 * error)) ≤
      |(relativeVelocityFrame (((2 : ℝ) ^ T₀)⁻¹) (((2 : ℝ) ^ T₁)⁻¹) Q₀ Q₁).det| := by
  rw [relativeVelocityFrame_dyadic_det]
  calc
    _ = N ^ (-(w₁ + error)) / N ^ (-(w₀ - error)) := by
      rw [← Real.rpow_sub hN]
      congr 1
      ring
    _ ≤ _ := div_le_div₀ (by positivity) h₁
      (mul_pos (abs_pos.mpr hQ₀) (by positivity)) h₀

namespace PFrame

open Submission.Obl.k4_remainder_pure_profile_normalization.Normalization

noncomputable section

/-- The major and minor model velocities are the actual parent-normalized velocities. -/
theorem velocity_eq (Φ : PFrame) (l : ℕ × (Fin 6 → ℝ)) :
    WithLp.toLp 2 ![Φ.eb l 3, Φ.eb l 4] =
      Φ.F.q • Matrix.toEuclideanLin Φ.F.D⁻¹ (gv l - Φ.F.u) := by
  ext e
  fin_cases e <;> simp [eb, Frame.normCoeff, gv, toEuclideanLin_apply_fin2] <;> left <;> ring

/-- A model slope strip returns in the actual old chart's normalized
velocity frame. Its normal length is explicit, so width and bias estimates
can use the true relative determinant. -/
theorem strip_return (Φ : PFrame) (hq : Φ.F.q ≠ 0) (hD : Φ.F.D.det ≠ 0)
    (T : ℕ) (u : EuclideanSpace ℝ (Fin 2)) (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (hQ : Q.det ≠ 0) (z : Fin 2 → ℝ) (width : ℝ) :
    let q := ((2 : ℝ) ^ T)⁻¹
    let M := relativeVelocityFrame Φ.F.q q Φ.F.D Q
    let offset := Φ.F.q • Matrix.toEuclideanLin Φ.F.D⁻¹ (u - Φ.F.u)
    ∃ (a : Fin 2 → ℝ) (bias : ℝ), (∑ e, (a e) ^ 2) = 1 ∧
      |bias| ≤ (|z 0| + |offset 1| + |z 1| * |offset 0|) / stripRowLength M (z 1) ∧
      ∀ l : ℕ × (Fin 6 → ℝ),
        |Φ.eb l 4 - z 0 - z 1 * Φ.eb l 3| ≤ width →
        InStrip T u Q a bias (width / stripRowLength M (z 1)) l := by
  dsimp only
  let q := ((2 : ℝ) ^ T)⁻¹
  have hq' : q ≠ 0 := by dsimp [q]; positivity
  let M := relativeVelocityFrame Φ.F.q q Φ.F.D Q
  let offset := Φ.F.q • Matrix.toEuclideanLin Φ.F.D⁻¹ (u - Φ.F.u)
  have hM : M.det ≠ 0 := relativeVelocityFrame_det_ne_zero hq hq' hD hQ
  obtain ⟨a, bias, ha, hb, hfit⟩ := slope_strip_return M hM
    (fun e => offset e) z width
  refine ⟨a, bias, ha, hb, fun l hl => ?_⟩
  have heq := relativeVelocityFrame_identity (q₀ := Φ.F.q) (Q₀ := Φ.F.D) hq' hQ Φ.F.u u (gv l)
  rw [← Φ.velocity_eq] at heq
  have hcoord : ∀ e : Fin 2,
      (![Φ.eb l 3, Φ.eb l 4] : Fin 2 → ℝ) e = offset e +
        ∑ f : Fin 2, M e f * (q * (Matrix.toEuclideanLin Q⁻¹ (gv l - u)) f) := by
    intro e
    have he := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w e) heq
    simpa only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      toEuclideanLin_apply_fin2, Fin.sum_univ_two, M, offset] using he
  have hr := hfit (fun e => q * (Matrix.toEuclideanLin Q⁻¹ (gv l - u)) e)
    ![Φ.eb l 3, Φ.eb l 4] hcoord hl
  simpa only [InStrip, q, M, v, k4_quadratic_finite_greedy_cover.v, gv, mul_assoc] using hr

end

end PFrame

end Submission.Obl.k4_finite_affine_parent_sources
