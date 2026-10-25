/- Adapted from this LOT tree, obligation o200, session x0934, commit 2510f40626244312a0552650c06c57bcfd48d368,
   Submission/Obl/k4_finite_projected_horizontal_candidates/AffineDomainBounds.lean.
   Namespace renamed from Submission.Obl.k4_finite_projected_horizontal_candidates to Submission.Obl.k4_narrow_projected_row_parents.Cmp; earlier source attributions retained. -/
import Mathlib
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetJets

/-! Small real affine matrices send the common comparison ball into a native stable ball. -/

namespace Submission.Obl.k4_narrow_projected_row_parents.Cmp.CommonDomain

open Metric
open Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison

noncomputable section

theorem complex_norm_le_three {B : ℝ} (hB : 0 ≤ B) (z : EuclideanSpace ℂ (Fin 3))
    (hz : ∀ i, ‖z i‖ ≤ B) : ‖z‖ ≤ 3 * B := by
  have hs := EuclideanSpace.norm_sq_eq z
  simp only [Fin.sum_univ_three] at hs
  have h₀ := pow_le_pow_left₀ (norm_nonneg (z 0)) (hz 0) 2
  have h₁ := pow_le_pow_left₀ (norm_nonneg (z 1)) (hz 1) 2
  have h₂ := pow_le_pow_left₀ (norm_nonneg (z 2)) (hz 2) 2
  nlinarith [norm_nonneg z]

theorem complex_matrix_norm_le (M : Matrix (Fin 3) (Fin 3) ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hrow : ∀ i, (∑ j, |M i j|) ≤ r) (z : EuclideanSpace ℂ (Fin 3)) :
    ‖(WithLp.toLp 2 (fun i => ∑ j, (M i j : ℂ) * z j) : EuclideanSpace ℂ (Fin 3))‖ ≤
      3 * r * ‖z‖ := by
  have hcoord (i : Fin 3) : ‖∑ j, (M i j : ℂ) * z j‖ ≤ r * ‖z‖ := by
    calc
      _ ≤ ∑ j, ‖(M i j : ℂ) * z j‖ := norm_sum_le _ _
      _ = ∑ j, |M i j| * ‖z j‖ := by simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ∑ j, |M i j| * ‖z‖ := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (PiLp.norm_apply_le z j) (abs_nonneg _)
      _ = (∑ j, |M i j|) * ‖z‖ := (Finset.sum_mul _ _ _).symm
      _ ≤ r * ‖z‖ := mul_le_mul_of_nonneg_right (hrow i) (norm_nonneg z)
  have h := complex_norm_le_three (mul_nonneg hr (norm_nonneg z))
    (WithLp.toLp 2 (fun i => ∑ j, (M i j : ℂ) * z j)) hcoord
  simpa only [mul_assoc] using h

/-- A common point lies in the eighth ball. A sufficiently small matrix therefore
sends the whole complex comparison ball into that point's stable native ball. -/
theorem affine_ball_containment (b : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (hrow : ∀ i, (∑ j, |M i j|) ≤ ρ / 20)
    (x₀ : EuclideanSpace ℝ (Fin 3)) (hx₀ : ‖x₀‖ ≤ 1 / 8) :
    ∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
      (WithLp.toLp 2 (fun i => (b i : ℂ) + ∑ j, (M i j : ℂ) * z j) : EuclideanSpace ℂ (Fin 3)) ∈
      ball (WithLp.toLp 2 (fun i => (b i : ℂ) + ∑ j, (M i j : ℂ) * emb x₀ j)) ρ := by
  intro z hz
  rw [mem_ball, dist_eq_norm]
  have heq :
      (WithLp.toLp 2 (fun i => (b i : ℂ) + ∑ j, (M i j : ℂ) * z j) : EuclideanSpace ℂ (Fin 3)) -
        WithLp.toLp 2 (fun i => (b i : ℂ) + ∑ j, (M i j : ℂ) * emb x₀ j) =
      WithLp.toLp 2 (fun i => ∑ j, (M i j : ℂ) * (z - emb x₀) j) := by
    ext i
    simp [Finset.sum_sub_distrib, mul_sub]
  rw [heq]
  have h := complex_matrix_norm_le M (show 0 ≤ ρ / 20 by positivity) hrow (z - emb x₀)
  have hz' : ‖z‖ < 4 := by simpa only [mem_ball_zero_iff] using hz
  have hx' : ‖emb x₀‖ ≤ 1 / 8 := by simpa only [norm_emb] using hx₀
  have hdist : ‖z - emb x₀‖ < 5 := by linarith [norm_sub_le z (emb x₀)]
  exact lt_of_le_of_lt h (by nlinarith)

end

end Submission.Obl.k4_narrow_projected_row_parents.Cmp.CommonDomain
