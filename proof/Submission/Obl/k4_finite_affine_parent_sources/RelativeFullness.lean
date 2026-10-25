-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.MajorFrame
import Submission.Obl.k4_finite_affine_parent_sources.VelocityFrame
import Submission.Obl.k4_finite_affine_parent_sources.QuantitativeRows

namespace Submission.Obl.k4_finite_affine_parent_sources

open Submission.Lib.K4FinitePlankAtlases Submission.Lib.K4XInterface
open Submission.Obl.k4_compatible_pair_frame_preparation.Construction

noncomputable section

namespace MajorFrame

/-- Positive cumulative narrowness makes the parent's minor scale small
relative to its time scale, using only physical major-axis fullness. -/
theorem minor_le_of_normalized_area
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.det ≠ 0)
    (q H : ℝ) (hq : 0 < q) (hH : 1 ≤ H)
    (hfull : q / H ≤ r₁ Q)
    (harea : |Q.det| ≤ q ^ 2 / (2 * H ^ 3)) :
    r₂ Q ≤ q / (2 * H ^ 2) := by
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  dsimp only [r₂]
  calc
    _ ≤ (q ^ 2 / (2 * H ^ 3)) / (q / H) :=
      div_le_div₀ ((abs_nonneg _).trans harea) harea (by positivity) hfull
    _ = _ := by field_simp <;> ring

/-- The lower row bound is for the time-normalized velocity matrix.
The parent's transverse direction is absorbed using its actual minor
scale; no angular alignment of the two frames is assumed. -/
theorem normalized_relative_major_lower
    (Q₀ Q₁ : Matrix (Fin 2) (Fin 2) ℝ) (hQ₀ : Q₀.det ≠ 0)
    (q₀ q₁ H : ℝ) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁) (hH : 1 ≤ H)
    (hparent : r₁ Q₀ ≤ H * q₀)
    (hminor : r₂ Q₀ ≤ q₀ / (2 * H ^ 2))
    (hchild : q₁ / H ≤ r₁ Q₁)
    (hrow : ‖frameRow (relativeVelocityFrame q₀ q₁ (frame Q₀) Q₁) 1‖ ≤ H) :
    1 / (2 * H ^ 2) ≤
      ‖frameRow (relativeVelocityFrame q₀ q₁ (frame Q₀) Q₁) 0‖ := by
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  let R := relativeVelocityFrame q₀ q₁ (frame Q₀) Q₁
  have hscaled : plankFrame (r₁ Q₀ / q₀) (r₂ Q₀ / q₀) (tangent Q₀) (nrm Q₀) =
      q₀⁻¹ • frame Q₀ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [frame, plankFrame] <;> ring
  have hprod : plankFrame (r₁ Q₀ / q₀) (r₂ Q₀ / q₀) (tangent Q₀) (nrm Q₀) * R =
      q₁⁻¹ • Q₁ := by
    rw [hscaled]
    dsimp only [R, relativeVelocityFrame]
    rw [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (det_ne_zero hQ₀)),
      Matrix.one_mul, smul_smul]
    congr 1
    field_simp
  have hcol : ∃ j : Fin 2, ‖WithLp.toLp 2 (fun i => Q₁ i j)‖ = r₁ Q₁ := by
    by_cases hc : ‖col1 Q₁‖ ≤ ‖col0 Q₁‖
    · refine ⟨0, ?_⟩
      have heq : WithLp.toLp 2 (fun i => Q₁ i 0) = col0 Q₁ := by
        ext i; fin_cases i <;> rfl
      rw [heq]
      simp only [r₁, longCol, ite_eq_left hc]
    · refine ⟨1, ?_⟩
      have heq : WithLp.toLp 2 (fun i => Q₁ i 1) = col1 Q₁ := by
        ext i; fin_cases i <;> rfl
      rw [heq]
      simp only [r₁, longCol, ite_eq_right hc]
  have hfull : ∃ j : Fin 2, 1 / H ≤
      ‖WithLp.toLp 2 (fun i =>
        (plankFrame (r₁ Q₀ / q₀) (r₂ Q₀ / q₀) (tangent Q₀) (nrm Q₀) * R) i j)‖ := by
    obtain ⟨j, hj⟩ := hcol
    refine ⟨j, ?_⟩
    rw [hprod]
    have heq : WithLp.toLp 2 (fun i => (q₁⁻¹ • Q₁) i j) =
        q₁⁻¹ • WithLp.toLp 2 (fun i => Q₁ i j) := by ext i; rfl
    rw [heq, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hq₁, hj]
    have h : 1 / H ≤ r₁ Q₁ / q₁ := (le_div_iff₀ hq₁).mpr
      (by simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hchild)
    simpa only [div_eq_mul_inv, mul_comm] using h
  apply quantitative_major_row_lower (r₁ Q₀ / q₀) (r₂ Q₀ / q₀) H
    (div_pos (r₁_pos hQ₀) hq₀) (div_nonneg (r₂_nonneg Q₀) hq₀.le) hH
    ((div_le_iff₀ hq₀).mpr hparent) _
    (tangent Q₀) (nrm Q₀) (norm_tangent hQ₀) (norm_nrm hQ₀) R hfull hrow
  apply (div_le_iff₀ hq₀).mpr
  simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hminor

/-- Convert the relative velocity budgets back to the position matrix
used by the frozen tilted-label geometry. The native block length is
exactly the ratio of the two original block lengths. -/
theorem relative_position_row_budgets
    (Q₀ Q₁ : Matrix (Fin 2) (Fin 2) ℝ) (hQ₀ : Q₀.det ≠ 0)
    (q₀ q₁ H g : ℝ) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁) (hH : 1 ≤ H)
    (hparent : r₁ Q₀ ≤ H * q₀)
    (hminor : r₂ Q₀ ≤ q₀ / (2 * H ^ 2))
    (hchild : q₁ / H ≤ r₁ Q₁)
    (hrows : ∀ e : Fin 2,
      ‖frameRow (relativeVelocityFrame q₀ q₁ (frame Q₀) Q₁) e‖ ≤ H)
    (hdet : |(relativeVelocityFrame q₀ q₁ (frame Q₀) Q₁).det| ≤ H * g) :
    (q₁ / q₀) / (2 * H ^ 2) ≤ ‖frameRow ((frame Q₀)⁻¹ * Q₁) 0‖ ∧
      (∀ e : Fin 2, ‖frameRow ((frame Q₀)⁻¹ * Q₁) e‖ ≤ H * (q₁ / q₀)) ∧
      |((frame Q₀)⁻¹ * Q₁).det| ≤ H * (q₁ / q₀) ^ 2 * g := by
  have hlo := normalized_relative_major_lower Q₀ Q₁ hQ₀ q₀ q₁ H hq₀ hq₁ hH
    hparent hminor hchild (hrows 1)
  have heq : (q₁ / q₀)⁻¹ • ((frame Q₀)⁻¹ * Q₁) =
      relativeVelocityFrame q₀ q₁ (frame Q₀) Q₁ := by
    simp only [relativeVelocityFrame, inv_div]
  apply rescale_relative_row_budgets ((frame Q₀)⁻¹ * Q₁) (q₁ / q₀) H g
    (div_pos hq₁ hq₀)
  · simpa only [heq] using hlo
  · simpa only [heq] using hrows
  · simpa only [heq] using hdet

end MajorFrame

end

end Submission.Obl.k4_finite_affine_parent_sources
