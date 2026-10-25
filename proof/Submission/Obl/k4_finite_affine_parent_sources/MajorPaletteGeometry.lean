-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.MajorFrame
import Submission.Obl.k4_raw_localized_native_systems.Packing.FramePowers

namespace Submission.Obl.k4_finite_affine_parent_sources.MajorFrame

open Submission.Obl.k4_compatible_pair_frame_preparation.Construction
open Submission.Lib.K4FinitePlankAtlases

noncomputable section

theorem major_column_le {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0)
    (e : Fin 2) : |frame Q e 0| ≤ r₁ Q := by
  have ht : |tangent Q e| ≤ 1 := by
    simpa only [norm_tangent hQ, Real.norm_eq_abs] using PiLp.norm_apply_le (tangent Q) e
  have heq : frame Q e 0 = r₁ Q * tangent Q e := by
    fin_cases e <;> rfl
  rw [heq, abs_mul, abs_of_pos (r₁_pos hQ)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left ht (r₁_nonneg Q)

theorem palette_minor_column_le {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0)
    (e : Fin 2) : |frame Q e 1| ≤ r₂ Q := by
  have hn : |nrm Q e| ≤ 1 := by
    simpa only [norm_nrm hQ, Real.norm_eq_abs] using PiLp.norm_apply_le (nrm Q) e
  have heq : frame Q e 1 = r₂ Q * nrm Q e := by
    fin_cases e <;> rfl
  rw [heq, abs_mul, abs_of_pos (minor_pos hQ)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hn (r₂_nonneg Q)

/-- A full major axis controls the original planar-code readout by its
major scale alone, even when the parent minor scale is arbitrarily small. -/
theorem inverse_major_row_budget {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0)
    {q H : ℝ} (hq : 0 ≤ q) (hfull : q ≤ H * r₁ Q) :
    |q| * (|(frame Q)⁻¹ 0 0| + |(frame Q)⁻¹ 0 1|) ≤ 2 * H := by
  have he (e : Fin 2) : q * |(frame Q)⁻¹ 0 e| ≤ H := by
    have ht : |tangent Q e| ≤ 1 := by
      simpa only [norm_tangent hQ, Real.norm_eq_abs] using PiLp.norm_apply_le (tangent Q) e
    rw [inverse_major_row hQ e, abs_div, abs_of_pos (r₁_pos hQ)]
    calc
      _ = (q / r₁ Q) * |tangent Q e| := by ring
      _ ≤ (q / r₁ Q) * 1 :=
        mul_le_mul_of_nonneg_left ht (div_nonneg hq (r₁_nonneg Q))
      _ ≤ H := by simpa only [mul_one] using (div_le_iff₀ (r₁_pos hQ)).mpr hfull
  rw [abs_of_nonneg hq, mul_add]
  linarith [he 0, he 1]

theorem major_velocity_column_le {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0)
    {q H : ℝ} (hq : 0 < q) (hmajor : r₁ Q ≤ H * q) (e : Fin 2) :
    |(q⁻¹ • frame Q) e 0| ≤ H := by
  simp only [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hq)]
  calc
    _ ≤ q⁻¹ * (H * q) :=
      mul_le_mul_of_nonneg_left ((major_column_le hQ e).trans hmajor) (inv_nonneg.mpr hq.le)
    _ = H := by field_simp [hq.ne']

theorem minor_velocity_column_le {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0)
    {q a : ℝ} (hq : 0 < q) (hminor : r₂ Q ≤ q * a) (e : Fin 2) :
    |(q⁻¹ • frame Q) e 1| ≤ a := by
  simp only [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hq)]
  calc
    _ ≤ q⁻¹ * (q * a) :=
      mul_le_mul_of_nonneg_left ((palette_minor_column_le hQ e).trans hminor) (inv_nonneg.mpr hq.le)
    _ = a := by field_simp [hq.ne']

/-- Apply the accepted physical minor-width estimate to this exact major
frame; its width is the same determinant divided by the same long column. -/
theorem minor_width_power {Q : Matrix (Fin 2) (Fin 2) ℝ}
    {N q g band u : ℝ} (hN : 1 ≤ N) (hq : 0 < q) (hg : 0 ≤ g)
    (hdet : |Q.det| ≤ q ^ 2 * g * N ^ (2 * band))
    (hmajor : q * N ^ (-u) ≤ r₁ Q) :
    r₂ Q ≤ q * g * N ^ (2 * band + u) := by
  exact Submission.Obl.k4_raw_localized_native_systems.Packing.minor_width_power_bound
    hN hq hg hdet hmajor

end
end Submission.Obl.k4_finite_affine_parent_sources.MajorFrame
