-- Adapted from this LOT tree, obligation o254, branch x0898, commit f25a0cc9, file Submission/Obl/k4_general_parent_wide_layer_candidates/Native/ParentCommonFrame.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
/- Adapted from this LOT tree, obligation o200, session x0934, commit 3ef9d3b45123d3245f500a2dc2bd85270a8fff3d,
   Submission/Obl/k4_finite_projected_horizontal_candidates/ParentCommonFrame.lean. Original source attributions are retained below. -/
import Mathlib
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.CommonPhysicalFrame
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.AffineDomainBounds

/-! The true-packet frame after the common comparison frame. -/

namespace Submission.Obl.k4_general_wide_layer_offset_comparison.Native.CommonDomain

noncomputable section

/-- Linear part of the accepted support zoom of a true parent. -/
def parentMatrix (K Q g : ℝ) (c : Fin 5 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1 / (32 * K * Q), 0, 0;
    0, 1 / (32 * K * Q), 0;
    -c 3 / (16 * K * Q * g), -c 4 / (16 * K * Q * g), 1 / (16 * K * Q * g)]

def parentFromCommonMatrix (K Q q χ g m : ℝ) (c : Fin 5 → ℝ) (u : Code) :
    Matrix (Fin 3) (Fin 3) ℝ := parentMatrix K Q g c * physicalMatrix q χ g m u

theorem parentMatrix_det_ne_zero {K Q g : ℝ} (hK : 0 < K) (hQ : 0 < Q) (hg : 0 < g)
    (c : Fin 5 → ℝ) : (parentMatrix K Q g c).det ≠ 0 := by
  have hdet : (parentMatrix K Q g c).det =
      (32 * K * Q)⁻¹ * (32 * K * Q)⁻¹ * (16 * K * Q * g)⁻¹ := by
    simp [parentMatrix, Matrix.det_fin_three]
  rw [hdet]
  positivity

theorem parentFromCommonMatrix_eq {K Q q χ g m : ℝ} (hK : K ≠ 0) (hQ : Q ≠ 0) (hg : g ≠ 0)
    (c : Fin 5 → ℝ) (u : Code) :
    parentFromCommonMatrix K Q q χ g m c u =
      !![100 * q / (32 * K * Q), 0, 0;
        100 * q * ((u 1 : ℝ) * χ) / (32 * K * Q), 100 * χ / (32 * K * Q), 0;
        100 * q * ((u 3 : ℝ) * g - c 3 - c 4 * ((u 1 : ℝ) * χ)) / (16 * K * Q * g),
        -(100 * c 4 * χ) / (16 * K * Q * g), 100 * m / (16 * K * Q * g)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [parentFromCommonMatrix, parentMatrix, physicalMatrix, Matrix.mul_apply,
      Fin.sum_univ_three] <;> field_simp <;> ring

/-- Rounding the two velocity coefficients changes the true row derivative by
at most two additional old losses. No smallness of a raw polynomial coefficient
or of the transverse velocity itself is used. -/
theorem rounded_parent_slope {K q χ g m t : ℝ} (hK : 1 ≤ K) (hχ : 0 < χ) (hg : 0 < g)
    (hχg : χ ≤ g) (b : Fin 6 → ℝ) (c : Fin 5 → ℝ) (hc : |c 4| ≤ K)
    (hslope : |b 4 - c 3 - c 4 * b 3| ≤ K * g) :
    |((code q χ g m b t) 3 : ℝ) * g - c 3 - c 4 * (((code q χ g m b t) 1 : ℝ) * χ)| ≤
      3 * K * g := by
  let V : ℝ := ((code q χ g m b t) 1 : ℝ) * χ
  let W : ℝ := ((code q χ g m b t) 3 : ℝ) * g
  have hV : |b 3 - V| ≤ χ := by
    simpa [V, code] using Submission.Lib.K4VelocityStrips.midpoint_floor_center_bound hχ (b 3)
  have hW : |W - b 4| ≤ g := by
    simpa [W, code, abs_sub_comm] using Submission.Lib.K4VelocityStrips.midpoint_floor_center_bound hg (b 4)
  have heq : W - c 3 - c 4 * V =
      (W - b 4) + (b 4 - c 3 - c 4 * b 3) + c 4 * (b 3 - V) := by ring
  change |W - c 3 - c 4 * V| ≤ _
  rw [heq]
  calc
    _ ≤ |W - b 4| + |b 4 - c 3 - c 4 * b 3| + |c 4 * (b 3 - V)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ g + K * g + K * χ := by
      rw [abs_mul]
      exact add_le_add (add_le_add hW hslope) (mul_le_mul hc hV (abs_nonneg _) (by linarith))
    _ ≤ 3 * K * g := by
      have h₁ : g ≤ K * g := by nlinarith
      have h₂ := mul_le_mul_of_nonneg_left hχg (show 0 ≤ K by linarith)
      linarith

theorem rounded_major_velocity_bound {K q χ g m t : ℝ} (hK : 1 ≤ K) (hχ : 0 < χ)
    (hχ1 : χ ≤ 1) (b : Fin 6 → ℝ) (hb : |b 3| ≤ K) :
    |((code q χ g m b t) 1 : ℝ) * χ| ≤ 2 * K := by
  have hf := Submission.Lib.K4VelocityStrips.midpoint_floor_center_bound hχ (b 3)
  have h := abs_sub_abs_le_abs_sub ((⌊b 3 / χ⌋ : ℝ) * χ) (b 3)
  rw [abs_sub_comm ((⌊b 3 / χ⌋ : ℝ) * χ) (b 3)] at h
  simp only [code, Matrix.cons_val_one, Matrix.cons_val_zero]
  linarith

end

end Submission.Obl.k4_general_wide_layer_offset_comparison.Native.CommonDomain
