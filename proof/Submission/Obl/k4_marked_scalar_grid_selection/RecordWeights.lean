import Submission.Obl.k4_marked_scalar_grid_selection.Scalar.NodeWeights

namespace Submission.Obl.k4_marked_scalar_grid_selection

open MeasureTheory Set Filter Scalar
open scoped ENNReal

/-- A fixed-power atom cutoff bounds all original record weights over a
bounded interval of velocity depths. -/
theorem realNodeMass_power_bounds {H J : ℕ} {κ : Type*}
    (I : Finset (AtomIndex H J)) (w : Fin H → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hw1 : ∑ j, w j = 1) (code : AtomIndex H J → κ)
    {n m u V B : ℝ} {M : ℕ} (hn : 1 ≤ n) (hm : 0 ≤ m)
    (hu : 0 ≤ u) (huV : u ≤ V)
    (hJ : 1 ≤ J) (hJupper : (J : ℝ) ≤ n ^ (M : ℝ))
    (i : AtomIndex H J) (hi : i ∈ I) (hcut : n ^ (-B) ≤ cellWeight J w i) :
    n ^ (-(B + V)) ≤ realNodeMass I (n ^ (-m)) (n ^ (-u)) w code (code i) ∧
      realNodeMass I (n ^ (-m)) (n ^ (-u)) w code (code i) ≤ n ^ ((M : ℝ) + m) := by
  have hn0 : 0 < n := by linarith
  have hσ : 0 < n ^ (-m) := Real.rpow_pos_of_pos hn0 _
  have hρ : 0 < n ^ (-u) := Real.rpow_pos_of_pos hn0 _
  have hσ₁ : n ^ (-m) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn (by linarith)
  have hρ₁ : n ^ (-u) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn (by linarith)
  constructor
  · calc
      n ^ (-(B + V)) = n ^ (-V) * n ^ (-B) := by
        rw [← Real.rpow_add hn0]; congr 1; ring
      _ ≤ n ^ (-u) * n ^ (-B) := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hn (by linarith)) (Real.rpow_nonneg hn0.le _)
      _ ≤ _ := realNodeMass_lower_cellWeight hJ I hσ hσ₁ hρ.le hρ₁
        (Real.rpow_nonneg hn0.le _) w hw code i hi hcut
  · calc
      _ ≤ (n ^ (-m))⁻¹ * (J : ℝ) := realNodeMass_upper I hσ hρ.le w hw hw1 code _
      _ = n ^ m * (J : ℝ) := by rw [Real.rpow_neg hn0.le, inv_inv]
      _ ≤ n ^ m * n ^ (M : ℝ) :=
        mul_le_mul_of_nonneg_left hJupper (Real.rpow_nonneg hn0.le _)
      _ = n ^ ((M : ℝ) + m) := by rw [← Real.rpow_add hn0]; congr 1; ring

end Submission.Obl.k4_marked_scalar_grid_selection
