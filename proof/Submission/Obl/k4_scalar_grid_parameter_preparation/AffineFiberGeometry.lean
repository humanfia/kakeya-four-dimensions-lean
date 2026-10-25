/- Adapted from this LOT tree, o092, session x0317, commit d881f97f20e4.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/AffineFiberGeometry.lean -/
import Submission.Obl.k4_scalar_grid_parameter_preparation.TraceRectangle
import Submission.Obl.k4_fixed_budget_quadratic_recovery.ScalarCandidates

/-! A physical cell and an original velocity bin control the old affine intercept. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

open Set
open Submission.Obl.k4_fixed_budget_quadratic_recovery

theorem scalar_intercept_difference_of_fine_cells (ξ K : ℝ) (hξ : 0 < ξ)
    (a b : Fin 5 → ℝ) (t u : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (hb : |b 1| ≤ K)
    (hT : (⌊t / ξ⌋ : ℤ) = ⌊u / ξ⌋)
    (hY : (⌊scalarY a t / ξ⌋ : ℤ) = ⌊scalarY b u / ξ⌋)
    (hV : (⌊a 1 / ξ⌋ : ℤ) = ⌊b 1 / ξ⌋) : |a 0 - b 0| ≤ (K + 2) * ξ := by
  have hdiff (x y : ℝ) (hxy : (⌊x / ξ⌋ : ℤ) = ⌊y / ξ⌋) : |x - y| ≤ ξ := by
    simpa only [Real.dist_eq] using scalarVelocityBin_diameter_le hξ
      (show x ∈ scalarVelocityBin ξ ⌊x / ξ⌋ from rfl)
      (show y ∈ scalarVelocityBin ξ ⌊x / ξ⌋ from hxy.symm)
  have htdiff := hdiff t u hT
  have hydiff := hdiff (scalarY a t) (scalarY b u) hY
  have hvdiff := hdiff (a 1) (b 1) hV
  have ht₁ : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  have htdiff' : |u - t| ≤ ξ := by simpa only [abs_sub_comm] using htdiff
  have hre : a 0 - b 0 = (scalarY a t - scalarY b u) + (-t) * (a 1 - b 1) + (u - t) * b 1 := by
    dsimp [scalarY]
    ring
  calc
    _ = |(scalarY a t - scalarY b u) + (-t) * (a 1 - b 1) + (u - t) * b 1| := congrArg abs hre
    _ ≤ |scalarY a t - scalarY b u| + |(-t) * (a 1 - b 1)| + |(u - t) * b 1| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ ξ + 1 * ξ + ξ * K := add_le_add (add_le_add hydiff (by
      rw [abs_mul,abs_neg]
      exact mul_le_mul ht₁ hvdiff (abs_nonneg _) (by norm_num))) (by
      rw [abs_mul]
      exact mul_le_mul htdiff' hb (abs_nonneg _) hξ.le)
    _ = _ := by ring

theorem scalar_intercept_near_affine_bin (ξ K : ℝ) (hξ : 0 < ξ)
    (a b : Fin 5 → ℝ) (t u : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (hb : |b 1| ≤ K)
    (hT : (⌊t / ξ⌋ : ℤ) = ⌊u / ξ⌋)
    (hY : (⌊scalarY a t / ξ⌋ : ℤ) = ⌊scalarY b u / ξ⌋)
    (hV : (⌊a 1 / ξ⌋ : ℤ) = ⌊b 1 / ξ⌋) (q : ℤ)
    (hq : a 0 ∈ scalarVelocityBin ξ q) : |b 0 - ξ * (q : ℝ)| ≤ (K + 3) * ξ := by
  have hd := scalar_intercept_difference_of_fine_cells ξ K hξ a b t u ht hb hT hY hV
  have he := scalarVelocityBin_center_error hξ hq
  calc
    _ ≤ |b 0 - a 0| + |a 0 - ξ * (q : ℝ)| := abs_sub_le _ _ _
    _ ≤ (K + 2) * ξ + ξ := add_le_add (by simpa only [abs_sub_comm] using hd) he
    _ = _ := by ring

end Submission.Obl.k4_scalar_grid_parameter_preparation
