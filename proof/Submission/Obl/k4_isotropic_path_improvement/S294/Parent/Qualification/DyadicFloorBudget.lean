-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.DyadicFloorBudget, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/DyadicFloorBudget.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/DyadicFloorBudget.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/DyadicFloorBudget.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.DyadicParameterBins
import Mathlib.Analysis.SpecificLimits.Normed


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory

noncomputable section

theorem dyadicParameterWidth_add (n m : ℕ) :
    dyadicParameterWidth (n+m)=dyadicParameterWidth n*dyadicParameterWidth m := by
  dsimp [dyadicParameterWidth]
  rw [pow_add,mul_inv]

theorem dyadicParameterWidth_antitone : Antitone dyadicParameterWidth := by
  intro n m hnm
  dsimp [dyadicParameterWidth]
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hnm)

/-- The actual aligned widths have a geometric summable original loss.
Its bound is independent of the number of tested levels. -/
theorem dyadic_floor_loss_budget (η C : ℝ) (hη : 0 < η) (hC : 0 ≤ C) (n L : ℕ) :
    (∑ i : Fin L, C*(dyadicParameterWidth (n+i.val))^η) ≤
      C*(dyadicParameterWidth n)^η/(1-(2 : ℝ)^(-η)) := by
  have hq0 : 0 ≤ (2 : ℝ)^(-η) := Real.rpow_nonneg (by norm_num) _
  have hq1 : (2 : ℝ)^(-η) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hp (i : ℕ) : (dyadicParameterWidth i)^η=((2 : ℝ)^(-η))^i := by
    dsimp [dyadicParameterWidth]
    rw [←Real.rpow_neg_one,←Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [←Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),←Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hSum : ∑ i : Fin L, ((2 : ℝ)^(-η))^i.val ≤ (1-(2 : ℝ)^(-η))⁻¹ := by
    rw [Fin.sum_univ_eq_sum_range]
    have hh := (summable_geometric_of_lt_one hq0 hq1).sum_le_tsum (Finset.range L)
      (fun i _ => pow_nonneg hq0 i)
    simpa only [tsum_geometric_of_lt_one hq0 hq1,one_div] using hh
  calc
    (∑ i : Fin L, C*(dyadicParameterWidth (n+i.val))^η) =
        C*(dyadicParameterWidth n)^η*(∑ i : Fin L, ((2 : ℝ)^(-η))^i.val) := by
      simp_rw [dyadicParameterWidth_add,Real.mul_rpow
        (dyadicParameterWidth_pos n).le (dyadicParameterWidth_pos _).le,hp]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ C*(dyadicParameterWidth n)^η*(1-(2 : ℝ)^(-η))⁻¹ :=
      mul_le_mul_of_nonneg_left hSum
        (mul_nonneg hC (Real.rpow_nonneg (dyadicParameterWidth_pos n).le _))
    _ = _ := by rw [div_eq_mul_inv]

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
