-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.ShallowClockBudgets, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/ShallowClockBudgets.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1046 (branch x0943), commit 1fcc75a78b90aa1b479052c83612b68563af73b6,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/ShallowClockBudgets.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ParentRenewalBudgets

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open scoped ENNReal

noncomputable section

/-- Two clock cuts fit below the density available on a shallow ancestor. -/
theorem shallow_clock_inverse_cost_strong {K κ : ℝ}
    (hκ : 1 ≤ κ) (hK : 2304 ≤ K) (hκK : 3*κ ≤ K) :
    (K^20)⁻¹ ≤ κ⁻¹/16384 := by
  have hKp : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hκp : 0 < κ := zero_lt_one.trans_le hκ
  have hκK' : κ ≤ K := by linarith
  have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2304) hK 2
  norm_num at hsq
  have h19 : (16384:ℝ) ≤ K^19 :=
    (by linarith : (16384:ℝ) ≤ K^2).trans (pow_le_pow_right₀ hK1 (by norm_num))
  have h20 : 16384*κ ≤ K^20 := by
    calc
      _ ≤ 16384*K := mul_le_mul_of_nonneg_left hκK' (by norm_num)
      _ ≤ K^19*K := mul_le_mul_of_nonneg_right h19 hKp.le
      _ = _ := (pow_succ K 19).symm
  have h := (inv_le_inv₀ (pow_pos hKp 20) (by positivity : 0 < 16384*κ)).mpr h20
  simpa only [mul_inv_rev,div_eq_mul_inv] using h

theorem shallow_clock_inverse_cost_small {K κ : ℝ}
    (hκ : 1 ≤ κ) (hK : 2304 ≤ K) (hκK : 3*κ ≤ K) :
    (K^20)⁻¹ ≤ κ⁻¹/4096 := by
  have hKp : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hκp : 0 < κ := zero_lt_one.trans_le hκ
  have hκK' : κ ≤ K := by linarith
  have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2304) hK 2
  norm_num at hsq
  have h19 : (4096:ℝ) ≤ K^19 :=
    (by linarith : (4096:ℝ) ≤ K^2).trans (pow_le_pow_right₀ hK1 (by norm_num))
  have h20 : 4096*κ ≤ K^20 := by
    calc
      _ ≤ 4096*K := mul_le_mul_of_nonneg_left hκK' (by norm_num)
      _ ≤ K^19*K := mul_le_mul_of_nonneg_right h19 hKp.le
      _ = _ := (pow_succ K 19).symm
  have h := (inv_le_inv₀ (pow_pos hKp 20) (by positivity : 0 < 4096*κ)).mpr h20
  simpa only [mul_inv_rev,div_eq_mul_inv] using h

/-- The actual shallow clock preparation has three original-reference
costs. No repeated parent-gradient deletion is needed. -/
theorem shallow_parent_clock_source_cost_small {K κ census coarsening : ℝ} (R : ℕ)
    (hκ : 1 ≤ κ) (hK : 2304 ≤ K) (hκK : 3*κ ≤ K)
    (hC : 0 < census) (hD : 0 < coarsening) :
    ENNReal.ofReal ((census*coarsening^3)*parentClockCellRate K census coarsening)+
      ENNReal.ofReal (parentClockDurationRate K*(3*K^4+3)*(7:ℝ)^4)+
      ENNReal.ofReal (parentRenewalFloor K R)*(⌈K^12⌉₊:ENNReal)*ENNReal.ofReal (κ^2) ≤
        ENNReal.ofReal (κ⁻¹/512) := by
  have hKp : 0 < K := by linarith
  have hκp : 0 < κ := zero_lt_one.trans_le hκ
  have hcell : (census*coarsening^3)*parentClockCellRate K census coarsening=(K^20)⁻¹ := by
    unfold parentClockCellRate
    field_simp
  have hduration : parentClockDurationRate K*(3*K^4+3)*(7:ℝ)^4=(K^20)⁻¹ := by
    unfold parentClockDurationRate
    field_simp
  have hnative := ENNReal.ofReal_le_ofReal (shallow_clock_inverse_cost_small hκ hK hκK)
  rw [hcell,hduration]
  apply (add_le_add (add_le_add hnative hnative) (parent_state_cost_small R hκ hK hκK)).trans
  rw [←ENNReal.ofReal_add (by positivity) (by positivity),
    ←ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  nlinarith [inv_nonneg.mpr hκp.le]

/-- Several different earlier clock grids may be staged while all of
their whole-cell floors retain their own original laws. -/
theorem shallow_parent_clock_source_cost_strong {K κ census coarsening : ℝ} (R : ℕ)
    (hκ : 1 ≤ κ) (hK : 2304 ≤ K) (hκK : 3*κ ≤ K)
    (hC : 0 < census) (hD : 0 < coarsening) :
    ENNReal.ofReal ((census*coarsening^3)*parentClockCellRate K census coarsening)+
      ENNReal.ofReal (parentClockDurationRate K*(3*K^4+3)*(7:ℝ)^4)+
      ENNReal.ofReal (parentRenewalFloor K R)*(⌈K^12⌉₊:ENNReal)*ENNReal.ofReal (κ^2) ≤
        ENNReal.ofReal (κ⁻¹/4096) := by
  have hKp : 0 < K := by linarith
  have hκp : 0 < κ := zero_lt_one.trans_le hκ
  have hcell : (census*coarsening^3)*parentClockCellRate K census coarsening=(K^20)⁻¹ := by
    unfold parentClockCellRate
    field_simp
  have hduration : parentClockDurationRate K*(3*K^4+3)*(7:ℝ)^4=(K^20)⁻¹ := by
    unfold parentClockDurationRate
    field_simp
  have hnative := ENNReal.ofReal_le_ofReal (shallow_clock_inverse_cost_strong hκ hK hκK)
  rw [hcell,hduration]
  apply (add_le_add (add_le_add hnative hnative)
    ((parent_state_cost_le_inverse_twentieth R hκ hK hκK).trans hnative)).trans
  rw [←ENNReal.ofReal_add (by positivity) (by positivity),
    ←ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  nlinarith [inv_nonneg.mpr hκp.le]

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
