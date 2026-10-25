-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.ParentRenewalBudgets, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/ParentRenewalBudgets.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1046 (branch x0943), commit 1fcc75a78b90aa1b479052c83612b68563af73b6,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/ParentRenewalBudgets.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.CoreRetentionNumerics
import Submission.Lib.K4NativePreparationNumerics.NativeOutputBudgets

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open scoped ENNReal

noncomputable section

/-- A native polynomial floor pays the parent-gradient and state renewals. -/
def parentRenewalFloor (K : ℝ) (R : ℕ) : ℝ := (K^(3*R+60))⁻¹

theorem parentRenewalFloor_pos {K : ℝ} (hK : 0 < K) (R : ℕ) :
    0 < parentRenewalFloor K R := by unfold parentRenewalFloor; positivity

theorem parentRenewalFloor_le_one {K : ℝ} (hK : 1 ≤ K) (R : ℕ) :
    parentRenewalFloor K R ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hK)

/-- All registered-depth gradient cuts cost a small fixed fraction of
original mass. Geometry and grid envelopes do not enter this inequality. -/
theorem parent_gradient_real_cost_small {K κ : ℝ} (n R : ℕ)
    (hκ : 1 ≤ κ) (hK : 2304 ≤ K) (hκK : 3*κ ≤ K) (hn : (n:ℝ) ≤ K) :
    (n:ℝ)*(4*K^(3*R+28)*κ^2)*
      (parentRenewalFloor K R*(K^R)⁻¹+27*(parentRenewalFloor K R*κ^2)) ≤ κ⁻¹/32768 := by
  have hKp : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hκp : 0 < κ := zero_lt_one.trans_le hκ
  have hκK' : κ ≤ K := by linarith
  have hparens : (K^R)⁻¹+27*κ^2 ≤ 28*K^2 := by
    have hinv : (K^R)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hK1)
    have hκ2 := pow_le_pow_left₀ hκp.le hκK' 2
    have hK2 : 1 ≤ K^2 := one_le_pow₀ hK1
    linarith
  have hnumerator : (n:ℝ)*(4*K^(3*R+28)*κ^2)*((K^R)⁻¹+27*κ^2) ≤
      112*K^(3*R+33) := by
    calc
      _ ≤ (K*(4*K^(3*R+28)*K^2))*(28*K^2) := by
        apply mul_le_mul _ hparens (by positivity) (by positivity)
        gcongr
      _ = _ := by rw [show 3*R+33=(3*R+28)+5 by omega,pow_add]; ring
  have hcost : (n:ℝ)*(4*K^(3*R+28)*κ^2)*
      (parentRenewalFloor K R*(K^R)⁻¹+27*(parentRenewalFloor K R*κ^2)) ≤ 112/K^27 := by
    calc
      _ = ((n:ℝ)*(4*K^(3*R+28)*κ^2)*((K^R)⁻¹+27*κ^2))/K^(3*R+60) := by
        unfold parentRenewalFloor
        ring
      _ ≤ (112*K^(3*R+33))/K^(3*R+60) :=
        div_le_div_of_nonneg_right hnumerator (pow_nonneg hKp.le _)
      _ = _ := by
        rw [show 3*R+60=(3*R+33)+27 by omega,pow_add]
        field_simp
        simp only [pow_add]
        ring
  have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2304) hK 2
  norm_num at hsq
  have h26 : (112*32768:ℝ) ≤ K^26 :=
    (by linarith : (112*32768:ℝ) ≤ K^2).trans (pow_le_pow_right₀ hK1 (by norm_num))
  have h27 : (112*32768:ℝ)*κ ≤ K^27 := by
    calc
      _ ≤ (112*32768:ℝ)*K := mul_le_mul_of_nonneg_left hκK' (by norm_num)
      _ ≤ K^26*K := mul_le_mul_of_nonneg_right h26 hKp.le
      _ = _ := (pow_succ K 26).symm
  have hlast : (112:ℝ)/K^27 ≤ 1/(32768*κ) :=
    (div_le_div_iff₀ (pow_pos hKp 27) (by positivity : 0 < 32768*κ)).mpr
      (by simpa only [one_mul,mul_assoc] using h27)
  apply hcost.trans
  simpa only [div_eq_mul_inv,mul_inv_rev,one_mul] using hlast

/-- The same bound in the literal original-reference gradient budget. -/
theorem parent_gradient_cost_small {K κ : ℝ} (n R : ℕ)
    (hκ : 1 ≤ κ) (hK : 2304 ≤ K) (hκK : 3*κ ≤ K) (hn : (n:ℝ) ≤ K) :
    (n:ENNReal)*(ENNReal.ofReal (4*K^(3*R+28)*κ^2)*
      (ENNReal.ofReal (parentRenewalFloor K R*(K^R)⁻¹)+
        27*(ENNReal.ofReal (parentRenewalFloor K R)*ENNReal.ofReal (κ^2)))) ≤
      ENNReal.ofReal (κ⁻¹/32768) := by
  have hKp : 0 < K := by linarith
  have hfloor := parentRenewalFloor_pos hKp R
  calc
    _ = ENNReal.ofReal ((n:ℝ)*(4*K^(3*R+28)*κ^2)*
        (parentRenewalFloor K R*(K^R)⁻¹+27*(parentRenewalFloor K R*κ^2))) := by
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (n:ℝ)*(4*K^(3*R+28)*κ^2)),
        ENNReal.ofReal_mul (Nat.cast_nonneg n),ENNReal.ofReal_natCast,
        ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 27),
        ENNReal.ofReal_mul hfloor.le,ENNReal.ofReal_mul hfloor.le] <;> norm_num <;> ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (parent_gradient_real_cost_small n R hκ hK hκK hn)

/-- The actual ceiling of the physical menu size is paid by the same
native reference floor, with no state-count hypothesis. -/
theorem parent_state_cost_le_inverse_twentieth {K κ : ℝ} (R : ℕ)
    (hκ : 1 ≤ κ) (hK : 2304 ≤ K) (hκK : 3*κ ≤ K) :
    ENNReal.ofReal (parentRenewalFloor K R)*(⌈K^12⌉₊:ENNReal)*ENNReal.ofReal (κ^2) ≤
      ENNReal.ofReal ((K^20)⁻¹) := by
  have hKp : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hκp : 0 < κ := zero_lt_one.trans_le hκ
  have hκK' : κ ≤ K := by linarith
  have hfloor := parentRenewalFloor_pos hKp R
  have hceil : (⌈K^12⌉₊:ℝ) ≤ K^13 := by
    calc
      _ ≤ K^12+1 := (Nat.ceil_lt_add_one (pow_nonneg hKp.le 12)).le
      _ ≤ 2*K^12 := by linarith [one_le_pow₀ hK1 (n := 12)]
      _ ≤ K*K^12 := mul_le_mul_of_nonneg_right (by linarith : 2 ≤ K) (pow_nonneg hKp.le 12)
      _ = _ := (pow_succ' K 12).symm
  have hnum : (⌈K^12⌉₊:ℝ)*κ^2*K^20 ≤ K^(3*R+60) := by
    calc
      _ ≤ K^13*K^2*K^20 := by gcongr
      _ = K^35 := by ring
      _ ≤ _ := pow_le_pow_right₀ hK1 (by omega)
  have hreal : parentRenewalFloor K R*(⌈K^12⌉₊:ℝ)*κ^2 ≤ (K^20)⁻¹ := by
    have hh : ((⌈K^12⌉₊:ℝ)*κ^2)/K^(3*R+60) ≤ 1/K^20 :=
      (div_le_div_iff₀ (pow_pos hKp _) (pow_pos hKp _)).mpr (by simpa only [one_mul] using hnum)
    simpa only [parentRenewalFloor,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul,mul_one] using hh
  calc
    _ = ENNReal.ofReal (parentRenewalFloor K R*(⌈K^12⌉₊:ℝ)*κ^2) := by
      rw [ENNReal.ofReal_mul (mul_nonneg hfloor.le (Nat.cast_nonneg _)),
        ENNReal.ofReal_mul hfloor.le,ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((K^20)⁻¹) := ENNReal.ofReal_le_ofReal hreal

/-- A fixed fraction of the original density pays the same state renewal. -/
theorem parent_state_cost_small {K κ : ℝ} (R : ℕ)
    (hκ : 1 ≤ κ) (hK : 2304 ≤ K) (hκK : 3*κ ≤ K) :
    ENNReal.ofReal (parentRenewalFloor K R)*(⌈K^12⌉₊:ENNReal)*ENNReal.ofReal (κ^2) ≤
      ENNReal.ofReal (κ⁻¹/1024) :=
  (parent_state_cost_le_inverse_twentieth R hκ hK hκK).trans
    (ENNReal.ofReal_le_ofReal (original_core_loss_small hκ hK hκK))

/-- A reference floor which is a native polynomial still inherits a small
strip ratio from the refined original broad fraction. -/
theorem parent_renewal_fraction_small {K Λ : ℝ} (R : ℕ)
    (hK : 0 < K) (hΛ : 0 < Λ) (hbudget : K^(3*R+60) ≤ Λ) :
    (ENNReal.ofReal (parentRenewalFloor K R))⁻¹*
      ENNReal.ofReal (8*(2*(100000*Λ)⁻¹)) ≤ (1/5000:ENNReal) := by
  have hfloor := parentRenewalFloor_pos hK R
  have hratio : K^(3*R+60)/Λ ≤ 1 := (div_le_one hΛ).mpr hbudget
  have hreal : (8*(2*(100000*Λ)⁻¹))/parentRenewalFloor K R ≤ (1/5000:ℝ) := by
    have heq : (8*(2*(100000*Λ)⁻¹))/parentRenewalFloor K R=
        (16/100000:ℝ)*(K^(3*R+60)/Λ) := by
      unfold parentRenewalFloor
      field_simp <;> norm_num
    rw [heq]
    nlinarith
  calc
    _ = ENNReal.ofReal ((8*(2*(100000*Λ)⁻¹))/parentRenewalFloor K R) := by
      rw [ENNReal.ofReal_div_of_pos hfloor]
      simp only [div_eq_mul_inv,mul_comm]
    _ ≤ ENNReal.ofReal (1/5000:ℝ) := ENNReal.ofReal_le_ofReal hreal
    _ = _ := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 5000)]
      norm_num

/-- Calibrated cell floors spend only an inverse native power, even when
the census and dyadic coarsening envelopes are larger. -/
def parentClockCellRate (K census coarsening : ℝ) : ℝ :=
  (K^20)⁻¹/(census*coarsening^3)

/-- Earlier coarse-duration pruning spends the same inverse native power. -/
def parentClockDurationRate (K : ℝ) : ℝ :=
  (K^20)⁻¹/((3*K^4+3)*(7:ℝ)^4)

theorem parentClockCellRate_pos {K census coarsening : ℝ}
    (hK : 0 < K) (hC : 0 < census) (hD : 0 < coarsening) :
    0 < parentClockCellRate K census coarsening := by
  unfold parentClockCellRate
  positivity

theorem parentClockDurationRate_pos {K : ℝ} (hK : 0 < K) :
    0 < parentClockDurationRate K := by
  unfold parentClockDurationRate
  positivity

/-- The actual four original-reference costs in clock preparation fit
below half the dense original source floor. -/
theorem parent_clock_source_cost_small {K κ census coarsening : ℝ} (R : ℕ)
    (hκ : 1 ≤ κ) (hK : 2304 ≤ K) (hκK : 3*κ ≤ K)
    (hC : 0 < census) (hD : 0 < coarsening) :
    ENNReal.ofReal ((census*coarsening^3)*parentClockCellRate K census coarsening)+
      ENNReal.ofReal (parentClockDurationRate K*(3*K^4+3)*(7:ℝ)^4)+
      ENNReal.ofReal (4*K^(3*R+28)*κ^2)*
        (ENNReal.ofReal (parentRenewalFloor K R*(K^R)⁻¹)+
          27*(ENNReal.ofReal (parentRenewalFloor K R)*ENNReal.ofReal (κ^2)))+
      ENNReal.ofReal (parentRenewalFloor K R)*(⌈K^12⌉₊:ENNReal)*ENNReal.ofReal (κ^2) ≤
        ENNReal.ofReal (κ⁻¹/256) := by
  have hKp : 0 < K := by linarith
  have hκp : 0 < κ := zero_lt_one.trans_le hκ
  have hcell : (census*coarsening^3)*parentClockCellRate K census coarsening=(K^20)⁻¹ := by
    unfold parentClockCellRate
    field_simp
  have hduration : parentClockDurationRate K*(3*K^4+3)*(7:ℝ)^4=(K^20)⁻¹ := by
    unfold parentClockDurationRate
    field_simp
  have hnative : ENNReal.ofReal ((K^20)⁻¹) ≤ ENNReal.ofReal (κ⁻¹/1024) :=
    ENNReal.ofReal_le_ofReal (original_core_loss_small hκ hK hκK)
  have hgrad : ENNReal.ofReal (4*K^(3*R+28)*κ^2)*
      (ENNReal.ofReal (parentRenewalFloor K R*(K^R)⁻¹)+
        27*(ENNReal.ofReal (parentRenewalFloor K R)*ENNReal.ofReal (κ^2))) ≤
        ENNReal.ofReal (κ⁻¹/1024) := by
    have hh := parent_gradient_cost_small 1 R hκ hK hκK (by norm_num; linarith)
    simp only [Nat.cast_one,one_mul] at hh
    apply hh.trans
    apply ENNReal.ofReal_le_ofReal
    nlinarith [inv_nonneg.mpr hκp.le]
  rw [hcell,hduration]
  apply (add_le_add (add_le_add (add_le_add hnative hnative) hgrad)
    (parent_state_cost_small R hκ hK hκK)).trans
  apply le_of_eq
  rw [←ENNReal.ofReal_add (by positivity) (by positivity),
    ←ENNReal.ofReal_add (by positivity) (by positivity),
    ←ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
