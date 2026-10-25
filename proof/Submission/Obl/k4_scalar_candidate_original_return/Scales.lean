import Submission.Obl.k4_scalar_candidate_original_return.Prepared
import Submission.Lib.K4MeshListRecovery.MassDiagonal
import Submission.Lib.K4MeshListRecovery.ComplexityGuard
import Submission.Obl.k4_discrete_of_terminal_charts.Horizon

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

open Filter
open scoped Topology

/-- Numerical control in the actual original sample and the tangent depth units. -/
structure ScaleControl where
  original : ℕ → ℝ
  unit : ℕ → ℝ
  factor : ℕ → ℝ
  original_ge_two : ∀ k, 2 ≤ original k
  unit_pos : ∀ k, 0 < unit k
  unit_le_one : ∀ k, unit k ≤ 1
  factor_ge_two : ∀ k, 2 ≤ factor k
  tangent_tends : Tendsto (fun k => original k ^ unit k) atTop atTop
  allowance_subpower : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
    (factor k * Real.log (original k)) ^ (k + 1) ≤ (original k ^ unit k) ^ ε

namespace ScaleControl

noncomputable def tangent (a : ScaleControl) (k : ℕ) : ℝ := a.original k ^ a.unit k
noncomputable def allowance (a : ScaleControl) (k : ℕ) : ℝ :=
  (a.factor k * Real.log (a.original k)) ^ (k + 1)
noncomputable def loss (a : ScaleControl) (k : ℕ) : ℝ :=
  Real.log (a.allowance k) / Real.log (a.original k)

lemma original_pos (a : ScaleControl) (k : ℕ) : 0 < a.original k := by
  linarith [a.original_ge_two k]

lemma tangent_pos (a : ScaleControl) (k : ℕ) : 0 < a.tangent k :=
  Real.rpow_pos_of_pos (a.original_pos k) _

lemma log_original_pos (a : ScaleControl) (k : ℕ) : 0 < Real.log (a.original k) :=
  Real.log_pos (by linarith [a.original_ge_two k])

lemma tangent_le_original (a : ScaleControl) (k : ℕ) : a.tangent k ≤ a.original k := by
  have h := Real.rpow_le_rpow_of_exponent_le
    (show 1 ≤ a.original k by linarith [a.original_ge_two k]) (a.unit_le_one k)
  simpa only [tangent, Real.rpow_one] using h

lemma original_tends (a : ScaleControl) : Tendsto a.original atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [tendsto_atTop.1 a.tangent_tends b] with k hk
  exact hk.trans (a.tangent_le_original k)

lemma factor_log_ge_one (a : ScaleControl) (k : ℕ) :
    1 ≤ a.factor k * Real.log (a.original k) := by
  have hlog : (1 / 2 : ℝ) ≤ Real.log (a.original k) :=
    (show (1 / 2 : ℝ) ≤ Real.log 2 by linarith [Real.log_two_gt_d9]).trans
      (Real.log_le_log (by norm_num) (a.original_ge_two k))
  nlinarith [a.factor_ge_two k]

lemma allowance_ge_one (a : ScaleControl) (k : ℕ) : 1 ≤ a.allowance k :=
  one_le_pow₀ (a.factor_log_ge_one k)

lemma allowance_pos (a : ScaleControl) (k : ℕ) : 0 < a.allowance k :=
  lt_of_lt_of_le zero_lt_one (a.allowance_ge_one k)

lemma original_rpow_loss (a : ScaleControl) (k : ℕ) :
    a.original k ^ a.loss k = a.allowance k := by
  rw [Real.rpow_def_of_pos (a.original_pos k), loss]
  rw [mul_div_cancel₀ _ (a.log_original_pos k).ne']
  exact Real.exp_log (a.allowance_pos k)

lemma original_rpow_neg_loss (a : ScaleControl) (k : ℕ) :
    a.original k ^ (-a.loss k) = (a.allowance k)⁻¹ := by
  rw [Real.rpow_neg (a.original_pos k).le, a.original_rpow_loss]

lemma original_rpow_log_factor (a : ScaleControl) (k : ℕ) :
    a.original k ^ (Real.log (a.factor k) / Real.log (a.original k)) = a.factor k := by
  rw [Real.rpow_def_of_pos (a.original_pos k)]
  rw [mul_div_cancel₀ _ (a.log_original_pos k).ne']
  exact Real.exp_log (by linarith [a.factor_ge_two k])

lemma tangent_rpow (a : ScaleControl) (k : ℕ) (r : ℝ) :
    a.tangent k ^ r = a.original k ^ (a.unit k * r) := by
  exact (Real.rpow_mul (a.original_pos k).le _ _).symm

lemma loss_nonneg (a : ScaleControl) (k : ℕ) : 0 ≤ a.loss k :=
  div_nonneg (Real.log_nonneg (a.allowance_ge_one k)) (a.log_original_pos k).le

/-- The displayed tolerance is negligible in tangent exponent units. -/
lemma loss_div_unit_tends (a : ScaleControl) :
    Tendsto (fun k => a.loss k / a.unit k) atTop (𝓝 0) := by
  have h := Submission.Lib.K4MeshListRecovery.subpower_log_ratio_tendsto_zero
    a.tangent a.allowance a.tangent_tends a.allowance_ge_one a.allowance_subpower
  convert h using 1
  funext k
  rw [tangent, Real.log_rpow (a.original_pos k)]
  dsimp [loss]
  ring

lemma allowance_subpower_original (a : ScaleControl) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, a.allowance k ≤ a.original k ^ ε := by
  filter_upwards [a.allowance_subpower ε hε] with k hk
  exact hk.trans (Real.rpow_le_rpow (a.tangent_pos k).le
    (a.tangent_le_original k) hε.le)

/-- Every fixed power of the actual path factor and logarithm fits the predeclared allowance. -/
lemma eventually_fixed_power_le_allowance (a : ScaleControl) (C : ℝ) (p : ℕ) :
    ∀ᶠ k in atTop, C * (a.factor k * Real.log (a.original k)) ^ p ≤ a.allowance k := by
  obtain ⟨c, hc⟩ := exists_nat_gt C
  have hc' : C ≤ (2 : ℝ) ^ c :=
    (hc.trans (by exact_mod_cast c.lt_two_pow_self)).le
  filter_upwards [a.original_tends.eventually (eventually_ge_atTop (Real.exp 1)),
    eventually_ge_atTop (c + p)] with k hNk hkp
  have hlog : 1 ≤ Real.log (a.original k) := by
    have h := Real.log_le_log (Real.exp_pos 1) hNk
    simpa only [Real.log_exp] using h
  have hbase : 2 ≤ a.factor k * Real.log (a.original k) := by
    nlinarith [a.factor_ge_two k]
  calc
    C * (a.factor k * Real.log (a.original k)) ^ p ≤
        (2 : ℝ) ^ c * (a.factor k * Real.log (a.original k)) ^ p := by
      gcongr
    _ ≤ (a.factor k * Real.log (a.original k)) ^ c *
        (a.factor k * Real.log (a.original k)) ^ p := by
      gcongr
    _ = (a.factor k * Real.log (a.original k)) ^ (c + p) := (pow_add _ _ _).symm
    _ ≤ a.allowance k := pow_le_pow_right₀ (by linarith) (by omega)

lemma eventually_factor_power_le_allowance (a : ScaleControl) (C : ℝ) (p : ℕ) :
    ∀ᶠ k in atTop, C * a.factor k ^ p ≤ a.allowance k := by
  filter_upwards [a.eventually_fixed_power_le_allowance (max C 0) p,
    a.original_tends.eventually (eventually_ge_atTop (Real.exp 1))] with k hk hNk
  have hlog : 1 ≤ Real.log (a.original k) := by
    have h := Real.log_le_log (Real.exp_pos 1) hNk
    simpa only [Real.log_exp] using h
  apply le_trans ?_ hk
  apply mul_le_mul (le_max_left C 0) ?_
    (pow_nonneg (by linarith [a.factor_ge_two k]) _) (le_max_right C 0)
  apply pow_le_pow_left₀ (by linarith [a.factor_ge_two k])
  nlinarith [a.factor_ge_two k]

/-- Original inverse-resolution errors remain negligible after any fixed power of the allowance. -/
lemma allowance_pow_original_error_tends (a : ScaleControl) (p : ℕ) :
    Tendsto (fun k => a.allowance k ^ p / a.original k) atTop (𝓝 0) := by
  have hsub := Submission.Obl.k4_discrete_of_terminal_charts.subpower_pow
    (fun k => show 1 ≤ a.original k by linarith [a.original_ge_two k])
    (fun k => (a.allowance_ge_one k).trans' zero_le_one)
    a.allowance_subpower_original p
  have h := Submission.Lib.K4MeshListRecovery.subpower_log_mass_error_tendsto_zero
    a.original (fun k => a.allowance k ^ p) a.original_tends
    (fun k => one_le_pow₀ (a.allowance_ge_one k)) hsub
  apply squeeze_zero' ?_ ?_ h
  · exact Eventually.of_forall (fun k => div_nonneg (pow_nonneg (a.allowance_pos k).le _) (a.original_pos k).le)
  · filter_upwards [a.original_tends.eventually (eventually_ge_atTop (Real.exp 1))] with k hNk
    have hlog : 1 ≤ Real.log (a.original k) := by
      have hlog' := Real.log_le_log (Real.exp_pos 1) hNk
      simpa only [Real.log_exp] using hlog'
    apply div_le_div_of_nonneg_right ?_ (a.original_pos k).le
    nlinarith [show 0 ≤ a.allowance k ^ p from pow_nonneg (a.allowance_pos k).le _]

end ScaleControl

end Submission.Obl.k4_scalar_candidate_original_return
