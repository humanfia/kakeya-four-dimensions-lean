import Submission.Obl.k4_scalar_candidate_original_return.SplitInterfaces

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

open Filter
open scoped Topology

noncomputable section

/-- The actual displayed original exponent needed by a fixed path budget. -/
def recoveryExponent (a : PreparedData) (C : ℝ) (p k : ℕ) : ℝ :=
  Real.log (C * a.H k ^ p) / Real.log (a.original k)

namespace EncodingCore

variable {a : PreparedData} (ha : EncodingCore a)
include ha

lemma original_ge_two (k : ℕ) : 2 ≤ a.original k := (ha.1 k).1.1 (a.sm k)

lemma original_pos (k : ℕ) : 0 < a.original k := by linarith [ha.original_ge_two k]

lemma bounds (k : ℕ) : 0 < a.sc k ∧ a.sc k ≤ 1 ∧ 2 ≤ a.H k ∧ 1 ≤ a.rM k ∧
    M (a.p k) ≤ a.rM k ∧ D (a.p k) ≤ a.rM k ∧
    L (a.p k) ≤ (a.rM k : ℝ) ∧ K (a.p k) (a.sm k) ≤ a.H k := ha.2.1 k

lemma tangent_le_original (k : ℕ) : a.tangent k ≤ a.original k := by
  simpa only [PreparedData.tangent, Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le
      (by linarith [ha.original_ge_two k] : 1 ≤ a.original k) (ha.bounds k).2.1

lemma original_tends : Tendsto a.original atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [tendsto_atTop.1 ha.2.2.1 b] with k hk
  exact hk.trans (ha.tangent_le_original k)

lemma tangent_rpow (k : ℕ) (r : ℝ) :
    a.tangent k ^ r = a.original k ^ (a.sc k * r) :=
  (Real.rpow_mul (ha.original_pos k).le _ _).symm

lemma factor_subpower_original (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, a.H k ≤ a.original k ^ ε := by
  filter_upwards [ha.2.2.2.2.1 ε hε] with k hk
  exact hk.trans (Real.rpow_le_rpow (Real.rpow_pos_of_pos (ha.original_pos k) _).le
    (ha.tangent_le_original k) hε.le)

lemma original_error_le_floor {C : ℝ} (hC : 0 < C) (p : ℕ) :
    ∀ᶠ k in atTop, (a.original k)⁻¹ ≤ (2 * C * a.H k ^ p)⁻¹ := by
  have hsub := k4_discrete_of_terminal_charts.subpower_pow
    (fun k => by linarith [ha.original_ge_two k] : ∀ k, 1 ≤ a.original k)
    (fun k => by linarith [(ha.bounds k).2.2.1] : ∀ k, 0 ≤ a.H k)
    ha.factor_subpower_original p
  have ht := Submission.Lib.K4MeshListRecovery.subpower_log_mass_error_tendsto_zero
    a.original (fun k => a.H k ^ p) ha.original_tends
    (fun k => one_le_pow₀ (by linarith [(ha.bounds k).2.2.1])) hsub
  have hs : ∀ᶠ k in atTop, a.H k ^ p * Real.log (a.original k) / a.original k < (2 * C)⁻¹ :=
    (tendsto_order.1 ht).2 _ (by positivity)
  filter_upwards [hs, ha.original_tends.eventually (eventually_ge_atTop (Real.exp 1))]
    with k hk hNk
  have hlog : 1 ≤ Real.log (a.original k) := by
    have h := Real.log_le_log (Real.exp_pos 1) hNk
    simpa only [Real.log_exp] using h
  have hpow : 0 < a.H k ^ p := pow_pos (by linarith [(ha.bounds k).2.2.1]) _
  have hratio : a.H k ^ p / a.original k < (2 * C)⁻¹ := by
    apply lt_of_le_of_lt _ hk
    apply div_le_div_of_nonneg_right _ (ha.original_pos k).le
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hlog hpow.le
  have hbound : 2 * C * a.H k ^ p ≤ a.original k := by
    have hh := (div_lt_iff₀ (ha.original_pos k)).mp hratio
    have hh' := mul_le_mul_of_nonneg_left hh.le (show 0 ≤ 2 * C by positivity)
    simpa only [← mul_assoc, mul_inv_cancel₀ (show 2 * C ≠ 0 by positivity), one_mul] using hh'
  simpa only [one_div] using one_div_le_one_div_of_le (by positivity) hbound

lemma rpow_recoveryExponent {C : ℝ} (hC : 0 < C) (p k : ℕ) :
    a.original k ^ recoveryExponent a C p k = C * a.H k ^ p := by
  rw [Real.rpow_def_of_pos (ha.original_pos k), recoveryExponent,
    mul_div_cancel₀ _ (Real.log_pos (by linarith [ha.original_ge_two k])).ne']
  have hH : 0 < a.H k := by linarith [(ha.bounds k).2.2.1]
  exact Real.exp_log (by positivity)

lemma neg_rpow_recoveryExponent {C : ℝ} (hC : 0 < C) (p k : ℕ) :
    a.original k ^ (-recoveryExponent a C p k) = (C * a.H k ^ p)⁻¹ := by
  rw [Real.rpow_neg (ha.original_pos k).le, ha.rpow_recoveryExponent hC]

lemma old_slack_le_recoveryExponent {C : ℝ} (hC : 1 ≤ C)
    {p : ℕ} (hp : 1 ≤ p) (k : ℕ) :
    Real.log (a.H k) / Real.log (a.original k) ≤ recoveryExponent a C p k := by
  have hH : 1 ≤ a.H k := by linarith [(ha.bounds k).2.2.1]
  have hpow : a.H k ≤ a.H k ^ p := by
    simpa only [pow_one] using pow_le_pow_right₀ hH hp
  apply div_le_div_of_nonneg_right _ (Real.log_pos (by linarith [ha.original_ge_two k])).le
  apply Real.log_le_log (by linarith)
  exact hpow.trans (by simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hC (pow_nonneg (by linarith) p))

lemma recovery_budget {C : ℝ} (hC : 0 < C) (p : ℕ) :
    ∀ᶠ k in atTop, a.original k ^ recoveryExponent a C p k ≤
      C * (a.H k * Real.log (a.original k)) ^ p := by
  filter_upwards [ha.original_tends.eventually (eventually_ge_atTop (Real.exp 1))] with k hk
  rw [ha.rpow_recoveryExponent hC]
  have hlog : 1 ≤ Real.log (a.original k) := by
    have h := Real.log_le_log (Real.exp_pos 1) hk
    simpa only [Real.log_exp] using h
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply pow_le_pow_left₀ (by linarith [(ha.bounds k).2.2.1])
  have hH : 0 ≤ a.H k := by linarith [(ha.bounds k).2.2.1]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hlog hH

end EncodingCore

end

end Submission.Obl.k4_scalar_candidate_original_return
