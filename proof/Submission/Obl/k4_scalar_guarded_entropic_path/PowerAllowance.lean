import Submission.Obl.k4_scalar_guarded_entropic_path.Guard

/-! Finite-stage power envelopes allow width and reference factors to be
chosen after the fixed-complexity original guard tolerance. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path

open Filter
open scoped Topology
open Submission.Obl.k4_scalar_linear_critical_extremizers

/-- The logarithmic exponent of the actual allowance has the prescribed
small finite-stage limit. -/
theorem power_allowance_loss_tendsto (N : ℕ → ℝ) (hN : Tendsto N atTop atTop)
    (v : ℝ) (n : ℕ) :
    Tendsto (fun j => Real.log ((N j ^ v * Real.log (N j)) ^ n) / Real.log (N j))
      atTop (nhds ((n : ℝ) * v)) := by
  have hloglog : Tendsto (fun j => Real.log (Real.log (N j)) / Real.log (N j))
      atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp (Real.tendsto_log_atTop.comp hN)
  have ht := ((tendsto_const_nhds (x := v)).add hloglog).const_mul (n : ℝ)
  simp only [add_zero] at ht
  apply ht.congr'
  filter_upwards [hN.eventually (eventually_gt_atTop 1)] with j hj
  have hpos : 0 < N j := zero_lt_one.trans hj
  have hlog : 0 < Real.log (N j) := Real.log_pos hj
  rw [Real.log_pow, Real.log_mul (Real.rpow_pos_of_pos hpos _).ne' hlog.ne',
    Real.log_rpow hpos]
  field_simp [hlog.ne']

/-- A strict finite-stage exponent budget absorbs the actual natural
power of both the path envelope and the original logarithm. -/
theorem eventually_power_allowance_le (N : ℕ → ℝ) (hN : Tendsto N atTop atTop)
    {v a : ℝ} (n : ℕ) (hbudget : (n : ℝ) * v < a) :
    ∀ᶠ j in atTop, (N j ^ v * Real.log (N j)) ^ n ≤ N j ^ a := by
  have hsmall := (power_allowance_loss_tendsto N hN v n).eventually
    (ge_mem_nhds hbudget)
  filter_upwards [hsmall, hN.eventually (eventually_gt_atTop 1)] with j hj hN1
  have hpos : 0 < N j := zero_lt_one.trans hN1
  have hlog : 0 < Real.log (N j) := Real.log_pos hN1
  have hactual : 0 < (N j ^ v * Real.log (N j)) ^ n := by positivity
  calc
    _ = N j ^ (Real.log ((N j ^ v * Real.log (N j)) ^ n) / Real.log (N j)) := by
      conv_rhs => rw [Real.rpow_def_of_pos hpos]
      rw [show Real.log (N j) *
          (Real.log ((N j ^ v * Real.log (N j)) ^ n) / Real.log (N j)) =
          Real.log ((N j ^ v * Real.log (N j)) ^ n) by field_simp,
        Real.exp_log hactual]
    _ ≤ N j ^ a := Real.rpow_le_rpow_of_exponent_le hN1.le hj

/-- Declare complexity first, then choose a positive power envelope as
small as requested while preserving the actual original-sample guard. -/
theorem exists_power_allowance_guard {p : Code} (hp : Split.Exact p)
    {κ gain θ : ℝ} (hκ : 0 < κ) (hgain : 0 < gain) (hθ : 0 < θ)
    (hknown : ∀ r h : ℝ, 0 ≤ r → r < p.L → Split.Known p r p.L h → κ * r - gain / 4 < h)
    (B n : ℕ) (hB : 1 ≤ B) (hn : 0 < n) :
    ∃ v : ℝ, 0 < v ∧ v < θ ∧
      ∀ᶠ m in atTop, ∀ r h : ℝ, 0 ≤ r → r < p.L → h ≤ κ * r - gain →
        ¬Split.Chart p B r p.L h
          (Real.log ((p.N m ^ v * Real.log (p.N m)) ^ n) / Real.log (p.N m)) false m := by
  obtain ⟨ε, hε, hguard⟩ := finite_guard_of_known_exclusion hp hκ hgain hknown B hB
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  let v : ℝ := min (θ / 2) (ε / (2 * (n : ℝ)))
  have hv : 0 < v := lt_min (half_pos hθ) (div_pos hε (by positivity))
  have hvθ : v < θ := (min_le_left _ _).trans_lt (by linarith)
  have hnv : (n : ℝ) * v < ε := by
    have hvle : v ≤ ε / (2 * (n : ℝ)) := min_le_right _ _
    have hm := mul_le_mul_of_nonneg_left hvle hnR.le
    have heq : (n : ℝ) * (ε / (2 * (n : ℝ))) = ε / 2 := by field_simp
    rw [heq] at hm
    linarith
  have hsmall := (power_allowance_loss_tendsto p.N hp.1.2.1 v n).eventually (ge_mem_nhds hnv)
  refine ⟨v, hv, hvθ, ?_⟩
  filter_upwards [hguard, hsmall] with m hm hs r h hr hrL hh hc
  exact hm r h hr hrL hh (Chart.relax_false (exact_N_ge_one hp m) le_rfl le_rfl hs hc)

end Submission.Obl.k4_scalar_guarded_entropic_path
