import Mathlib

/-!
Adapted from: here:o064

The finite-stage mass and slack requirements of the guarded critical-path
diagonal.  The path factors are taken from the unchanged exact sequence.
-/

namespace Submission.Lib.K4MeshListRecovery

open Filter
open scoped Topology

/-- A subpower path factor has vanishing logarithmic exponent. -/
theorem subpower_log_ratio_tendsto_zero
    (N K : ℕ → ℝ) (hN : Tendsto N atTop atTop) (hK : ∀ j, 1 ≤ K j)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, K j ≤ N j ^ ε) :
    Tendsto (fun j => Real.log (K j) / Real.log (N j)) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hN.eventually (eventually_gt_atTop 1),
    hsub (ε / 2) (by positivity)] with j hNj hKj
  have hlogN : 0 < Real.log (N j) := Real.log_pos hNj
  have hlogK : 0 ≤ Real.log (K j) := Real.log_nonneg (hK j)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hlogK hlogN.le)]
  have hlog := Real.log_le_log (by linarith [hK j]) hKj
  rw [Real.log_rpow (by linarith : 0 < N j)] at hlog
  exact ((div_le_iff₀ hlogN).mpr hlog).trans_lt (by linarith)

/-- The inverse-resolution error is negligible relative to original path
mass, even after multiplication by the actual path factor and a logarithm. -/
theorem subpower_log_mass_error_tendsto_zero
    (N K : ℕ → ℝ) (hN : Tendsto N atTop atTop) (hK : ∀ j, 1 ≤ K j)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, K j ≤ N j ^ ε) :
    Tendsto (fun j => K j * Real.log (N j) / N j) atTop (𝓝 0) := by
  have hsmall := (isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ))
    (by norm_num)).tendsto_div_nhds_zero.comp hN
  apply squeeze_zero' ?_ ?_ hsmall
  · filter_upwards [hN.eventually (eventually_gt_atTop 1)] with j hj
    exact div_nonneg (mul_nonneg (by linarith [hK j]) (Real.log_nonneg hj.le))
      (by linarith)
  · filter_upwards [hN.eventually (eventually_gt_atTop 1),
      hsub (1 / 2) (by norm_num)] with j hj hKj
    have hpos : 0 < N j := by linarith
    have hrpos : 0 < N j ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hpos _
    have hsquare : (N j ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = N j := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
      norm_num
    calc
      K j * Real.log (N j) / N j ≤
          N j ^ (1 / 2 : ℝ) * Real.log (N j) / N j :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hKj (Real.log_nonneg hj.le)) hpos.le
      _ = Real.log (N j) / N j ^ (1 / 2 : ℝ) := by
        apply (div_eq_div_iff hpos.ne' hrpos.ne').mpr
        calc
          _ = Real.log (N j) * (N j ^ (1 / 2 : ℝ)) ^ (2 : ℕ) := by ring
          _ = _ := by rw [hsquare]

/-- Any fixed power of actual path factors and logarithms has negligible
slack exponent, at every fixed positive tangent scale. -/
theorem subpower_path_slack_tendsto_zero
    (N K : ℕ → ℝ) (hN : Tendsto N atTop atTop) (hK : ∀ j, 1 ≤ K j)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, K j ≤ N j ^ ε)
    (p : ℕ) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun j => Real.log ((K j * Real.log (N j)) ^ p) /
      (ε * Real.log (N j))) atTop (𝓝 0) := by
  have hloglog : Tendsto (fun j => Real.log (Real.log (N j)) / Real.log (N j))
      atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp (Real.tendsto_log_atTop.comp hN)
  have ht := (tendsto_const_nhds (x := (p : ℝ) / ε)).mul
    ((subpower_log_ratio_tendsto_zero N K hN hK hsub).add hloglog)
  simp only [zero_add, mul_zero] at ht
  apply ht.congr'
  filter_upwards [hN.eventually (eventually_gt_atTop 1)] with j hj
  have hlog : 0 < Real.log (N j) := Real.log_pos hj
  rw [Real.log_pow, Real.log_mul (by linarith [hK j]) hlog.ne']
  field_simp [hε.ne', hlog.ne']

/-- The guarded diagonal's three displayed finite-stage requirements hold
simultaneously, before increasing the stage. -/
theorem eventually_path_diagonal_requirements
    (N K : ℕ → ℝ) (hN : Tendsto N atTop atTop) (hK : ∀ j, 1 ≤ K j)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, K j ≤ N j ^ ε)
    (G : ℝ) (p : ℕ) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ j in atTop,
      G / Real.log (N j) ≤ δ ∧ K j * Real.log (N j) / N j ≤ δ ∧
      Real.log ((K j * Real.log (N j)) ^ p) / (ε * Real.log (N j)) ≤ δ := by
  have hG := (tendsto_const_nhds (x := G)).div_atTop (Real.tendsto_log_atTop.comp hN)
  filter_upwards [hG.eventually (Iio_mem_nhds hδ),
    (subpower_log_mass_error_tendsto_zero N K hN hK hsub).eventually (Iio_mem_nhds hδ),
    (subpower_path_slack_tendsto_zero N K hN hK hsub p ε hε).eventually (Iio_mem_nhds hδ)]
    with j hjG hjmass hjslack
  exact ⟨hjG.le, hjmass.le, hjslack.le⟩

end Submission.Lib.K4MeshListRecovery
