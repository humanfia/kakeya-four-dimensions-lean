-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.StripPowerBudgets, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/StripPowerBudgets.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/StripPowerBudgets.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/StripPowerBudgets.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/StripPowerBudgets.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_native_finite_terminal_atlas_lift.LiftBounds
import Submission.Obl.k4_profile_density_bounds.Asymptotics

/-! Uniform power budgets for strip refinements. Polynomial exponents are
fixed independently of the requested subpower slack. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open Submission.Obl.k4_native_finite_terminal_atlas_lift
open Filter

theorem strip_slack_envelope {K E C count r : ℝ}
    (hK : 1 ≤ K) (hE : 1 ≤ E) (hKE : K ≤ E)
    (hC : 0 ≤ C) (hCE : C ≤ 5 * E) (hcount : 0 ≤ count)
    (hcountE : count ≤ 3 * E ^ 2) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    K * (1 + C) ≤ 6 * E ^ 2 ∧
    K * (2 * (K + (1 + C) * r)) ≤ 14 * E ^ 2 ∧
    K * (count * (2 * C + 1)) ≤ 33 * E ^ 4 := by
  have hK0 : 0 ≤ K := by linarith
  have hE0 : 0 ≤ E := by linarith
  have hC' : 1 + C ≤ 6 * E := by linarith
  have hCr : (1 + C) * r ≤ 6 * E :=
    (mul_le_mul_of_nonneg_left hr1 (by linarith)).trans (by simpa using hC')
  have hClist : 2 * C + 1 ≤ 11 * E := by linarith
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ ≤ E * (6 * E) := mul_le_mul hKE hC' (by linarith) hE0
      _ = _ := by ring
  · calc
      _ ≤ E * (2 * (E + 6 * E)) := by gcongr
      _ = _ := by ring
  · calc
      _ ≤ E * ((3 * E ^ 2) * (11 * E)) := by gcongr
      _ = _ := by ring

theorem strip_center_power_budget {N E : ℝ} (hN : 2 ≤ N) (hE : E ≤ N) (J : ℕ) :
    32 * (N ^ J) ^ 2 * E ≤ N ^ (2 * J + 6) := by
  calc
    _ ≤ 32 * (N ^ J) ^ 2 * N := mul_le_mul_of_nonneg_left hE (by positivity)
    _ = 32 * N ^ (2 * J + 1) := by
      rw [show 2 * J + 1 = J * 2 + 1 by omega, pow_add, pow_mul, pow_one]
      ring
    _ ≤ _ := by
      simpa only [show 2 * J + 1 + 5 = 2 * J + 6 by omega] using
        power_absorbs_constant hN (2 * J + 1) 5 (by norm_num : (32 : ℝ) ≤ 2 ^ 5)

theorem strip_format_power_budget {N E count : ℝ} (hN : 2 ≤ N)
    (hE : 1 ≤ E) (hEN : E ≤ N) (hcount : count ≤ 3 * E ^ 2) (M : ℕ) :
    2 * N ^ M + 2 * count + 2 ≤ N ^ (M + 6) := by
  have hN1 : 1 ≤ N := by linarith
  have hM : 1 ≤ N ^ M := one_le_pow₀ hN1
  have hN2 : 1 ≤ N ^ 2 := one_le_pow₀ hN1
  have hP : 1 ≤ N ^ (M + 2) := one_le_pow₀ hN1
  have hMP : N ^ M ≤ N ^ (M + 2) := by rw [pow_add]; nlinarith
  have hEP : E ^ 2 ≤ N ^ (M + 2) := by
    calc
      _ ≤ N ^ 2 := pow_le_pow_left₀ (by linarith) hEN 2
      _ ≤ _ := by rw [pow_add]; nlinarith [sq_nonneg N]
  calc
    _ ≤ 10 * N ^ (M + 2) := by nlinarith
    _ ≤ _ := by
      simpa only [show M + 2 + 4 = M + 6 by omega] using
        power_absorbs_constant hN (M + 2) 4 (by norm_num : (10 : ℝ) ≤ 2 ^ 4)

theorem strip_card_power_budget {N E count Z r : ℝ} (hN : 2 ≤ N)
    (hE : 1 ≤ E) (hEN : E ≤ N) (hcountE : count ≤ 3 * E ^ 2)
    (hZ : 0 ≤ Z) (hr : 0 < r) (hZr : Z * r ≤ 2 * E)
    (M U : ℕ) (hrinv : r⁻¹ ≤ N ^ U) :
    N ^ M * (count * (2 * Z + 1)) ≤ N ^ (M + U + 7) := by
  have hE0 : 0 ≤ E := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hU : 1 ≤ N ^ U := one_le_pow₀ hN1
  have hZ' : Z ≤ 2 * E * N ^ U := by
    calc
      _ ≤ (2 * E) / r := (le_div_iff₀ hr).mpr hZr
      _ ≤ _ := by rw [div_eq_mul_inv]; gcongr
  have hZlist : 2 * Z + 1 ≤ 5 * E * N ^ U := by
    nlinarith [mul_le_mul hE hU (by norm_num) (by linarith : 0 ≤ E)]
  calc
    _ ≤ N ^ M * ((3 * E ^ 2) * (5 * E * N ^ U)) := by gcongr
    _ = 15 * N ^ M * E ^ 3 * N ^ U := by ring
    _ ≤ 15 * N ^ M * N ^ 3 * N ^ U := by gcongr
    _ = 15 * N ^ (M + U + 3) := by simp only [pow_add]; ring
    _ ≤ _ := by
      simpa only [show M + U + 3 + 4 = M + U + 7 by omega] using
        power_absorbs_constant hN (M + U + 3) 4 (by norm_num : (15 : ℝ) ≤ 2 ^ 4)

theorem strip_entry_power_budget {N K E C r : ℝ} (hN : 2 ≤ N)
    (hK : 1 ≤ K) (hE : 1 ≤ E) (hKE : K ≤ E) (hEN : E ≤ N)
    (hC : 0 ≤ C) (hCE : C ≤ 5 * E) (hr : 0 < r) (hr1 : r ≤ 1)
    (M U : ℕ) (hrinv : r⁻¹ ≤ N ^ U) :
    N ^ M * (2 * (K + (1 + C) * r + K⁻¹ + ((1 + C) * r)⁻¹)) ≤ N ^ (M + U + 6) := by
  have hE0 : 0 ≤ E := by linarith
  have hU : 1 ≤ N ^ U := one_le_pow₀ (by linarith : 1 ≤ N)
  have hC' : 1 + C ≤ 6 * E := by linarith
  have hCr : (1 + C) * r ≤ 6 * E :=
    (mul_le_mul_of_nonneg_left hr1 (by linarith)).trans (by simpa using hC')
  have hKinv : K⁻¹ ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hK
  have hr' : r ≤ (1 + C) * r := by nlinarith [mul_nonneg hC hr.le]
  have hCrinv : ((1 + C) * r)⁻¹ ≤ N ^ U := by
    exact (show ((1 + C) * r)⁻¹ ≤ r⁻¹ by
      simpa only [one_div] using one_div_le_one_div_of_le hr hr').trans hrinv
  have hlocal : 2 * (K + (1 + C) * r + K⁻¹ + ((1 + C) * r)⁻¹) ≤ 18 * E * N ^ U := by
    have hEU : E ≤ E * N ^ U := by nlinarith
    have hUE : N ^ U ≤ E * N ^ U := by nlinarith
    linarith
  calc
    _ ≤ N ^ M * (18 * E * N ^ U) := by gcongr
    _ ≤ N ^ M * (18 * N * N ^ U) := by gcongr
    _ = 18 * N ^ (M + U + 1) := by simp only [pow_add, pow_one]; ring
    _ ≤ _ := by
      simpa only [show M + U + 1 + 5 = M + U + 6 by omega] using
        power_absorbs_constant hN (M + U + 1) 5 (by norm_num : (18 : ℝ) ≤ 2 ^ 5)

/-- One exponent works uniformly for all supplied path envelopes. Its cutoff
may depend on the requested output slack; the polynomial exponents above do not. -/
theorem strip_uniform_power_envelope {N : ℕ → ℝ} (hN : Tendsto N atTop atTop)
    {τ loss : ℝ} (hτ : 0 < τ) (hloss : 0 < loss) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 ∧ ∀ᶠ k in atTop, ∀ E : ℝ,
      1 ≤ E → E ≤ N k ^ σ → E ≤ N k ∧ 100 * E ^ 8 ≤ N k ^ τ ∧ 6 * E ^ 2 ≤ N k ^ loss := by
  let σ : ℝ := min 1 (min (τ / 16) (loss / 4))
  have hσ : 0 < σ := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hσ1 : σ ≤ 1 := min_le_left _ _
  have hστ : σ ≤ τ / 16 := (min_le_right _ _).trans (min_le_left _ _)
  have hσloss : σ ≤ loss / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hτcut := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hN (show τ / 2 < τ by linarith) 100
  have hlcut := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hN (show loss / 2 < loss by linarith) 6
  refine ⟨σ, hσ, hσ1, ?_⟩
  filter_upwards [hN.eventually (eventually_ge_atTop (2 : ℝ)), hτcut, hlcut]
    with k hk hkτ hkl
  intro E hE hEN
  have hk1 : 1 ≤ N k := by linarith
  have hk0 : 0 ≤ N k := by linarith
  have hE0 : 0 ≤ E := by linarith
  refine ⟨?_, ?_, ?_⟩
  · exact hEN.trans (by simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hk1 hσ1)
  · have hpow : E ^ 8 ≤ N k ^ (τ / 2) := by
      calc
        _ ≤ (N k ^ σ) ^ 8 := pow_le_pow_left₀ hE0 hEN 8
        _ = N k ^ (σ * 8) := (Real.rpow_mul_natCast hk0 σ 8).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)
    exact (mul_le_mul_of_nonneg_left hpow (by norm_num)).trans hkτ.le
  · have hpow : E ^ 2 ≤ N k ^ (loss / 2) := by
      calc
        _ ≤ (N k ^ σ) ^ 2 := pow_le_pow_left₀ hE0 hEN 2
        _ = N k ^ (σ * 2) := (Real.rpow_mul_natCast hk0 σ 2).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)
    exact (mul_le_mul_of_nonneg_left hpow (by norm_num)).trans hkl.le

theorem strip_slack_of_power_envelope {E P : ℝ} (hE : 1 ≤ E) (hP : 100 * E ^ 8 ≤ P) :
    4 ≤ P ∧ E ≤ P ∧ 14 * E ^ 2 ≤ P ∧ 33 * E ^ 4 ≤ P ∧ 8 * E ≤ P := by
  have h1 : 1 ≤ E ^ 8 := one_le_pow₀ hE
  have hE1 : E ≤ E ^ 8 := by simpa using pow_le_pow_right₀ hE (show (1 : ℕ) ≤ 8 by omega)
  have hE2 : E ^ 2 ≤ E ^ 8 := pow_le_pow_right₀ hE (by omega)
  have hE4 : E ^ 4 ≤ E ^ 8 := pow_le_pow_right₀ hE (by omega)
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
