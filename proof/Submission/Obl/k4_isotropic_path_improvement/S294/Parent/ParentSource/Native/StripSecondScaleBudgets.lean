-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.StripSecondScaleBudgets, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/StripSecondScaleBudgets.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/StripSecondScaleBudgets.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/StripSecondScaleBudgets.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/StripSecondScaleBudgets.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripPowerBudgets

/-! The fixed entropy power is paid in the angular overlap decay and output
complexity. A separate small actual path power handles every later slack. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open Filter
open Submission.Obl.k4_native_finite_terminal_atlas_lift

/-- A cutoff uniform over all later path envelopes, rather than over a
single previously fixed subpower sequence. -/
theorem strip_uniform_monomial_bound {N : ℕ → ℝ} (hN : Tendsto N atTop atTop)
    {a b C : ℝ} (hab : a < b) (hC : 0 ≤ C) (p : ℕ) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 ∧ ∀ᶠ k in atTop,
      ∀ E : ℝ, 1 ≤ E → E ≤ N k ^ σ → C * E ^ p * N k ^ a ≤ N k ^ b := by
  let σ : ℝ := min 1 ((b - a) / (2 * ((p : ℝ) + 1)))
  have hσ : 0 < σ := lt_min (by norm_num) (by positivity)
  have hσ1 : σ ≤ 1 := min_le_left _ _
  have hσbudget : σ * (2 * ((p : ℝ) + 1)) ≤ b - a :=
    (le_div_iff₀ (by positivity : 0 < 2 * ((p : ℝ) + 1))).mp (min_le_right _ _)
  have hσp : a + σ * p ≤ (a + b) / 2 := by nlinarith
  have hcut := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hN (show (a + b) / 2 < b by linarith) C
  refine ⟨σ, hσ, hσ1, ?_⟩
  filter_upwards [hN.eventually (eventually_ge_atTop (2 : ℝ)), hcut] with k hk hkc
  intro E hE hEN
  have hk1 : 1 ≤ N k := by linarith
  have hkpos : 0 < N k := by linarith
  have hEp : E ^ p ≤ N k ^ (σ * p) := by
    exact (pow_le_pow_left₀ (by linarith) hEN p).trans_eq
      (Real.rpow_mul_natCast hkpos.le σ p).symm
  calc
    _ ≤ C * N k ^ (σ * p) * N k ^ a := by gcongr
    _ = C * N k ^ (a + σ * p) := by rw [Real.rpow_add hkpos]; ring
    _ ≤ C * N k ^ ((a + b) / 2) := by gcongr
    _ ≤ _ := hkc.le

theorem strip_heavy_net_count_power {N E floor count a : ℝ}
    (hN : 2 ≤ N) (hE : 1 ≤ E) (hEN : E ≤ N) (hfloor : 0 < floor)
    (p V : ℕ) (ha : 0 ≤ a) (hV : 2 * a ≤ (V : ℝ))
    (hInv : floor⁻¹ ≤ E ^ p * N ^ a) (hcount : count ≤ 2 / floor ^ 2 + 1) :
    count ≤ N ^ (2 * p + V + 2) := by
  have hN1 : 1 ≤ N := by linarith
  have hNpos : 0 < N := by linarith
  have hH : 1 ≤ E ^ p * N ^ a := by
    simpa only [one_mul] using mul_le_mul
      (one_le_pow₀ hE (n := p)) (Real.one_le_rpow hN1 ha) (by norm_num) (by positivity)
  have hcount' : count ≤ 3 * (E ^ p * N ^ a) ^ 2 := by
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ floor⁻¹) hInv 2
    have hid : 2 / floor ^ 2 + 1 = 2 * (floor⁻¹) ^ 2 + 1 := by field_simp
    rw [hid] at hcount
    nlinarith [one_le_pow₀ hH (n := 2)]
  have hHp : E ^ p * N ^ a ≤ N ^ ((p : ℝ) + a) := by
    rw [Real.rpow_add hNpos, Real.rpow_natCast]
    gcongr
  have hsq : (E ^ p * N ^ a) ^ 2 ≤ N ^ (2 * p + V) := by
    calc
      _ ≤ (N ^ ((p : ℝ) + a)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hHp 2
      _ = N ^ (((p : ℝ) + a) * 2) := (Real.rpow_mul_natCast hNpos.le _ 2).symm
      _ ≤ N ^ ((2 * p + V : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; nlinarith)
      _ = _ := Real.rpow_natCast _ _
  calc
    _ ≤ 3 * N ^ (2 * p + V) := hcount'.trans (mul_le_mul_of_nonneg_left hsq (by norm_num))
    _ ≤ _ := power_absorbs_constant hN (2 * p + V) 2 (by norm_num)

/-- Positive fixed exponent gaps make both packing errors and the sum of
far-pair overlaps negligible at once, uniformly before the supplied path. -/
theorem strip_two_scale_error_window {N : ℕ → ℝ} (hN : Tendsto N atTop atTop)
    {a v₁ v₂ : ℝ} (hpack : 2 * a < v₁) (hoverlap : 4 * a < v₂) (P Q : ℕ) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 ∧ ∀ᶠ k in atTop,
      ∀ E : ℝ, 1 ≤ E → E ≤ N k ^ σ →
        2 * E ^ P * N k ^ (2 * a - v₁) ≤ 1 ∧
        900 * E ^ (Q + 8) * N k ^ (4 * a - v₂) ≤ 1 := by
  obtain ⟨σ₁, hσ₁, hσ₁1, hk₁⟩ := strip_uniform_monomial_bound hN
    (show 2 * a - v₁ < 0 by linarith) (by norm_num : (0 : ℝ) ≤ 2) P
  obtain ⟨σ₂, hσ₂, hσ₂1, hk₂⟩ := strip_uniform_monomial_bound hN
    (show 4 * a - v₂ < 0 by linarith) (by norm_num : (0 : ℝ) ≤ 900) (Q + 8)
  refine ⟨min σ₁ σ₂, lt_min hσ₁ hσ₂, (min_le_left _ _).trans hσ₁1, ?_⟩
  filter_upwards [hN.eventually (eventually_ge_atTop (2 : ℝ)), hk₁, hk₂] with k hk h₁ h₂
  intro E hE hEN
  have hNk : 1 ≤ N k := by linarith
  constructor
  · simpa only [Real.rpow_zero] using h₁ E hE (hEN.trans
      (Real.rpow_le_rpow_of_exponent_le hNk (min_le_left _ _)))
  · simpa only [Real.rpow_zero] using h₂ E hE (hEN.trans
      (Real.rpow_le_rpow_of_exponent_le hNk (min_le_right _ _)))

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
