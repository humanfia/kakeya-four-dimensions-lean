-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.StripSecondScalePowers, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/StripSecondScalePowers.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/StripSecondScalePowers.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/StripSecondScalePowers.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/StripSecondScalePowers.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripPowerBudgets

/-! Quantitative first/second strip scales. Every actual path envelope below
one chosen power works after the same cutoff; neither cutoff depends on the
supplied parent, residual or strip predictions. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open Filter

theorem strip_second_scale_radius_bounds {N E A u : ℝ}
    (hN : 1 ≤ N) (hE : 1 ≤ E) (hA : 0 ≤ A) (hu : 0 ≤ u) :
    32 * (1 + 2 * E) * (A * N ^ (-u)) / N ^ (-u / 2) ≤
        96 * A * E * N ^ (-u / 2) ∧
      32 * (1 + 2 * E) * (A * N ^ (-u) + (1 + 2 * E) * N ^ (-u / 2)) /
        N ^ (-u / 4) ≤ 96 * (A + 3) * E ^ 2 * N ^ (-u / 4) := by
  have hNpos : 0 < N := by linarith
  have h3 : 1 + 2 * E ≤ 3 * E := by linarith
  have hab : N ^ (-u) ≤ N ^ (-u / 2) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hratio : N ^ (-u) / N ^ (-u / 2) = N ^ (-u / 2) := by
    rw [← Real.rpow_sub hNpos]
    congr 1
    ring
  have hratio' : N ^ (-u / 2) / N ^ (-u / 4) = N ^ (-u / 4) := by
    rw [← Real.rpow_sub hNpos]
    congr 1
    ring
  have hW : A * N ^ (-u) + (1 + 2 * E) * N ^ (-u / 2) ≤
      (A + 3) * E * N ^ (-u / 2) := by
    have hAE : A ≤ A * E := by nlinarith
    calc
      _ ≤ A * N ^ (-u / 2) + (3 * E) * N ^ (-u / 2) := by gcongr
      _ ≤ (A * E) * N ^ (-u / 2) + (3 * E) * N ^ (-u / 2) := by gcongr
      _ = _ := by ring
  constructor
  · calc
      _ ≤ 32 * (3 * E) * (A * N ^ (-u)) / N ^ (-u / 2) := by gcongr
      _ = 96 * A * E * (N ^ (-u) / N ^ (-u / 2)) := by ring
      _ = _ := by rw [hratio]
  · calc
      _ ≤ 32 * (3 * E) * ((A + 3) * E * N ^ (-u / 2)) / N ^ (-u / 4) := by gcongr
      _ = 96 * (A + 3) * E ^ 2 * (N ^ (-u / 2) / N ^ (-u / 4)) := by ring
      _ = _ := by rw [hratio']

theorem strip_second_scale_power_window {N : ℕ → ℝ} (hN : Tendsto N atTop atTop)
    {A u : ℝ} (hA : 0 ≤ A) (hu : 0 < u) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 ∧ σ ≤ u / 32 ∧ ∀ᶠ k in atTop,
      ∀ E : ℝ, 1 ≤ E → E ≤ N k ^ σ →
      let r₀ := A * N k ^ (-u)
      let r₁ := N k ^ (-u / 2)
      let r₂ := N k ^ (-u / 4)
      let w := r₀ + (1 + 2 * E) * r₁
      0 < r₁ ∧ 0 < r₂ ∧ r₁ ≤ r₂ ∧ r₂ ≤ 1 ∧ 4 * r₀ ≤ r₁ ∧ 4 * w ≤ r₂ ∧
        32 * (1 + 2 * E) * r₀ / r₁ ≤ N k ^ (-u / 4) ∧
        32 * (1 + 2 * E) * w / r₂ ≤ N k ^ (-u / 8) ∧
        E * (32 * (1 + 2 * E) * w / r₂) ≤ N k ^ (-u / 16) := by
  let σ : ℝ := min 1 (u / 32)
  have hσ : 0 < σ := lt_min (by norm_num) (by positivity)
  have hσ1 : σ ≤ 1 := min_le_left _ _
  have hσu : σ ≤ u / 32 := min_le_right _ _
  have hcut₁ := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hN (show σ - u / 2 < -u / 4 by linarith) (96 * A)
  have hcut₂ := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hN (show σ * 2 - u / 4 < -u / 8 by linarith) (96 * (A + 3))
  refine ⟨σ, hσ, hσ1, hσu, ?_⟩
  filter_upwards [hN.eventually (eventually_ge_atTop (2 : ℝ)), hcut₁, hcut₂]
    with k hk hk₁ hk₂
  intro E hE hEN
  have hk1 : 1 ≤ N k := by linarith
  have hkpos : 0 < N k := by linarith
  have hk0 : 0 ≤ N k := hkpos.le
  have hE0 : 0 ≤ E := by linarith
  have hr₁ : 0 < N k ^ (-u / 2) := Real.rpow_pos_of_pos hkpos _
  have hr₂ : 0 < N k ^ (-u / 4) := Real.rpow_pos_of_pos hkpos _
  have hr₂1 : N k ^ (-u / 4) ≤ 1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hk1 (show -u / 4 ≤ 0 by linarith)
  have hr₈1 : N k ^ (-u / 8) ≤ 1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hk1 (show -u / 8 ≤ 0 by linarith)
  obtain ⟨hR₁, hR₂⟩ := strip_second_scale_radius_bounds hk1 hE hA hu.le
  have hbound₁ : 32 * (1 + 2 * E) * (A * N k ^ (-u)) / N k ^ (-u / 2) ≤
      N k ^ (-u / 4) := by
    calc
      _ ≤ 96 * A * E * N k ^ (-u / 2) := hR₁
      _ ≤ 96 * A * N k ^ σ * N k ^ (-u / 2) := by gcongr
      _ = 96 * A * N k ^ (σ - u / 2) := by
        rw [show σ - u / 2 = σ + (-u / 2) by ring, Real.rpow_add hkpos]
        ring
      _ ≤ _ := hk₁.le
  have hbound₂ : 32 * (1 + 2 * E) *
      (A * N k ^ (-u) + (1 + 2 * E) * N k ^ (-u / 2)) / N k ^ (-u / 4) ≤
      N k ^ (-u / 8) := by
    calc
      _ ≤ 96 * (A + 3) * E ^ 2 * N k ^ (-u / 4) := hR₂
      _ ≤ 96 * (A + 3) * (N k ^ σ) ^ 2 * N k ^ (-u / 4) := by gcongr
      _ = 96 * (A + 3) * N k ^ (σ * 2 - u / 4) := by
        have hp : (N k ^ σ) ^ 2 = N k ^ (σ * 2) :=
          (Real.rpow_mul_natCast hk0 σ 2).symm
        rw [hp, show σ * 2 - u / 4 = σ * 2 + (-u / 4) by ring, Real.rpow_add hkpos]
        ring
      _ ≤ _ := hk₂.le
  have hr₀ : 0 ≤ A * N k ^ (-u) := mul_nonneg hA (Real.rpow_nonneg hk0 _)
  have hw : 0 ≤ A * N k ^ (-u) + (1 + 2 * E) * N k ^ (-u / 2) := by positivity
  refine ⟨hr₁, hr₂, Real.rpow_le_rpow_of_exponent_le hk1 (by linarith), hr₂1,
    ?_, ?_, hbound₁, hbound₂, ?_⟩
  · have hnum := (div_le_one hr₁).mp (hbound₁.trans hr₂1)
    nlinarith [mul_nonneg (show 0 ≤ 32 * (1 + 2 * E) - 4 by linarith) hr₀]
  · have hnum := (div_le_one hr₂).mp (hbound₂.trans hr₈1)
    nlinarith [mul_nonneg (show 0 ≤ 32 * (1 + 2 * E) - 4 by linarith) hw]
  · calc
      _ ≤ E * N k ^ (-u / 8) := mul_le_mul_of_nonneg_left hbound₂ hE0
      _ ≤ N k ^ σ * N k ^ (-u / 8) := by gcongr
      _ = N k ^ (σ - u / 8) := by
        rw [show σ - u / 8 = σ + (-u / 8) by ring, Real.rpow_add hkpos]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
