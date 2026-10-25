import Mathlib

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open Filter

/-- Only the numerical hypotheses of the key comparison kernels. All
physical graph and measure assertions remain outside this record. -/
structure ShortNumerics (N H q a g D χ ζ w mesh B Lb Lv : ℝ) : Prop where
  q_one : q ≤ 1
  chi_q : χ ≤ q
  chi_m : χ ≤ q * g
  m_D : q * g ≤ D
  jitter_quarter : w ≤ 1 / 4
  jitter_resolved : 18 * B * w ≤ H
  interval_drift : q * (ζ + χ) ≤ (q * g) * w
  mesh_time : mesh ≤ q / 2
  mesh_intercept : mesh ≤ 2 * χ
  shear_intercept : Lv * mesh ≤ 2 * χ
  mesh_slice : mesh ≤ (q * g) * w
  shear_slice : Lv * mesh ≤ (q * g) * w
  block_freeze : 3 * Lb * mesh ≤ H * a
  sheet_freeze : 7 * H * (mesh + (mesh + Lv * mesh) / (4 * D)) ≤ H * a
  block_graph : Lb * (2 * χ + q * (ζ + χ)) ≤ H * a
  sheet_graph : 7 * H * (q * (ζ + χ)) / (4 * D) ≤ H * a
  key_drift : (B + 1) * 7 * (q * (ζ + χ) / (2 * (q * g))) ≤ 1
  key_freeze : (B + 1) * 7 * (mesh / q + (1 + Lv) * mesh / (2 * (q * g))) ≤ 1
  affine_sample_budget : 2 * H + H * a + 3 * (1 + 2 * H) ^ 2 *
    (H * (1 + a / q ^ 2)) ≤ Lb
  block_coeff : 8 * (Lb * (2 + 4 * H + 8 * H) / a) ≤ B
  sheet_coeff : 88 * H / a ≤ B

/-- A pure quantitative target for the short comparisons at any of the
three fixed depths. The slack exponent is chosen before the scale cutoff. -/
def ShortNumericsStatement : Prop :=
  ∀ (N : ℕ → ℝ), (∀ k, 2 ≤ N k) → Tendsto N atTop atTop →
  ∀ κ s₀ s M e₀ : ℝ, 0 < κ → κ ≤ 1 → 0 < s₀ → s₀ < s → s < 3 * s₀ / 2 →
    100 * s₀ < M → 100 * M < e₀ →
  ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ →
    ∀ᶠ k in atTop, ∀ K q : ℝ,
      1 ≤ K → K ≤ N k ^ η →
      (N k ^ (-κ * s)) / K ≤ q → q ≤ K * N k ^ (-κ * s) →
      ShortNumerics (N k) (N k ^ η) q (N k ^ (-s)) (N k ^ (-κ * s))
        (N k ^ (-2 * κ * s₀)) (N k ^ (-M)) (N k ^ (-e₀))
        (N k ^ (-M / 4)) (N k ^ (-2 * M))
        (N k ^ (10 * s₀)) (N k ^ (5 * s₀)) (4 * N k ^ η)

/- Inlined from LOT tree g-oai-074, obligation o202, session x0952,
commit 2fb339809fcfce34b26992c753e7b7c590ce76f7, file Submission/Obl/k4_horizontal_subcritical_rate_candidates/Wide/ShortNumerics.lean.
Independent-hidden-depth generalization of our original target. -/
/-- The same coarse time depth with an independently finer hidden accuracy. -/
def ShortNumericsAtHiddenDepthStatement : Prop :=
  ∀ (N : ℕ → ℝ), (∀ k, 2 ≤ N k) → Tendsto N atTop atTop →
  ∀ κ s₀ s sp M e₀ : ℝ, 0 < κ → κ ≤ 1 → 0 < s₀ → s₀ < s → s ≤ sp → sp < 3 * s₀ / 2 →
    100 * s₀ < M → 100 * M < e₀ →
  ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ →
    ∀ᶠ k in atTop, ∀ K q : ℝ,
      1 ≤ K → K ≤ N k ^ η →
      (N k ^ (-κ * s)) / K ≤ q → q ≤ K * N k ^ (-κ * s) →
      ShortNumerics (N k) (N k ^ η) q (N k ^ (-sp)) (N k ^ (-κ * s))
        (N k ^ (-2 * κ * s₀)) (N k ^ (-M)) (N k ^ (-e₀))
        (N k ^ (-M / 4)) (N k ^ (-2 * M))
        (N k ^ (10 * s₀)) (N k ^ (5 * s₀)) (4 * N k ^ η)


end Submission.Obl.k4_wide_three_layer_scalar_inputs
