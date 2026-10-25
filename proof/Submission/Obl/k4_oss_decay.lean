import Mathlib
import ChallengeDeps
import Submission.Obl.k4_oss_collision_cauchy_schwarz
import Submission.Obl.k4_oss_projection_flattening
import Submission.Obl.k4_oss_flat_decay
import Submission.Obl.k4_oss_unit_decay
import Submission.Obl.k4_oss_dyadic_reduction
set_option linter.unusedVariables false

/-!
# `Submission.k4_oss_decay`

Glue of the split of o004 (Bourgain's route, `n` free):

* `k4_oss_collision_cauchy_schwarz` and `k4_oss_projection_flattening`: one mixing step
  `(x₁y₁ - x₂y₂)/4` flattens a non-flat law by `δ^c` (the second uses the prebuilt package's
  robust projection theorem);
* `k4_oss_flat_decay`: a flat law times a Frostman law has small Fourier transform;
* `k4_oss_unit_decay`: from these three, multilinear decay for Frostman laws on `[1,2]` (CORE),
  by a Cauchy-Schwarz chain;
* `k4_oss_dyadic_reduction`: CORE implies the frozen statement (dyadic shells and signs).
-/

theorem Submission.k4_oss_decay : ∀ s : ℝ, 0 < s → s ≤ 1 → ∃ n : ℕ, 2 ≤ n ∧ ∃ r₀ ε₀ τ : ℝ, 0 < r₀ ∧ 0 < ε₀ ∧ 0 < τ ∧ ∀ r : ℝ, 0 < r → r < r₀ → ∀ μ : MeasureTheory.Measure ℝ, MeasureTheory.IsProbabilityMeasure μ → μ (Set.Icc (-1 : ℝ) 1)ᶜ = 0 → (∀ x u : ℝ, r ≤ u → u ≤ 1 → μ (Set.Icc (x - u) (x + u)) ≤ ENNReal.ofReal (r ^ (-ε₀) * u ^ s)) → ∀ ξ : ℝ, r⁻¹ ≤ |ξ| → |ξ| ≤ 2 * r⁻¹ → ‖MeasureTheory.integral (MeasureTheory.Measure.pi (fun _ : Fin n => μ)) (fun x : Fin n → ℝ => Complex.exp (((-2 * Real.pi * ξ * (∏ j : Fin n, x j) : ℝ) : ℂ) * Complex.I))‖ ≤ |ξ| ^ (-τ) :=
  Submission.k4_oss_dyadic_reduction
    (Submission.k4_oss_unit_decay Submission.k4_oss_collision_cauchy_schwarz
      Submission.k4_oss_projection_flattening Submission.k4_oss_flat_decay)
