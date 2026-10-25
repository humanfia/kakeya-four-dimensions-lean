import Mathlib
import ChallengeDeps
import Submission.Obl.k4_oss_dyadic_reduction.Reduction
import Submission.Obl.k4_oss_dyadic_reduction.Numerics
set_option linter.unusedVariables false

open Submission.Obl.k4_oss_dyadic_reduction

/-!
# `Submission.k4_oss_dyadic_reduction`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_oss_dyadic_reduction`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_oss_dyadic_reduction/`
belong to this obligation.
-/

theorem Submission.k4_oss_dyadic_reduction : (∀ s : ℝ, 0 < s → s ≤ 1 → ∃ n : ℕ, 2 ≤ n ∧ ∃ ε τ δ₀ : ℝ, 0 < ε ∧ 0 < τ ∧ 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ μ : Fin n → MeasureTheory.Measure ℝ, (∀ j : Fin n, MeasureTheory.IsProbabilityMeasure (μ j)) → (∀ j : Fin n, μ j (Set.Icc (1 : ℝ) 2)ᶜ = 0) → (∀ (j : Fin n) (x u : ℝ), δ ≤ u → u ≤ 1 → μ j (Set.Icc (x - u) (x + u)) ≤ ENNReal.ofReal (δ ^ (-ε) * u ^ s)) → ∀ ξ : ℝ, δ⁻¹ ≤ |ξ| → |ξ| ≤ 2 * δ⁻¹ → ‖MeasureTheory.integral (MeasureTheory.Measure.pi μ) (fun x : Fin n → ℝ => Complex.exp (((-2 * Real.pi * ξ * (∏ j : Fin n, x j) : ℝ) : ℂ) * Complex.I))‖ ≤ δ ^ τ) → ∀ s : ℝ, 0 < s → s ≤ 1 → ∃ n : ℕ, 2 ≤ n ∧ ∃ r₀ ε₀ τ : ℝ, 0 < r₀ ∧ 0 < ε₀ ∧ 0 < τ ∧ ∀ r : ℝ, 0 < r → r < r₀ → ∀ μ : MeasureTheory.Measure ℝ, MeasureTheory.IsProbabilityMeasure μ → μ (Set.Icc (-1 : ℝ) 1)ᶜ = 0 → (∀ x u : ℝ, r ≤ u → u ≤ 1 → μ (Set.Icc (x - u) (x + u)) ≤ ENNReal.ofReal (r ^ (-ε₀) * u ^ s)) → ∀ ξ : ℝ, r⁻¹ ≤ |ξ| → |ξ| ≤ 2 * r⁻¹ → ‖MeasureTheory.integral (MeasureTheory.Measure.pi (fun _ : Fin n => μ)) (fun x : Fin n → ℝ => Complex.exp (((-2 * Real.pi * ξ * (∏ j : Fin n, x j) : ℝ) : ℂ) * Complex.I))‖ ≤ |ξ| ^ (-τ) := by
  intro core s hs hs1
  obtain ⟨n, hn, ε, t, δ₀, hε, ht, hδ₀, hcore⟩ := core s hs hs1
  have hunit : UnitDecay n s ε t δ₀ := hcore
  obtain ⟨ε₀, τ, r₀, hε₀, hτ, hr₀, hparams⟩ :=
    exists_mesh_parameters n hs hs1 hε ht hδ₀
  refine ⟨n, hn, r₀, ε₀, τ, hr₀, hε₀, hτ, ?_⟩
  intro r hr hrr₀ μ hμ hsupport hcap ξ hξ1 hξ2
  letI := hμ
  obtain ⟨N, η, D, hN, hrN, hη, hD, hD₀, hND, hcoef, hfinal⟩ := hparams r hr hrr₀
  have hbound := norm_pi_mesh_le hunit hs.le hε.le ht.le hr hN hrN hη hD hD₀
    hND hcoef μ hsupport hcap hξ1 hξ2
  have hξ : 0 < |ξ| := (inv_pos.mpr hr).trans_le hξ1
  have hinv : r / 2 ≤ |ξ|⁻¹ := by
    calc
      r / 2 = 1 / (2 * r⁻¹) := by field_simp
      _ ≤ 1 / |ξ| := one_div_le_one_div_of_le hξ hξ2
      _ = |ξ|⁻¹ := one_div _
  have hend : (r / 2) ^ τ ≤ |ξ| ^ (-τ) := by
    rw [Real.rpow_neg_eq_inv_rpow]
    exact Real.rpow_le_rpow (by positivity) hinv hτ.le
  exact hbound.trans (hfinal.trans hend)
