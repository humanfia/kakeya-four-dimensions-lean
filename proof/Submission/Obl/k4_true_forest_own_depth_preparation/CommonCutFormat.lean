import Submission.Obl.k4_true_forest_own_depth_preparation.CommonCut
import Submission.Obl.k4_quadratic_atlas_normalization.ChartMonotonicity

namespace Submission.Obl.k4_true_forest_own_depth_preparation

open Set
open Submission.Obl.k4_coarsened_outer_horizon_composition

/-- Fixed polynomial complexity for a common cutoff over a polynomial number
of already formatted restrictions. -/
theorem common_cut_format_budget {N : ℝ} {C : ℕ} (hN : 2 ≤ N)
    (M M₁ : ℕ) (hC : (C : ℝ) ≤ N ^ M) :
    N ^ M₁ + ((2 * C : ℕ) : ℝ) * N ^ M₁ ≤ N ^ (M + M₁ + 2) := by
  have hN1 : 1 ≤ N := by linarith
  have hpow : 1 ≤ N ^ M := one_le_pow₀ hN1
  have hN2 : (4 : ℝ) ≤ N ^ 2 := by nlinarith
  have hcoef : 1 + ((2 * C : ℕ) : ℝ) ≤ N ^ M * N ^ 2 := by
    push_cast
    nlinarith
  calc
    _ = (1 + ((2 * C : ℕ) : ℝ)) * N ^ M₁ := by ring
    _ ≤ (N ^ M * N ^ 2) * N ^ M₁ := mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = _ := by simp only [pow_add]; ring

/-- All old/new incidence predicates can be combined into a shared cutoff
without changing their polynomial degree. -/
theorem format_common_selection {N : ℝ} {C W M M₁ D : ℕ}
    (hN : 2 ≤ N) (hC : (C : ℝ) ≤ N ^ M) (γ : Fin C → Fin W)
    (F H : Fin C → Set Inc)
    (hF : ∀ b i, fmt 7 (N ^ M₁) D
      {z : Fin 7 → ℝ | ((i, fun e : Fin 6 => z e.castSucc), z 6) ∈ F b})
    (hH : ∀ b i, fmt 7 (N ^ M₁) D
      {z : Fin 7 → ℝ | ((i, fun e : Fin 6 => z e.castSucc), z 6) ∈ H b})
    (b : Fin C) (i : ℕ) :
    fmt 7 (N ^ (M + M₁ + 2)) D
      {z : Fin 7 → ℝ | ((i, fun e : Fin 6 => z e.castSucc), z 6) ∈
        F b ∩ commonGood γ F H (γ b)} := by
  let φ : (Fin 7 → ℝ) → Inc := fun z => ((i, fun e => z e.castSucc), z 6)
  have hf := format_commonGood γ (fun a => φ ⁻¹' F a) (fun a => φ ⁻¹' H a)
    (fun a => hF a i) (fun a => hH a i) (γ b)
  have hi := Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.inter (hF b i) hf
  have heq : {z : Fin 7 → ℝ | φ z ∈ F b ∩ commonGood γ F H (γ b)} =
      (φ ⁻¹' F b) ∩ commonGood γ (fun a => φ ⁻¹' F a) (fun a => φ ⁻¹' H a) (γ b) := by
    rw [← preimage_commonGood]
    rfl
  change fmt 7 (N ^ (M + M₁ + 2)) D {z | φ z ∈ F b ∩ commonGood γ F H (γ b)}
  rw [heq]
  exact Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.mono (D' := D) hi
    (common_cut_format_budget hN M M₁ hC) (by simp)

end Submission.Obl.k4_true_forest_own_depth_preparation
