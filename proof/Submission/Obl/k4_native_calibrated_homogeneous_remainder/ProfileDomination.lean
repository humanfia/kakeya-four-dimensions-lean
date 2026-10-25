import Submission.Obl.k4_native_calibrated_homogeneous_remainder.TypicalOperations
import Submission.Obl.k4_native_grid_profile_extension.Profiles.ExponentLimit
import Submission.Obl.k4_dyadic_crop_typicality.Assembly

/-! Typical profiles survive subpower changes in the sampling measure. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_native_grid_profile_extension.Profiles

theorem powerSmall_pullback_of_subpower_domination
    {Ω Ω' : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)] [∀ k, MeasurableSpace (Ω' k)]
    (N : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k)
    (μ : (k : ℕ) → Measure (Ω k)) (μ' : (k : ℕ) → Measure (Ω' k))
    (ψ : ℕ → ℕ) (hψ : Tendsto ψ atTop atTop) (e : (k : ℕ) → Ω' k → Ω (ψ k))
    (B : ℕ → ℝ)
    (hB : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, B k ≤ N (ψ k) ^ ε)
    (hdom : ∀ k (A : Set (Ω (ψ k))), μ' k (e k ⁻¹' A) ≤
      ENNReal.ofReal (B k) * μ (ψ k) A)
    (A : (k : ℕ) → Set (Ω k)) (ht : IsPowerSmall N (fun k => μ k (A k))) :
    IsPowerSmall (N ∘ ψ) (fun k => μ' k (e k ⁻¹' A (ψ k))) := by
  have hsmall := IsPowerSmall.comp ht ψ hψ
  have hprod := Submission.Obl.k4_dyadic_crop_typicality.powerSmall_mul_subpower
    (fun k => hN (ψ k)) hB hsmall
  exact IsPowerSmall.mono hprod (Eventually.of_forall fun k => hdom k _)

theorem typical_pullback_of_subpower_domination
    {Ω Ω' : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)] [∀ k, MeasurableSpace (Ω' k)]
    (N : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k)
    (μ : (k : ℕ) → Measure (Ω k)) (μ' : (k : ℕ) → Measure (Ω' k))
    (ψ : ℕ → ℕ) (hψ : Tendsto ψ atTop atTop) (e : (k : ℕ) → Ω' k → Ω (ψ k))
    (B : ℕ → ℝ)
    (hB : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, B k ≤ N (ψ k) ^ ε)
    (hdom : ∀ k (A : Set (Ω (ψ k))), μ' k (e k ⁻¹' A) ≤
      ENNReal.ofReal (B k) * μ (ψ k) A)
    (g : (k : ℕ) → Ω k → ENNReal) (a : ℝ) (ht : HasTypicalDensity N μ g a) :
    HasTypicalDensity (N ∘ ψ) μ' (fun k z => g (ψ k) (e k z)) a := by
  intro τ hτ
  have hsmall := (IsPowerSmall.comp (ht τ hτ) ψ hψ)
  have hprod := Submission.Obl.k4_dyadic_crop_typicality.powerSmall_mul_subpower
    (fun k => hN (ψ k)) hB hsmall
  apply IsPowerSmall.mono hprod
  apply Eventually.of_forall
  intro k
  change μ' k (e k ⁻¹' {x | g (ψ k) x < ENNReal.ofReal (N (ψ k) ^ (-a - τ)) ∨
    ENNReal.ofReal (N (ψ k) ^ (-a + τ)) < g (ψ k) x}) ≤ _
  exact hdom k _

end Submission.Obl.k4_native_calibrated_homogeneous_remainder
