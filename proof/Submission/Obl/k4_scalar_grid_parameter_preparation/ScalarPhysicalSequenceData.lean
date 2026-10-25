/- Adapted from this LOT tree, o092, session x0317, commit 9697971769c3.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/ScalarPhysicalSequenceData.lean -/
import Submission.Obl.k4_scalar_grid_parameter_preparation.ScalarScalePackets
import Submission.Obl.k4_scalar_grid_parameter_preparation.VelocityBins

/-! Original caps and saturated packet families used by physical preparation. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

open Set MeasureTheory
open Submission.Obl.k4_fixed_budget_quadratic_recovery
open scoped ENNReal

def ScalarOriginalCapsAt {X : Type*} [MeasurableSpace X]
    (N K : ℕ → ℝ) (W : ℕ → ℕ)
    (ρ : (k : ℕ) → Fin (W k) → Measure (X × ℝ))
    (π : (k : ℕ) → Fin (W k) → Measure ℝ)
    (a : X → Fin 5 → ℝ) (d S R : ℝ) (k : ℕ) : Prop :=
  ∀ (g : Fin (W k)) (r s b : ℝ), R⁻¹ ≤ r → r ≤ R → R⁻¹ ≤ s → s ≤ R → R⁻¹ ≤ b → b ≤ R →
    (∀ c : ℤ, π k g (scalarVelocityBin (N k ^ (-b)) c) ≤
      ENNReal.ofReal (K k * N k ^ (-S * b))) ∧
    (∀ i j z c : ℤ, ρ k g {p | (⌊p.2 / N k ^ (-r)⌋ : ℤ) = i ∧
      (⌊scalarY (a p.1) p.2 / N k ^ (-r)⌋ : ℤ) = j ∧
      (⌊scalarX (a p.1) p.2 / N k ^ (-s)⌋ : ℤ) = z ∧
      a p.1 1 ∈ scalarVelocityBin (N k ^ (-b)) c} ≤
        ENNReal.ofReal (K k * N k ^ (-2 * r - d * s)) * π k g (scalarVelocityBin (N k ^ (-b)) c))

def ScalarPacketSequenceAt {X : Type*} [MeasurableSpace X]
    (N K : ℕ → ℝ) (W : ℕ → ℕ)
    (ν : (k : ℕ) → Fin (W k) → Measure X)
    (ρ : (k : ℕ) → Fin (W k) → Measure (X × ℝ))
    (a : X → Fin 5 → ℝ) (d R : ℝ) (k : ℕ) : Prop :=
  ∀ r : ℝ, R⁻¹ ≤ r → r ≤ R → ∃ (n q : ℕ)
    (D : ScalarScalePackets X (Fin (W k)) a (K k) (N k ^ (-r)) n q),
    0 < q ∧ (q : ℝ) ≤ K k * N k ^ r ∧
    (∀ i, ENNReal.ofReal (N k ^ (-d * r) / (K k * (q : ℝ))) ≤ ν k (D.world i) (D.labels i)) ∧
    ∀ g, ρ k g (scalarScaleCovered D g)ᶜ = 0

end Submission.Obl.k4_scalar_grid_parameter_preparation
