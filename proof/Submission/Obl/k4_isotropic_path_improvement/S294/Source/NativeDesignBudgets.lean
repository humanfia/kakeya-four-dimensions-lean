-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.NativeDesignBudgets, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeDesign
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.RegularityMassBudgets

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeDesign

open Filter

noncomputable section

/-- The literal fixed-length regularity product uses less than one
tenth of the native failure exponent. -/
theorem regularityCoeff_mass_budget (κ₁ d₁ : ℝ) {Ep : ℕ} {precision loss : ℝ}
    (hloss : 0 < loss) :
    28*regularityCoeff κ₁ d₁ Ep precision loss*(regularityLength κ₁ d₁ Ep precision loss:ℝ) <
      massCoeff κ₁ d₁ Ep precision loss/10 := by
  have hL : (0:ℝ) < regularityLength κ₁ d₁ Ep precision loss :=
    Nat.cast_pos.mpr (regularityLength_pos _ _ _ _ _)
  have hmass := massCoeff_pos κ₁ d₁ (Ep:=Ep) (precision:=precision) hloss
  have heq : 28*regularityCoeff κ₁ d₁ Ep precision loss*
      (regularityLength κ₁ d₁ Ep precision loss:ℝ)=7*massCoeff κ₁ d₁ Ep precision loss/100 := by
    unfold regularityCoeff
    field_simp
    ring
  rw [heq]
  linarith only [hmass]

/-- The exact retention factor satisfies its native design power
bound, uniformly in every actual regularity constant after k. -/
theorem eventually_regularity_factor_le
    (N : ℕ → ℝ) (hN : Tendsto N atTop atTop) (κ₁ d₁ : ℝ)
    {Ep : ℕ} {precision loss gain L : ℝ}
    (hloss : 0 < loss) (hgain : 0 < gain) (hL : 0 < L) :
    ∀ᶠ k in atTop, ∀ A : ℝ, 1 ≤ A →
      A ≤ N k^(regularityCoeff κ₁ d₁ Ep precision loss*gain*L) →
      0 < regularityMassFactor A (regularityLength κ₁ d₁ Ep precision loss) ∧
      regularityMassFactor A (regularityLength κ₁ d₁ Ep precision loss) ≠ ⊤ ∧
      regularityMassFactor A (regularityLength κ₁ d₁ Ep precision loss) ≤
        ENNReal.ofReal (N k^(massCoeff κ₁ d₁ Ep precision loss*gain*L/10)) := by
  have hreg := regularityCoeff_pos κ₁ d₁ (Ep:=Ep) (precision:=precision) hloss
  have hcompare := mul_lt_mul_of_pos_right
    (regularityCoeff_mass_budget κ₁ d₁ (Ep:=Ep) (precision:=precision) hloss)
    (mul_pos hgain hL)
  apply eventually_regularity_mass_factor_le N hN (regularityLength κ₁ d₁ Ep precision loss)
    (by positivity : 0 < regularityCoeff κ₁ d₁ Ep precision loss*gain*L)
  nlinarith only [hcompare]

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeDesign
