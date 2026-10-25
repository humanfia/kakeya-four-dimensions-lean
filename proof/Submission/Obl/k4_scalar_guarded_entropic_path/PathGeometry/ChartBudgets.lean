/-
Adapted from this LOT tree, obligation o093, session x0535, commit 62576536,
Submission/Obl/k4_scalar_critical_path_terminal/ChartBudgets.lean. Original attribution is retained below.
-/
import Submission.Obl.k4_scalar_true_terminal_lifting.Step
import Submission.Obl.k4_quadratic_atlas_normalization.AssignmentMass

/-! Any actual root chart has one original full-prior reference budget,
independently of the number of its pieces. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ChartBudgets

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_scalar_true_terminal_lifting (ChartW)

/-- Use full original assigned priors, without restricting them to the
selected incidences or multiplying them by success probabilities. -/
theorem assignment_budget_le_one {p : Code} (hp : Exact p)
    {B k : ℕ} {r b h ε : ℝ} {flag : Bool} (Q : ChartW p B r b h ε flag k) :
    (∑ d, ENNReal.ofReal (ω p k (Q.γ d)) * ENNReal.ofReal (((2 : ℝ) ^ Q.T)⁻¹) *
      ν p k (Q.γ d) (Q.A d)) ≤ 1 := by
  have hbudget := Submission.Obl.k4_quadratic_atlas_normalization.weighted_assignment_budget_ofReal
    (ν p k) (ω p k) Q.γ Q.j Q.A
    (fun a => ((hp.2.1 k).2.2.2.1 a).1) (hp.2.1 k).2.1 (hp.2.1 k).2.2.1
    (fun d => (Q.hcd.2.2.1 d).1) Q.hcd.2.2.2.1
  calc
    _ = ENNReal.ofReal (((2 : ℝ) ^ Q.T)⁻¹) *
        ∑ d, ENNReal.ofReal (ω p k (Q.γ d)) * ν p k (Q.γ d) (Q.A d) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      ring
    _ ≤ ENNReal.ofReal (((2 : ℝ) ^ Q.T)⁻¹) *
        (Fintype.card (Fin (2 ^ Q.T)) : ENNReal) := mul_le_mul' le_rfl hbudget
    _ = 1 := by
      rw [← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (show 0 ≤ ((2 : ℝ) ^ Q.T)⁻¹ by positivity)]
      norm_num only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
      rw [inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)), ENNReal.ofReal_one]

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ChartBudgets
