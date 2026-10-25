import Submission.Obl.k4_coarsened_outer_horizon_composition.BinRange
import Submission.Obl.k4_scalar_true_atlas_terminal_lists.BinBounds

namespace Submission.Obl.k4_coarsened_outer_horizon_composition

/-- A single fixed exponent absorbs the nine tests for each chart and every
native hidden-coordinate bin, together with the original selected-event format. -/
theorem native_cut_format_budget {N : ℝ} {C : ℕ} (hN : 2 ≤ N)
    (M Mb n : ℕ) (hC : (C : ℝ) ≤ N ^ M) :
    N ^ M + ((polynomialBins N (M + Mb + n + 2)).card : ℝ) * (2 + (C : ℝ) * 9) ≤
      N ^ ((M + 1) + (M + Mb + n + 2) + 12) := by
  have hN1 : 1 ≤ N := by linarith
  have hcard := polynomialBins_card hN (M + Mb + n + 2)
  have hcard' : ((polynomialBins N (M + Mb + n + 2)).card : ℝ) ≤
      N ^ ((M + Mb + n + 2) + 5) :=
    hcard.trans (pow_le_pow_right₀ hN1 (by omega))
  have htwice : 2 * (C : ℝ) ≤ N ^ (M + 1) := by
    calc
      _ ≤ N * N ^ M := mul_le_mul hN hC (Nat.cast_nonneg _) (by positivity)
      _ = _ := by rw [pow_succ]; ring
  have hbudget := Submission.Obl.k4_scalar_true_atlas_terminal_lists.crossing_atom_budget
    hN hcard' (Nat.cast_nonneg _) htwice (by positivity : 0 ≤ 2 * (C : ℝ))
  apply le_trans _ hbudget
  apply add_le_add (pow_le_pow_right₀ hN1 (by omega))
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  nlinarith [show (0 : ℝ) ≤ C from Nat.cast_nonneg C]

end Submission.Obl.k4_coarsened_outer_horizon_composition
