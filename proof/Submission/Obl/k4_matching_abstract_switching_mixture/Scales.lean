import Mathlib

namespace Submission.Obl.k4_matching_abstract_switching_mixture

open Filter

/-- Fixed polynomial losses in the two input bounds fit into the output
subpower allowance after choosing a sufficiently small input exponent. -/
theorem absorb_polynomial (C : ℝ) (hC : 0 ≤ C) (n : ℕ) (hn : 1 ≤ n)
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ η : ℝ, 0 < η ∧ ∃ R : ℝ, 2 ≤ R ∧
      ∀ N B K : ℝ, R ≤ N → 1 ≤ B → B ≤ N ^ η → 1 ≤ K → K ≤ N ^ η →
        C * (B * K) ^ n ≤ N ^ κ := by
  let η : ℝ := κ / (4 * (n : ℝ))
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hη : 0 < η := div_pos hκ (by positivity)
  obtain ⟨R, hR⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (half_pos hκ)).eventually_ge_atTop C)
  refine ⟨η, hη, max 2 R, le_max_left _ _, ?_⟩
  intro N B K hN hB hBN hK hKN
  have hN2 : 2 ≤ N := le_trans (le_max_left _ _) hN
  have hN0 : 0 < N := by linarith
  have hCN : C ≤ N ^ (κ / 2) := hR N (le_trans (le_max_right _ _) hN)
  have hpow : (B * K) ^ n ≤ (N ^ η * N ^ η) ^ n := by
    apply pow_le_pow_left₀ (by positivity)
    exact mul_le_mul hBN hKN (by positivity) (by positivity)
  calc
    C * (B * K) ^ n ≤ N ^ (κ / 2) * (N ^ η * N ^ η) ^ n :=
      mul_le_mul hCN hpow (by positivity) (by positivity)
    _ = N ^ κ := by
      rw [← Real.rpow_add hN0, ← Real.rpow_mul_natCast hN0.le, ← Real.rpow_add hN0]
      congr 1
      dsimp [η]
      field_simp [ne_of_gt hn0]
      ring

end Submission.Obl.k4_matching_abstract_switching_mixture
