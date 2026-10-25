-- Adapted from this LOT tree, o156, session x0524, commit86ade225;
-- Submission/Obl/k4_terminal_local_sheet_pairing/NormalizationMass.lean. Existing attribution comments are retained below.

import Mathlib

namespace Submission.Obl.k4_paired_test_normalization.NormalizationStep

open MeasureTheory

/-- Convert the finite weighted density budget to the real sublevel-loss bound. -/
theorem normalization_loss_budget {ι : Type*} [Fintype ι] (b : ι → ℝ)
    {A θ : ℝ} (hb : ∀ i, 0 ≤ b i) (hA : 0 ≤ A) (hθ : 0 ≤ θ)
    (hsum : ∑ i, b i ≤ A) (v : ENNReal) (hv : v ≠ ⊤) :
    2 * (∑ i, ENNReal.ofReal (b i) * (ENNReal.ofReal (128 * θ) * v)) ≤
      ENNReal.ofReal (2 * A * (128 * v.toReal * θ)) := by
  classical
  rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => hb i)]
  calc
    _ ≤ 2 * (ENNReal.ofReal A * (ENNReal.ofReal (128 * θ) * v)) := by
      gcongr <;> assumption
    _ = _ := by
      conv_lhs => rw [← ENNReal.ofReal_toReal hv]
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 128 * θ),
        ← ENNReal.ofReal_mul hA]
      have h2 : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by norm_num
      rw [h2, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring

/-- The fixed coverage margin pays for a finite normalization deletion without
changing the slack that defines the moving-frame coordinates. -/
theorem coverage_four_to_two {κ : ℝ} (hκ : 0 < κ) {old new loss : ENNReal}
    (hstart : ENNReal.ofReal (4 * κ⁻¹) ≤ old)
    (hdelete : old ≤ new + loss) (hloss : loss ≤ ENNReal.ofReal (2 * κ⁻¹)) :
    ENNReal.ofReal (2 * κ⁻¹) ≤ new := by
  have hh : ENNReal.ofReal (2 * κ⁻¹) + ENNReal.ofReal (2 * κ⁻¹) ≤
      new + ENNReal.ofReal (2 * κ⁻¹) := by
    calc
      _ = ENNReal.ofReal (4 * κ⁻¹) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
      _ ≤ old := hstart
      _ ≤ new + loss := hdelete
      _ ≤ _ := add_le_add le_rfl hloss
  exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp hh

end Submission.Obl.k4_paired_test_normalization.NormalizationStep
