/- Adapted from this LOT tree, obligation o200, session x0934, commit 2510f40626244312a0552650c06c57bcfd48d368,
   Submission/Obl/k4_finite_projected_horizontal_candidates/ReferenceNumerators.lean.
   Namespace renamed from Submission.Obl.k4_finite_projected_horizontal_candidates to Submission.Obl.k4_narrow_projected_row_parents.Cmp; earlier source attributions retained. -/
import Mathlib

/-! Exact real reference numerators from finite original palette budgets. -/

namespace Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison

open scoped ENNReal

noncomputable section

/-- The matching estimate uses real weights. Converting a finite original
palette budget to those weights preserves the numerator exactly. -/
theorem real_reference_budget {ι : Type*} [Fintype ι]
    (T : ι → ℝ) (hT : ∀ i, 0 ≤ T i) (palette : ι → ℝ≥0∞)
    (hp : ∀ i, palette i ≠ ⊤) {B : ℝ} (hB : 0 ≤ B) (mass : ℝ≥0∞) (hmass : mass ≠ ⊤)
    (hbound : (∑ i, ENNReal.ofReal (T i) * palette i) ≤ ENNReal.ofReal B * mass) :
    (∑ i, T i * (palette i).toReal) ≤ B * mass.toReal := by
  have hsum : (∑ i, ENNReal.ofReal (T i) * palette i) =
      ENNReal.ofReal (∑ i, T i * (palette i).toReal) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hT i) ENNReal.toReal_nonneg)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [ENNReal.ofReal_mul (hT i), ENNReal.ofReal_toReal (hp i)]
  have hright : ENNReal.ofReal B * mass = ENNReal.ofReal (B * mass.toReal) := by
    rw [ENNReal.ofReal_mul hB, ENNReal.ofReal_toReal hmass]
  rw [hsum, hright] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hB ENNReal.toReal_nonneg)).mp hbound

/-- Both colors' original cutoff costs are exactly the real reference numerator
divided by the pruning parameter. The original palette is unchanged. -/
theorem two_color_reference_cutoff {ι : Type*} [Fintype ι]
    (n₁ n₂ : ι → ℕ) (T : ι → ℝ) (hT : ∀ i, 0 ≤ T i)
    (palette : ι → ℝ≥0∞) (hp : ∀ i, palette i ≠ ⊤) {F : ℝ} (hF : 0 < F) :
    (∑ i, ((n₁ i : ℝ≥0∞) * (ENNReal.ofReal (T i / F) * palette i) +
      (n₂ i : ℝ≥0∞) * (ENNReal.ofReal (T i / F) * palette i))) =
    ENNReal.ofReal ((∑ i, ((n₁ i : ℝ) * (T i * (palette i).toReal) +
      (n₂ i : ℝ) * (T i * (palette i).toReal))) / F) := by
  have hterm (i : ι) (n : ℕ) :
      (n : ℝ≥0∞) * (ENNReal.ofReal (T i / F) * palette i) =
      ENNReal.ofReal (((n : ℝ) * (T i * (palette i).toReal)) / F) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_toReal (hp i),
      ← ENNReal.ofReal_mul (div_nonneg (hT i) hF.le),
      ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
    rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
    congr 1
    ring
  calc
    _ = ∑ i, ENNReal.ofReal (((n₁ i : ℝ) * (T i * (palette i).toReal) +
        (n₂ i : ℝ) * (T i * (palette i).toReal)) / F) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hTi := hT i
      rw [hterm i (n₁ i), hterm i (n₂ i), ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    _ = _ := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by
        have hTi := hT i
        positivity), Finset.sum_div]

end

end Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison
