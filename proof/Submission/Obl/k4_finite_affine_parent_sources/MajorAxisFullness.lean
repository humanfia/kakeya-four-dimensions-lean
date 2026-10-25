-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.PathFullness
import Submission.Obl.k4_finite_affine_parent_sources.MajorFrame

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Submission.Lib.K4XInterface
open Submission.Obl.k4_compatible_pair_frame_preparation.Construction

noncomputable section

/-- Four coordinate projections compare the full absolute-entry sum to
the actual largest column scale. -/
theorem entrySum_le_four_major (Q : Matrix (Fin 2) (Fin 2) ℝ) :
    (∑ i : Fin 2, ∑ j : Fin 2, |Q i j|) ≤ 4 * r₁ Q := by
  have hcols := col_norm_le Q
  have h₀ (i : Fin 2) : |Q i 0| ≤ r₁ Q := by
    have h := (PiLp.norm_apply_le (col0 Q) i).trans hcols.1
    fin_cases i <;> simpa [col0, Real.norm_eq_abs] using h
  have h₁ (i : Fin 2) : |Q i 1| ≤ r₁ Q := by
    have h := (PiLp.norm_apply_le (col1 Q) i).trans hcols.2.1
    fin_cases i <;> simpa [col1, Real.norm_eq_abs] using h
  simp only [Fin.sum_univ_two]
  linarith [h₀ 0, h₀ 1, h₁ 0, h₁ 1]

/-- Keeping a label outside the original deficient-axis event supplies
the physical fullness needed for quantitative relative-frame geometry. -/
theorem PathData.major_fullness_of_not_deficient
    {W : ℕ} (p : PathData W) (b : Fin p.C) (ρ H : ℝ)
    (hH : 0 < H) (hbudget : 4 / H ≤ ρ * p.κ)
    (hkeep : ¬p.axisDeficient ρ b) :
    (((2 : ℝ) ^ p.T (p.lev b))⁻¹) / H ≤ r₁ (p.frame b) := by
  have hdef : ρ * p.κ / (2 : ℝ) ^ p.T (p.lev b) <
      ∑ i : Fin 2, ∑ j : Fin 2, |p.frame b i j| := lt_of_not_ge hkeep
  have hq : 0 < ((2 : ℝ) ^ p.T (p.lev b))⁻¹ := by positivity
  have hscaled := mul_le_mul_of_nonneg_right hbudget hq.le
  have hsum := entrySum_le_four_major (p.frame b)
  have heq : ρ * p.κ / (2 : ℝ) ^ p.T (p.lev b) =
      (ρ * p.κ) * ((2 : ℝ) ^ p.T (p.lev b))⁻¹ := by ring
  rw [heq] at hdef
  have hlo : 4 * (((2 : ℝ) ^ p.T (p.lev b))⁻¹ / H) ≤
      (ρ * p.κ) * ((2 : ℝ) ^ p.T (p.lev b))⁻¹ := by
    convert hscaled using 1 <;> ring
  linarith

/-- The original chart's size bound supplies the complementary physical
major-axis upper bound with the same full original assignment. -/
theorem PathData.Valid.major_upper
    {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {s : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (b : Fin p.C) (H : ℝ) (hκ : p.κ ≤ H) :
    r₁ (p.frame b) ≤ H * ((2 : ℝ) ^ p.T (p.lev b))⁻¹ := by
  have hsize := (hp.chart b).2.2.2.1
  calc
    _ ≤ ∑ i : Fin 2, ∑ j : Fin 2, |p.frame b i j| := r₁_le_entrySum _
    _ ≤ p.κ / (2 : ℝ) ^ p.T (p.lev b) := hsize
    _ ≤ H * ((2 : ℝ) ^ p.T (p.lev b))⁻¹ := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hκ (by positivity)

end

end Submission.Obl.k4_finite_affine_parent_sources
