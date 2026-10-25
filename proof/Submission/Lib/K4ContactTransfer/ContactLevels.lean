import Mathlib
import Submission.Lib.K4ContactTransfer.ContactCommon

/-!
# Grid levels and scale comparisons of the zoomed instance

A zoomed depth `σ` uses the grid level `j = lev σ`, of original depth
`r + (j + 1) δ`; the gap `σ - (j + 1) δ` lies in `[0, δ]` on the used range.
The zoomed block length is the ratio of original block lengths, and the
zoomed widths `N^(-σ)`, `N^(-ℓσ)` differ from the original ratios by at most
`N^(δ)`-type factors.
-/

namespace Submission.Lib.K4ContactTransfer

open MeasureTheory Set Filter
open scoped ENNReal
open PreparedModel

noncomputable section

variable {α : Type} [MeasurableSpace α]

namespace ZoomInput

variable {p : Parameters} {a : PreparedModel α} {r : ℝ} (I : ZoomInput p a r)

/-- The grid gap of a used depth. -/
theorem lev_gap (hM : 0 < I.M) (hδ : 0 < I.δ) {σ : ℝ} (h1 : I.δ ≤ σ)
    (h2 : σ ≤ ((I.M : ℝ) + 1) * I.δ) :
    0 ≤ σ - (((I.lev hM σ : ℕ) : ℝ) + 1) * I.δ ∧
      σ - (((I.lev hM σ : ℕ) : ℝ) + 1) * I.δ ≤ I.δ := by
  have hσ0 : 0 ≤ σ := le_trans hδ.le h1
  set f := ⌊σ / I.δ⌋₊ with hf
  have hf1 : 1 ≤ f := by
    rw [hf]
    apply Nat.le_floor
    rw [Nat.cast_one, le_div_iff₀ hδ, one_mul]
    exact h1
  have hfl : (f : ℝ) ≤ σ / I.δ := Nat.floor_le (div_nonneg hσ0 hδ.le)
  have hfu : σ / I.δ < (f : ℝ) + 1 := Nat.lt_floor_add_one _
  have hfl' : (f : ℝ) * I.δ ≤ σ := by rwa [le_div_iff₀ hδ] at hfl
  have hfu' : σ < ((f : ℝ) + 1) * I.δ := by rwa [div_lt_iff₀ hδ] at hfu
  simp only [lev]
  rcases le_or_gt (I.M - 1) (f - 1) with hc | hc
  · rw [min_eq_left hc]
    have hcast : ((I.M - 1 : ℕ) : ℝ) + 1 = (I.M : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hcast]
    have hMf : (I.M : ℝ) ≤ (f : ℝ) := by
      have : I.M ≤ f := by omega
      exact_mod_cast this
    constructor
    · nlinarith
    · nlinarith
  · rw [min_eq_right hc.le]
    have hcast : ((f - 1 : ℕ) : ℝ) + 1 = (f : ℝ) := by
      rw [Nat.cast_sub hf1]; push_cast; ring
    rw [hcast]
    constructor
    · linarith
    · linarith

/-- The zoomed block length is the ratio of block lengths. -/
theorem zoom_q {j : Fin I.M} (x : I.Ret j) :
    (2 : ℝ) ^ (-((a.T I.k (I.depth j) - a.T I.k r : ℕ) : ℤ)) = a.q I.k (I.depth j) / a.q I.k r :=
  rel_length (level_le_of_interval_subset (I.block_sub x))

end ZoomInput

/-- Ratio of two powers of `N`. -/
theorem rpow_ratio {N x y : ℝ} (hN : 0 < N) : N ^ x / N ^ y = N ^ (x - y) := by
  rw [Real.rpow_sub hN]

/-- Comparison of `N^(-c u)` with `N^(-c σ)` for `σ - δ ≤ u ≤ σ`, `c ≥ 0`. -/
theorem rpow_neg_mul_le {N c u σ δ : ℝ} (hN : 1 ≤ N) (hc : 0 ≤ c) (h1 : u ≤ σ)
    (h2 : σ - δ ≤ u) :
    N ^ (-(c * σ)) ≤ N ^ (-(c * u)) ∧ N ^ (-(c * u)) ≤ N ^ (c * δ) * N ^ (-(c * σ)) := by
  have hN0 : 0 < N := by linarith
  constructor
  · apply Real.rpow_le_rpow_of_exponent_le hN; nlinarith
  · rw [← Real.rpow_add hN0]
    apply Real.rpow_le_rpow_of_exponent_le hN; nlinarith

end

end Submission.Lib.K4ContactTransfer
