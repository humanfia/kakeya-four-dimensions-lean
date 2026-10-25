import Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets.Basic

/-!
# Covering a scalar strip by squares

The set `{(x, y) : x - f y ∈ [s₀, s₀ + q), |y - y₀| ≤ L}` with `|f| ≤ K` is covered by the
`(⌊2L/q⌋ + 1) (⌊2K⌋ + 2)` squares `[a j + i q, a j + i q + q) × [b j, b j + q)` with
`b j = y₀ - L + j q` and `a j = s₀ + f (b j) - |f| q`.
-/

namespace Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets

open Set

noncomputable section

/-- Row offsets of the square cover. -/
def paraB (y₀ L q : ℝ) (j : ℕ) : ℝ := y₀ - L + j * q

/-- Column offsets of the square cover. -/
def paraA (s₀ f y₀ L q : ℝ) (j : ℕ) : ℝ := s₀ + f * paraB y₀ L q j - |f| * q

theorem para_cover {q L f s₀ y₀ K x y : ℝ} (hq : 0 < q) (hf : |f| ≤ K)
    (hs1 : s₀ ≤ x - f * y) (hs2 : x - f * y < s₀ + q) (hy : |y - y₀| ≤ L) :
    ∃ j < ⌊2 * L / q⌋₊ + 1, ∃ i < ⌊2 * K⌋₊ + 2,
      x ∈ Ico (paraA s₀ f y₀ L q j + i * q) (paraA s₀ f y₀ L q j + i * q + q) ∧
        y ∈ Ico (paraB y₀ L q j) (paraB y₀ L q j + q) := by
  have hyb : 0 ≤ y - (y₀ - L) := by rw [abs_le] at hy; linarith
  set j : ℕ := ⌊(y - (y₀ - L)) / q⌋₊ with hj
  have hj1 : (j : ℝ) ≤ (y - (y₀ - L)) / q := Nat.floor_le (div_nonneg hyb hq.le)
  have hj2 : (y - (y₀ - L)) / q < j + 1 := Nat.lt_floor_add_one _
  have hjy1 : paraB y₀ L q j ≤ y := by
    have := (le_div_iff₀ hq).mp hj1
    simp only [paraB]; linarith
  have hjy2 : y < paraB y₀ L q j + q := by
    have := (div_lt_iff₀ hq).mp hj2
    simp only [paraB]; nlinarith
  have hjn : j < ⌊2 * L / q⌋₊ + 1 := by
    have h2 : (y - (y₀ - L)) / q ≤ 2 * L / q := by
      apply div_le_div_of_nonneg_right _ hq.le
      rw [abs_le] at hy; linarith
    have : j ≤ ⌊2 * L / q⌋₊ := Nat.floor_mono h2
    omega
  set b := paraB y₀ L q j
  have hdy0 : 0 ≤ y - b := by linarith
  have hdyq : y - b < q := by linarith
  have habs : |f * (y - b)| ≤ |f| * q := by
    rw [abs_mul, abs_of_nonneg hdy0]; gcongr
  have hFy1 : -(|f| * q) ≤ f * (y - b) := by linarith [neg_abs_le (f * (y - b))]
  have hFy2 : f * (y - b) ≤ |f| * q := by linarith [le_abs_self (f * (y - b))]
  set a := paraA s₀ f y₀ L q j
  have ha : a = s₀ + f * b - |f| * q := rfl
  have hxa0 : 0 ≤ x - a := by rw [ha]; nlinarith
  have hxa1 : x - a < q * (1 + 2 * K) := by rw [ha]; nlinarith
  set i : ℕ := ⌊(x - a) / q⌋₊ with hi
  have hi1 : (i : ℝ) ≤ (x - a) / q := Nat.floor_le (div_nonneg hxa0 hq.le)
  have hi2 : (x - a) / q < i + 1 := Nat.lt_floor_add_one _
  have hin : i < ⌊2 * K⌋₊ + 2 := by
    have h1 : (x - a) / q < 1 + 2 * K := by rw [div_lt_iff₀ hq]; linarith
    have h3 : 2 * K < ⌊2 * K⌋₊ + 1 := Nat.lt_floor_add_one _
    have h4 : (i : ℝ) < (⌊2 * K⌋₊ : ℝ) + 2 := by linarith
    exact_mod_cast h4
  refine ⟨j, hjn, i, hin, ⟨?_, ?_⟩, hjy1, hjy2⟩
  · have := (le_div_iff₀ hq).mp hi1; linarith
  · have := (div_lt_iff₀ hq).mp hi2; nlinarith

theorem para_rows_le {L q : ℝ} (hq : 0 < q) (hL : 0 ≤ L) :
    ((⌊2 * L / q⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * L / q + 1 := by
  push_cast; linarith [Nat.floor_le (by positivity : (0:ℝ) ≤ 2 * L / q)]

theorem para_cols_le {K : ℝ} (hK : 0 ≤ K) : ((⌊2 * K⌋₊ + 2 : ℕ) : ℝ) ≤ 2 * K + 2 := by
  push_cast; linarith [Nat.floor_le (by positivity : (0:ℝ) ≤ 2 * K)]

end

end Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets
