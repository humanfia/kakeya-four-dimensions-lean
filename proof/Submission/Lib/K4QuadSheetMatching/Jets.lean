import Mathlib
import Submission.Lib.K4QuadSheetMatching.Basic
-- Adapted from: here:o078 (session x0262, branch x0262 of o078).

/-!
# Jets of quadratic sheets and their line restrictions

A version-1 sheet is a quadratic `qev c t y` in the base variables. If a difference of two
sheets is tiny at a point of the unit square but not small on the whole square, then one of
five fixed directional derivatives (first order along `e₁`, `e₂`; second order along `e₁`,
`e₂`, `e₁ + e₂`) is large at that point. Along each of the three directions the sheets restrict
to one-variable quadratics whose iterated derivatives are these directional derivatives.
This is the version-1 form of the jet selection in the paper's local graph matching
(Corollary 3.4).
-/

namespace Submission.Lib.K4QuadSheetMatching

open Set

/-- The quadratic with coefficient vector `c`. -/
def qev (c : Fin 6 → ℝ) (t y : ℝ) : ℝ :=
  c 0 + c 1 * t + c 2 * y + c 3 * t ^ 2 + c 4 * (t * y) + c 5 * y ^ 2

/-- First derivative in `t`. -/
def qdt (c : Fin 6 → ℝ) (t y : ℝ) : ℝ := c 1 + 2 * c 3 * t + c 4 * y
/-- First derivative in `y`. -/
def qdy (c : Fin 6 → ℝ) (t y : ℝ) : ℝ := c 2 + c 4 * t + 2 * c 5 * y
/-- Second derivative in `t`. -/
def qdtt (c : Fin 6 → ℝ) : ℝ := 2 * c 3
/-- Second derivative in `y`. -/
def qdyy (c : Fin 6 → ℝ) : ℝ := 2 * c 5
/-- Second derivative along `e₁ + e₂`. -/
def qddd (c : Fin 6 → ℝ) : ℝ := 2 * c 3 + 2 * c 4 + 2 * c 5

lemma qev_sub (c c' : Fin 6 → ℝ) (t y : ℝ) : qev (c - c') t y = qev c t y - qev c' t y := by
  simp only [qev, Pi.sub_apply]; ring

lemma qdt_sub (c c' : Fin 6 → ℝ) (t y : ℝ) : qdt (c - c') t y = qdt c t y - qdt c' t y := by
  simp only [qdt, Pi.sub_apply]; ring

lemma qdy_sub (c c' : Fin 6 → ℝ) (t y : ℝ) : qdy (c - c') t y = qdy c t y - qdy c' t y := by
  simp only [qdy, Pi.sub_apply]; ring

lemma qdtt_sub (c c' : Fin 6 → ℝ) : qdtt (c - c') = qdtt c - qdtt c' := by
  simp only [qdtt, Pi.sub_apply]; ring

lemma qdyy_sub (c c' : Fin 6 → ℝ) : qdyy (c - c') = qdyy c - qdyy c' := by
  simp only [qdyy, Pi.sub_apply]; ring

lemma qddd_sub (c c' : Fin 6 → ℝ) : qddd (c - c') = qddd c - qddd c' := by
  simp only [qddd, Pi.sub_apply]; ring

/-- **Jet bound.** On the unit square a quadratic is bounded by its value and its five
directional derivatives at any point of the square. -/
lemma abs_qev_le_jet (e : Fin 6 → ℝ) {t₀ y₀ t y : ℝ} (ht : |t - t₀| ≤ 1) (hy : |y - y₀| ≤ 1) :
    |qev e t y| ≤ |qev e t₀ y₀| + |qdt e t₀ y₀| + |qdy e t₀ y₀| + |qdtt e| + |qdyy e| +
      |qddd e| := by
  set a := t - t₀
  set b := y - y₀
  have hTaylor : qev e t y = qev e t₀ y₀ + qdt e t₀ y₀ * a + qdy e t₀ y₀ * b +
      qdtt e / 2 * a ^ 2 + (qddd e - qdtt e - qdyy e) / 2 * (a * b) + qdyy e / 2 * b ^ 2 := by
    simp only [qev, qdt, qdy, qdtt, qdyy, qddd, a, b]; ring
  have ha2 : a ^ 2 ≤ 1 := by
    have := abs_le.mp ht; nlinarith
  have hb2 : b ^ 2 ≤ 1 := by
    have := abs_le.mp hy; nlinarith
  have hab : |a * b| ≤ 1 := by
    rw [abs_mul]; exact mul_le_one₀ ht (abs_nonneg _) hy
  have e1 : |qdt e t₀ y₀ * a| ≤ |qdt e t₀ y₀| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) ht
  have e2 : |qdy e t₀ y₀ * b| ≤ |qdy e t₀ y₀| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) hy
  have e3 : |qdtt e / 2 * a ^ 2| ≤ |qdtt e| / 2 := by
    rw [abs_mul, abs_div, abs_of_nonneg (sq_nonneg a)]; norm_num
    exact mul_le_of_le_one_right (by positivity) ha2
  have e5 : |qdyy e / 2 * b ^ 2| ≤ |qdyy e| / 2 := by
    rw [abs_mul, abs_div, abs_of_nonneg (sq_nonneg b)]; norm_num
    exact mul_le_of_le_one_right (by positivity) hb2
  have e4 : |(qddd e - qdtt e - qdyy e) / 2 * (a * b)| ≤
      (|qddd e| + |qdtt e| + |qdyy e|) / 2 := by
    have hX : |qddd e - qdtt e - qdyy e| ≤ |qddd e| + |qdtt e| + |qdyy e| := by
      calc |qddd e - qdtt e - qdyy e| ≤ |qddd e - qdtt e| + |qdyy e| := abs_sub _ _
        _ ≤ |qddd e| + |qdtt e| + |qdyy e| := by linarith [abs_sub (qddd e) (qdtt e)]
    calc |(qddd e - qdtt e - qdyy e) / 2 * (a * b)|
        = |qddd e - qdtt e - qdyy e| / 2 * |a * b| := by rw [abs_mul, abs_div, abs_two]
      _ ≤ |qddd e - qdtt e - qdyy e| / 2 * 1 := mul_le_mul_of_nonneg_left hab (by positivity)
      _ ≤ _ := by linarith
  rw [hTaylor]
  have := abs_add_three (qev e t₀ y₀ + qdt e t₀ y₀ * a + qdy e t₀ y₀ * b)
    (qdtt e / 2 * a ^ 2) ((qddd e - qdtt e - qdyy e) / 2 * (a * b))
  have h3 := abs_add_three (qev e t₀ y₀) (qdt e t₀ y₀ * a) (qdy e t₀ y₀ * b)
  calc _ ≤ |qev e t₀ y₀ + qdt e t₀ y₀ * a + qdy e t₀ y₀ * b + qdtt e / 2 * a ^ 2 +
        (qddd e - qdtt e - qdyy e) / 2 * (a * b)| + |qdyy e / 2 * b ^ 2| := abs_add_le _ _
    _ ≤ _ := by linarith [abs_nonneg (qdtt e), abs_nonneg (qdyy e), abs_nonneg (qddd e)]

/-- The five jet quantities of a coefficient vector at a point. -/
def jetq (e : Fin 6 → ℝ) (t y : ℝ) : Fin 5 → ℝ :=
  ![|qdt e t y|, |qdy e t y|, |qdtt e|, |qdyy e|, |qddd e|]

/-- **Jet selection.** If the quadratic is at most `θ` at `(t₀, y₀)` and at least `r` at some
point of the unit square, one of the five jet quantities at `(t₀, y₀)` is at least
`(r - θ) / 5`. -/
lemma exists_large_jet (e : Fin 6 → ℝ) {t₀ y₀ t y θ r : ℝ}
    (h₀ : (t₀, y₀) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) (h : (t, y) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
    (hθ : |qev e t₀ y₀| ≤ θ) (hr : r ≤ |qev e t y|) :
    ∃ k : Fin 5, (r - θ) / 5 ≤ jetq e t₀ y₀ k := by
  have ht : |t - t₀| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [h.1.1, h.1.2, h₀.1.1, h₀.1.2]
  have hy : |y - y₀| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [h.2.1, h.2.2, h₀.2.1, h₀.2.2]
  have hj := abs_qev_le_jet e ht hy
  by_contra hcon
  push Not at hcon
  have h0 := hcon 0; have h1 := hcon 1; have h2 := hcon 2; have h3 := hcon 3; have h4 := hcon 4
  simp only [jetq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three, Matrix.cons_val_four] at h0 h1 h2 h3 h4
  linarith

end Submission.Lib.K4QuadSheetMatching
