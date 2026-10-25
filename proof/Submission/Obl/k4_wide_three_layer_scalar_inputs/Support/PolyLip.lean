import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.Input

set_option linter.unusedVariables false

/-!
# Differences of the normalized predictor polynomials

`quadZ p x y + transv τ x y U` with coefficients bounded by `H` varies, on bounded arguments, by
explicit multiples of the argument differences; the nonconstant transverse coefficients of two
predictors vary along the base by explicit multiples as well.
-/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

noncomputable section

/-- The predictor polynomial in normalized coordinates. -/
def predQ (p : Fin 6 → ℝ) (τ : Fin 4 → ℝ) (x y U : ℝ) : ℝ := quadZ p x y + transv τ x y U

/-- The linear transverse coefficient at a base point. -/
def lin1 (τ : Fin 4 → ℝ) (x y : ℝ) : ℝ := τ 0 + τ 1 * x + τ 2 * y

theorem predQ_eq (p : Fin 6 → ℝ) (τ : Fin 4 → ℝ) (x y U : ℝ) :
    predQ p τ x y U = quadZ p x y + lin1 τ x y * U + τ 3 * U ^ 2 := by
  simp only [predQ, transv, lin1]; ring

theorem predQ_diff {p : Fin 6 → ℝ} {τ : Fin 4 → ℝ} {H X Y Ub : ℝ}
    (hp : ∀ e, |p e| ≤ H) (hτ : ∀ e, |τ e| ≤ H) {x y U x' y' U' : ℝ}
    (hx : |x| ≤ X) (hx' : |x'| ≤ X) (hy : |y| ≤ Y) (hy' : |y'| ≤ Y) (hU : |U| ≤ Ub)
    (hU' : |U'| ≤ Ub) :
    |predQ p τ x y U - predQ p τ x' y' U'| ≤
      H * ((1 + 2 * X + Y + Ub) * |x - x'| + (1 + X + 2 * Y + Ub) * |y - y'| +
        (1 + X + Y + 2 * Ub) * |U - U'|) := by
  have hH : 0 ≤ H := (abs_nonneg _).trans (hp 0)
  have hX : 0 ≤ X := (abs_nonneg _).trans hx
  have hY : 0 ≤ Y := (abs_nonneg _).trans hy
  have hUb : 0 ≤ Ub := (abs_nonneg _).trans hU
  have hid : predQ p τ x y U - predQ p τ x' y' U' =
      p 1 * (x - x') + p 2 * (y - y') + p 3 * ((x + x') * (x - x')) +
      p 4 * (x * (y - y') + y' * (x - x')) + p 5 * ((y + y') * (y - y')) +
      (τ 0 * (U - U') + τ 1 * (x * (U - U') + U' * (x - x')) +
        τ 2 * (y * (U - U') + U' * (y - y')) + τ 3 * ((U + U') * (U - U'))) := by
    simp only [predQ, quadZ, transv]; ring
  rw [hid]
  set a := |x - x'|
  set b := |y - y'|
  set c := |U - U'|
  have h1 : |p 1 * (x - x')| ≤ H * a := by rw [abs_mul]; gcongr; exact hp 1
  have h2 : |p 2 * (y - y')| ≤ H * b := by rw [abs_mul]; gcongr; exact hp 2
  have h3 : |p 3 * ((x + x') * (x - x'))| ≤ H * (2 * X * a) := by
    rw [abs_mul, abs_mul]
    gcongr
    · exact hp 3
    · calc |x + x'| ≤ |x| + |x'| := abs_add_le _ _
        _ ≤ 2 * X := by linarith
  have h4 : |p 4 * (x * (y - y') + y' * (x - x'))| ≤ H * (X * b + Y * a) := by
    rw [abs_mul]
    gcongr
    · exact hp 4
    · calc |x * (y - y') + y' * (x - x')| ≤ |x| * b + |y'| * a := by
            refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_mul]
        _ ≤ X * b + Y * a := by gcongr
  have h5 : |p 5 * ((y + y') * (y - y'))| ≤ H * (2 * Y * b) := by
    rw [abs_mul, abs_mul]
    gcongr
    · exact hp 5
    · calc |y + y'| ≤ |y| + |y'| := abs_add_le _ _
        _ ≤ 2 * Y := by linarith
  have h6 : |τ 0 * (U - U')| ≤ H * c := by rw [abs_mul]; gcongr; exact hτ 0
  have h7 : |τ 1 * (x * (U - U') + U' * (x - x'))| ≤ H * (X * c + Ub * a) := by
    rw [abs_mul]
    gcongr
    · exact hτ 1
    · calc |x * (U - U') + U' * (x - x')| ≤ |x| * c + |U'| * a := by
            refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_mul]
        _ ≤ X * c + Ub * a := by gcongr
  have h8 : |τ 2 * (y * (U - U') + U' * (y - y'))| ≤ H * (Y * c + Ub * b) := by
    rw [abs_mul]
    gcongr
    · exact hτ 2
    · calc |y * (U - U') + U' * (y - y')| ≤ |y| * c + |U'| * b := by
            refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_mul]
        _ ≤ Y * c + Ub * b := by gcongr
  have h9 : |τ 3 * ((U + U') * (U - U'))| ≤ H * (2 * Ub * c) := by
    rw [abs_mul, abs_mul]
    gcongr
    · exact hτ 3
    · calc |U + U'| ≤ |U| + |U'| := abs_add_le _ _
        _ ≤ 2 * Ub := by linarith
  have htri : ∀ a b c d e f g h i : ℝ, |a + b + c + d + e + (f + g + h + i)| ≤
      |a| + |b| + |c| + |d| + |e| + |f| + |g| + |h| + |i| := by
    intro a b c d e f g h i
    have := abs_add_le (a + b + c + d + e) (f + g + h + i)
    have := abs_add_le (a + b + c + d) e
    have := abs_add_le (a + b + c) d
    have := abs_add_le (a + b) c
    have := abs_add_le a b
    have := abs_add_le (f + g + h) i
    have := abs_add_le (f + g) h
    have := abs_add_le f g
    linarith
  refine (htri _ _ _ _ _ _ _ _ _).trans ?_
  nlinarith [h1, h2, h3, h4, h5, h6, h7, h8, h9]

theorem lin1_diff {τ τ' : Fin 4 → ℝ} {H : ℝ} (hτ : ∀ e, |τ e| ≤ H) (hτ' : ∀ e, |τ' e| ≤ H)
    (x y x' y' : ℝ) :
    |(lin1 τ x y - lin1 τ' x y) - (lin1 τ x' y' - lin1 τ' x' y')| ≤
      2 * H * (|x - x'| + |y - y'|) := by
  have hid : (lin1 τ x y - lin1 τ' x y) - (lin1 τ x' y' - lin1 τ' x' y') =
      (τ 1 - τ' 1) * (x - x') + (τ 2 - τ' 2) * (y - y') := by simp only [lin1]; ring
  rw [hid]
  have hd : ∀ e, |τ e - τ' e| ≤ 2 * H := fun e =>
    (abs_sub _ _).trans (by linarith [hτ e, hτ' e])
  calc _ ≤ |τ 1 - τ' 1| * |x - x'| + |τ 2 - τ' 2| * |y - y'| := by
        refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_mul]
    _ ≤ 2 * H * |x - x'| + 2 * H * |y - y'| := by gcongr <;> exact hd _
    _ = _ := by ring

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
