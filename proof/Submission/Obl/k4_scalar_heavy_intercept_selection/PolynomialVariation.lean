/- Adapted from this LOT tree oai_074_kakeya_four_dimensions, obligation o231,
session x0798, branch x0798, commit fbdba9e7,
Submission/Obl/k4_scalar_capped_heavy_potential/PolynomialVariation.lean.
Earlier source credits are retained below. -/

import Submission.Lib.K4CubicTests.FinitePolynomialBounds
import Submission.Lib.K4PolynomialPotential.Coordinate

namespace Submission.Obl.k4_scalar_heavy_intercept_selection

open Set MeasureTheory MvPolynomial
open Submission.Lib.K4CubicTests Submission.Lib.K4PolynomialPotential

noncomputable section

/-- A common coefficient bound gives a common derivative bound on the
whole normalized coordinate box. -/
theorem polynomial_gradient_eval_bound (P : MvPolynomial (Fin 2) ℝ) (D : ℕ)
    (hD : P.totalDegree ≤ D) {A H : ℝ} (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hcoeff : ∀ m, |P.coeff m| ≤ H) (z : Fin 2 → ℝ) (hz : ∀ i, |z i| ≤ A)
    (i : Fin 2) :
    |eval z (pderiv i P)| ≤ (D + 1 : ℕ) * (max 1 (2 * A)) ^ D * ((D : ℝ) * H) := by
  have hdeg : (pderiv i P).totalDegree ≤ D :=
    (totalDegree_pderiv_le P i).trans ((Nat.sub_le _ _).trans hD)
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using
    finite_polynomial_eval_abs_le (pderiv i P) D hdeg A ((D : ℝ) * H) hA
      (by positivity) (finite_coeff_pderiv_abs_le_of_totalDegree P D hD H hH hcoeff i) z hz

/-- The mean-value bound on an arbitrary coordinate interval. -/
theorem coordinate_eval_oscillation (P : MvPolynomial (Fin 2) ℝ) (z : Fin 2 → ℝ)
    (i : Fin 2) {A E a b : ℝ}
    (ha : a ∈ Icc (-A) A) (hb : b ∈ Icc (-A) A)
    (hderiv : ∀ t ∈ Icc (-A) A, |eval (Function.update z i t) (pderiv i P)| ≤ E) :
    |eval (Function.update z i b) P - eval (Function.update z i a) P| ≤ E * |b - a| := by
  let q := coordinatePolynomialHom z i P
  have hbound : ∀ t ∈ Icc (-A) A, ‖q.derivative.eval t‖ ≤ E := by
    intro t ht
    dsimp only [q]
    rw [derivative_coordinatePolynomialHom, eval_coordinatePolynomialHom, Real.norm_eq_abs]
    exact hderiv t ht
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Icc (-A) A) (x := a) (y := b)
    (f := fun t => q.eval t) (f' := fun t => q.derivative.eval t)
    (fun t _ => (q.hasDerivAt t).hasDerivWithinAt) hbound (convex_Icc _ _) ha hb
  simpa only [q, eval_coordinatePolynomialHom, Real.norm_eq_abs] using h

/-- Fixed degree and coefficient bounds control the variation on a
normalized base cell. The displayed factor is polynomial in the box size. -/
theorem polynomial_eval_oscillation (P : MvPolynomial (Fin 2) ℝ) (D : ℕ)
    (hD : P.totalDegree ≤ D) {A H δ : ℝ} (hA : 0 ≤ A) (hH : 0 ≤ H) (hδ : 0 ≤ δ)
    (hcoeff : ∀ m, |P.coeff m| ≤ H) (x y : Fin 2 → ℝ)
    (hx : ∀ i, |x i| ≤ A) (hy : ∀ i, |y i| ≤ A) (hxy : ∀ i, |y i - x i| ≤ δ) :
    |eval y P - eval x P| ≤
      2 * ((D + 1 : ℕ) * (max 1 (2 * A)) ^ D * ((D : ℝ) * H)) * δ := by
  let C : ℝ := (D + 1 : ℕ) * (max 1 (2 * A)) ^ D * ((D : ℝ) * H)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have haxis (z : Fin 2 → ℝ) (hz : ∀ i, |z i| ≤ A) (i : Fin 2)
      (b : ℝ) (hb : |b| ≤ A) :
      |eval (Function.update z i b) P - eval z P| ≤ C * |b - z i| := by
    have h := coordinate_eval_oscillation P z i (E := C) (abs_le.mp (hz i)) (abs_le.mp hb) ?_
    · simpa only [Function.update_eq_self] using h
    · intro t ht
      apply polynomial_gradient_eval_bound P D hD hA hH hcoeff _ _ i
      intro j
      by_cases hji : j = i
      · subst j
        simpa using abs_le.mpr ht
      · simpa [hji] using hz j
  let z := Function.update x 0 (y 0)
  have hz : ∀ i, |z i| ≤ A := by
    intro i
    fin_cases i
    · simpa [z] using hy 0
    · simpa [z] using hx 1
  have h₀ := haxis x hx 0 (y 0) (hy 0)
  have h₁ := haxis z hz 1 (y 1) (hy 1)
  have heq : Function.update z 1 (y 1) = y := by
    ext i
    fin_cases i <;> simp [z]
  rw [heq] at h₁
  have h₀' : |eval z P - eval x P| ≤ C * δ := h₀.trans (mul_le_mul_of_nonneg_left (hxy 0) hC)
  have h₁' : |eval y P - eval z P| ≤ C * δ := h₁.trans
    (mul_le_mul_of_nonneg_left (by simpa [z] using hxy 1) hC)
  calc
    _ ≤ |eval y P - eval z P| + |eval z P - eval x P| := abs_sub_le _ _ _
    _ ≤ C * δ + C * δ := add_le_add h₁' h₀'
    _ = _ := by dsimp [C]; ring

/-- The variation factor is a fixed constant times one fixed power of
the common loss, so it can be inserted into the scale margins. -/
theorem polynomial_eval_oscillation_power_bound (P : MvPolynomial (Fin 2) ℝ) (D : ℕ)
    (hD : P.totalDegree ≤ D) {H δ : ℝ} (hH : 1 ≤ H) (hδ : 0 ≤ δ)
    (hcoeff : ∀ m, |P.coeff m| ≤ H) (x y : Fin 2 → ℝ)
    (hx : ∀ i, |x i| ≤ H) (hy : ∀ i, |y i| ≤ H) (hxy : ∀ i, |y i - x i| ≤ δ) :
    |eval y P - eval x P| ≤
      ((2 : ℝ) * (D + 1 : ℕ) * (2 : ℝ) ^ D * (D : ℝ)) * H ^ (D + 1) * δ := by
  have ht := polynomial_eval_oscillation P D hD (by linarith : 0 ≤ H)
    (by linarith : 0 ≤ H) hδ hcoeff x y hx hy hxy
  convert ht using 1
  rw [max_eq_right (by linarith : 1 ≤ 2 * H), mul_pow, pow_succ]
  ring

end
end Submission.Obl.k4_scalar_heavy_intercept_selection
