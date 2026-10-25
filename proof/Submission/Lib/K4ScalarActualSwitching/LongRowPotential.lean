/-
Adapted from: here:o062
Original proof: session x0212, branch x0212, commit 514fed9ca7cc96e045a817f747bad2429ad3ea3f,
Submission/Obl/k4_scalar_mesh_projection/LongRowPotential.lean.
The conditional and switching primitives are imported from the accepted
K4ScalarSwitching contribution, rather than copied.
-/

import Submission.Lib.K4ScalarActualSwitching.LongRowFits

namespace Submission.Lib.K4ScalarActualSwitching

open Set MeasureTheory MvPolynomial
open Submission.Lib.K4PolynomialPotential

/-- An intercept specified by the original trajectory and the common
potential, with no measurable choice of a good time point. -/
noncomputable def potentialLineQuadratic (P : MvPolynomial (Fin 2) ℝ)
    (S : Polynomial ℝ) (u : ℝ) : Polynomial ℝ :=
  S - Polynomial.C (S.eval 0 - eval ![0, u] P)

theorem natDegree_potentialLineQuadratic (P : MvPolynomial (Fin 2) ℝ)
    (S : Polynomial ℝ) (u : ℝ) (hS : S.natDegree ≤ 2) :
    (potentialLineQuadratic P S u).natDegree ≤ 2 := by
  exact (Polynomial.natDegree_sub_le _ _).trans (max_le hS (by simp))

/-- Polynomial qualification only on the original long row suffices for
a whole-time potential fit: Remez extends the residual derivative before
integration. Nothing is asserted about the field away from the row. -/
theorem potential_fit_of_long_row_gradient_bounds
    (P A B : MvPolynomial (Fin 2) ℝ) (D : ℕ) (hP : P.totalDegree ≤ D)
    (S : Polynomial ℝ) (hS : S.natDegree ≤ 2) (u v : ℝ)
    (R : Set ℝ) {η δ E₀ E₁ : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hδ : 0 ≤ δ) (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁)
    (hR : R ⊆ Icc (-1 : ℝ) 1) (hmass : ENNReal.ofReal η ≤ volume R)
    (hrow : ∀ t ∈ R, |S.derivative.eval t - (eval ![t, u + t * v] A +
      v * eval ![t, u + t * v] B)| ≤ δ)
    (h₀ : ∀ t ∈ R, |eval ![t, u + t * v] (pderiv 0 P) -
      eval ![t, u + t * v] A| ≤ E₀)
    (h₁ : ∀ t ∈ R, |eval ![t, u + t * v] (pderiv 1 P) -
      eval ![t, u + t * v] B| ≤ E₁) :
    ∀ t ∈ Icc (-1 : ℝ) 1,
      |eval ![t, u + t * v] P - (potentialLineQuadratic P S u).eval t| ≤
        (16 * ((D : ℝ) + 3) / η) ^ (D + 2) * (δ + E₀ + |v| * E₁) := by
  let r : Polynomial ℝ := S - scalarLineHom u v P
  have hr : r.natDegree ≤ D + 2 := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    exact max_le (hS.trans (Nat.le_add_left _ _))
      ((natDegree_scalarLineHom_le P u v).trans (hP.trans (Nat.le_add_right _ _)))
  have hdr : r.derivative.natDegree ≤ D + 2 :=
    (Polynomial.natDegree_derivative_le r).trans ((Nat.sub_le _ _).trans hr)
  have hrowBound : ∀ t ∈ R, |r.derivative.eval t| ≤ δ + E₀ + |v| * E₁ := by
    intro t ht
    exact scalar_residual_derivative_bound P A B S u v t (hrow t ht) (h₀ t ht) (h₁ t ht)
  let C := (16 * ((D : ℝ) + 3) / η) ^ (D + 2) * (δ + E₀ + |v| * E₁)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hder : ∀ t ∈ Icc (-1 : ℝ) 1, |r.derivative.eval t| ≤ C := by
    have h := polynomial_remez_signed_interval r.derivative (D + 2) hdr R hη hη1
      (by positivity : 0 ≤ δ + E₀ + |v| * E₁) hR hmass hrowBound
    simpa only [C, Nat.cast_add, Nat.cast_ofNat, add_assoc,
      show (2 : ℝ) + 1 = 3 by norm_num] using h
  intro t ht
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Icc (-1 : ℝ) 1) (x := 0) (y := t)
    (f := fun s => r.eval s) (f' := fun s => r.derivative.eval s)
    (fun s _ => (r.hasDerivAt s).hasDerivWithinAt)
    (fun s hs => by simpa only [Real.norm_eq_abs] using hder s hs)
    (convex_Icc _ _) (by norm_num) ht
  have hfit : |r.eval t - r.eval 0| ≤ C := by
    have h' : |r.eval t - r.eval 0| ≤ C * |t| := by
      simpa only [Real.norm_eq_abs, sub_zero] using h
    exact h'.trans ((mul_le_mul_of_nonneg_left (abs_le.mpr ht) hC).trans_eq (mul_one C))
  have hid : eval ![t, u + t * v] P - (potentialLineQuadratic P S u).eval t =
      -(r.eval t - r.eval 0) := by
    dsimp only [potentialLineQuadratic, r]
    simp only [Polynomial.eval_sub, Polynomial.eval_C, eval_scalarLineHom, zero_mul, add_zero]
    ring
  rw [hid, abs_neg]
  exact hfit

end Submission.Lib.K4ScalarActualSwitching
