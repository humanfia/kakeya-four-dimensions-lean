import Submission.Lib.K4PolynomialPotential.Potential

/-!
Adapted from: here:o062
Original trajectory-fit proofs: x0212, commit 3c84dbd,
Submission/Obl/k4_scalar_mesh_projection/TrajectoryFits.lean.

Restriction of polynomial fields to affine scalar trajectories. Derivative
control on a whole block gives a single intercept fit on that same block.
-/

namespace Submission.Lib.K4PolynomialPotential

open MvPolynomial Set

noncomputable def scalarLineHom (u v : ℝ) :
    MvPolynomial (Fin 2) ℝ →ₐ[ℝ] Polynomial ℝ :=
  MvPolynomial.aeval ![Polynomial.X, Polynomial.C v * Polynomial.X + Polynomial.C u]

theorem eval_scalarLineHom (P : MvPolynomial (Fin 2) ℝ) (u v t : ℝ) :
    (scalarLineHom u v P).eval t = MvPolynomial.eval ![t, u + t * v] P := by
  change (MvPolynomial.eval₂ Polynomial.C
    ![Polynomial.X, Polynomial.C v * Polynomial.X + Polynomial.C u] P).eval t = _
  rw [Submission.Lib.K4PolynomialPotential.eval_polynomial_substitution]
  apply congrArg (fun x : Fin 2 → ℝ => MvPolynomial.eval x P)
  funext i
  fin_cases i <;> simp <;> ring

theorem natDegree_scalarLineHom_le (P : MvPolynomial (Fin 2) ℝ) (u v : ℝ) :
    (scalarLineHom u v P).natDegree ≤ P.totalDegree := by
  unfold scalarLineHom
  have hlin : ∀ i : Fin 2,
      (![Polynomial.X, Polynomial.C v * Polynomial.X + Polynomial.C u] i : Polynomial ℝ).natDegree ≤ 1 := by
    intro i
    fin_cases i
    · simp
    · exact Polynomial.natDegree_linear_le
  simpa only [Nat.mul_one] using MvPolynomial.aeval_natDegree_le P le_rfl _ hlin

theorem derivative_scalarLineHom (P : MvPolynomial (Fin 2) ℝ) (u v : ℝ) :
    (scalarLineHom u v P).derivative =
      scalarLineHom u v (pderiv 0 P) +
        Polynomial.C v * scalarLineHom u v (pderiv 1 P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [scalarLineHom]
  | add P Q hP hQ =>
    simp only [map_add, Polynomial.derivative_add, hP, hQ]
    ring
  | mul_X P i hP =>
    simp only [map_mul, Polynomial.derivative_mul, hP, pderiv_mul, map_add]
    fin_cases i <;> simp [scalarLineHom] <;> ring

theorem eval_derivative_scalarLineHom (P : MvPolynomial (Fin 2) ℝ) (u v t : ℝ) :
    (scalarLineHom u v P).derivative.eval t =
      MvPolynomial.eval ![t, u + t * v] (pderiv 0 P) +
        v * MvPolynomial.eval ![t, u + t * v] (pderiv 1 P) := by
  rw [derivative_scalarLineHom, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, eval_scalarLineHom, eval_scalarLineHom]

theorem scalar_residual_derivative_bound (P A B : MvPolynomial (Fin 2) ℝ)
    (S : Polynomial ℝ) (u v t : ℝ) {δ E₀ E₁ : ℝ}
    (hrow : |S.derivative.eval t - (MvPolynomial.eval ![t, u + t * v] A +
      v * MvPolynomial.eval ![t, u + t * v] B)| ≤ δ)
    (h₀ : |MvPolynomial.eval ![t, u + t * v] (pderiv 0 P) -
      MvPolynomial.eval ![t, u + t * v] A| ≤ E₀)
    (h₁ : |MvPolynomial.eval ![t, u + t * v] (pderiv 1 P) -
      MvPolynomial.eval ![t, u + t * v] B| ≤ E₁) :
    |(S - scalarLineHom u v P).derivative.eval t| ≤ δ + E₀ + |v| * E₁ := by
  let r : ℝ := S.derivative.eval t - (MvPolynomial.eval ![t, u + t * v] A +
    v * MvPolynomial.eval ![t, u + t * v] B)
  let e₀ : ℝ := MvPolynomial.eval ![t, u + t * v] (pderiv 0 P) -
    MvPolynomial.eval ![t, u + t * v] A
  let e₁ : ℝ := MvPolynomial.eval ![t, u + t * v] (pderiv 1 P) -
    MvPolynomial.eval ![t, u + t * v] B
  have hr : |r| ≤ δ := hrow
  have he₀ : |e₀| ≤ E₀ := h₀
  have he₁ : |e₁| ≤ E₁ := h₁
  have hid : (S - scalarLineHom u v P).derivative.eval t = r - e₀ - v * e₁ := by
    rw [Polynomial.derivative_sub, Polynomial.eval_sub, eval_derivative_scalarLineHom]
    dsimp [r, e₀, e₁]
    ring
  rw [hid]
  have h : |r - e₀ - v * e₁| ≤ |r - e₀| + |v * e₁| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (r - e₀) (-(v * e₁))
  have h' : |r - e₀| ≤ |r| + |e₀| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le r (-e₀)
  rw [abs_mul] at h
  have hm := mul_le_mul_of_nonneg_left he₁ (abs_nonneg v)
  linarith

/-- Whole-block row and gradient control gives a fit with the left-endpoint
residual as its explicit intercept. -/
theorem scalar_fit_of_row_gradient_bounds (P A B : MvPolynomial (Fin 2) ℝ)
    (S : Polynomial ℝ) (u v a q δ E₀ E₁ : ℝ)
    (hq : 0 ≤ q) (hδ : 0 ≤ δ) (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁)
    (hrow : ∀ t ∈ Icc a (a + q),
      |S.derivative.eval t - (MvPolynomial.eval ![t, u + t * v] A +
        v * MvPolynomial.eval ![t, u + t * v] B)| ≤ δ)
    (h₀ : ∀ t ∈ Icc a (a + q), |MvPolynomial.eval ![t, u + t * v] (pderiv 0 P) -
      MvPolynomial.eval ![t, u + t * v] A| ≤ E₀)
    (h₁ : ∀ t ∈ Icc a (a + q), |MvPolynomial.eval ![t, u + t * v] (pderiv 1 P) -
      MvPolynomial.eval ![t, u + t * v] B| ≤ E₁) :
    ∀ t ∈ Icc a (a + q),
      |(S.eval t - MvPolynomial.eval ![t, u + t * v] P) -
        (S.eval a - MvPolynomial.eval ![a, u + a * v] P)| ≤ q * (δ + E₀ + |v| * E₁) := by
  let r : Polynomial ℝ := S - scalarLineHom u v P
  have hder : ∀ t ∈ Icc a (a + q), ‖r.derivative.eval t‖ ≤ δ + E₀ + |v| * E₁ := by
    intro t ht
    simpa only [r, Real.norm_eq_abs] using
      scalar_residual_derivative_bound P A B S u v t (hrow t ht) (h₀ t ht) (h₁ t ht)
  have hC : 0 ≤ δ + E₀ + |v| * E₁ := by positivity
  have heval (t : ℝ) : r.eval t = S.eval t - MvPolynomial.eval ![t, u + t * v] P := by
    dsimp only [r]
    rw [Polynomial.eval_sub, eval_scalarLineHom]
  intro t ht
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Icc a (a + q)) (x := a) (y := t)
    (f := fun s => r.eval s) (f' := fun s => r.derivative.eval s)
    (fun s hs => (r.hasDerivAt s).hasDerivWithinAt) hder
    (convex_Icc _ _) (show a ∈ Icc a (a + q) by constructor <;> linarith) ht
  have h' : |r.eval t - r.eval a| ≤ (δ + E₀ + |v| * E₁) * |t - a| := by
    simpa only [Real.norm_eq_abs] using h
  have hlength : |t - a| ≤ q := by
    rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
    linarith [ht.2]
  rw [heval t, heval a] at h'
  exact h'.trans ((mul_le_mul_of_nonneg_left hlength hC).trans_eq (mul_comm _ _))

/-- For the constructed potential, the exact spatial row removes the
velocity factor from the gradient loss. -/
theorem scalar_potential_fit_on_block (A B : MvPolynomial (Fin 2) ℝ)
    (S : Polynomial ℝ) (u v a q δ E : ℝ)
    (hq : 0 ≤ q) (hδ : 0 ≤ δ) (hE : 0 ≤ E)
    (hcurl : ∀ z ∈ Icc (-1 : Fin 2 → ℝ) 1,
      |MvPolynomial.eval z (pderiv 0 B - pderiv 1 A)| ≤ E)
    (htraj : ∀ t ∈ Icc a (a + q), (![t, u + t * v] : Fin 2 → ℝ) ∈ Icc (-1) 1)
    (hrow : ∀ t ∈ Icc a (a + q),
      |S.derivative.eval t - (MvPolynomial.eval ![t, u + t * v] A +
        v * MvPolynomial.eval ![t, u + t * v] B)| ≤ δ) :
    ∀ t ∈ Icc a (a + q),
      |(S.eval t - MvPolynomial.eval ![t, u + t * v] (polynomialPotential A B)) -
        (S.eval a - MvPolynomial.eval ![a, u + a * v] (polynomialPotential A B))| ≤
        q * (δ + E) := by
  have h := scalar_fit_of_row_gradient_bounds (polynomialPotential A B) A B S
    u v a q δ E 0 hq hδ hE (by norm_num) hrow ?_ ?_
  · simpa only [mul_zero, add_zero] using h
  · intro t ht
    have hz := htraj t ht
    have herr := polynomialPotential_time_error_bound A B hcurl ![t, u + t * v] hz
    have hy : |u + t * v| ≤ 1 := by simpa using abs_le.mpr ⟨hz.1 1, hz.2 1⟩
    exact herr.trans (by simpa using mul_le_mul_of_nonneg_left hy hE)
  · intro t ht
    rw [polynomialPotential_spatial, sub_self, abs_zero]

end Submission.Lib.K4PolynomialPotential
