import Mathlib

/-!
# A relation `P(z, w)` as a polynomial in its last variable

`lastVar P` writes `P : MvPolynomial (Fin (n + 1)) ℂ` as a polynomial in the last variable `w`
whose coefficients are polynomials in the first `n` variables `z`, and `lineRestrict P x z`
restricts it to the complex line `t ↦ x + t (z - x)`, as a polynomial in `w` whose coefficients
are polynomials in `t`.
-/

namespace Submission.Obl.k4_algebraic_sheet_bound

open MvPolynomial

/-- `P` as a polynomial in its last variable, with coefficients polynomials in the others. -/
noncomputable def lastVar {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℂ) :
    Polynomial (MvPolynomial (Fin n) ℂ) :=
  finSuccEquiv ℂ n (rename (finRotate (n + 1)) P)

theorem eval_snoc_eq_lastVar {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℂ) (z : Fin n → ℂ)
    (w : ℂ) :
    eval (Fin.snoc z w : Fin (n + 1) → ℂ) P = ((lastVar P).map (eval z)).eval w := by
  rw [lastVar, ← eval_eq_eval_mv_eval', eval_rename, Fin.snoc_eq_cons_rotate]
  rfl

theorem lastVar_ne_zero {n : ℕ} {P : MvPolynomial (Fin (n + 1)) ℂ} (hP : P ≠ 0) :
    lastVar P ≠ 0 := by
  intro h
  apply hP
  have h1 : rename (finRotate (n + 1)) P = 0 := by
    rw [lastVar] at h
    exact (finSuccEquiv ℂ n).injective (by rw [h, map_zero])
  exact rename_injective _ (finRotate (n + 1)).injective (by rw [h1, map_zero])

/-- The affine parametrization `t ↦ x + t (z - x)` of a coordinate as a polynomial in `t`. -/
noncomputable def linePoly {n : ℕ} (x z : Fin n → ℂ) (i : Fin n) : Polynomial ℂ :=
  Polynomial.C (x i) + Polynomial.X * Polynomial.C (z i - x i)

theorem eval_aeval_linePoly {n : ℕ} (x z : Fin n → ℂ) (a : MvPolynomial (Fin n) ℂ) (t : ℂ) :
    (aeval (linePoly x z) a).eval t = eval (fun i => x i + t * (z i - x i)) a := by
  rw [← Polynomial.coe_evalRingHom, aeval_eq_eval₂Hom, coe_eval₂Hom, eval₂_comp_left]
  simp only [eval]
  congr 1
  · ext r
    simp
  · ext i
    simp [linePoly]

/-- The relation restricted to the complex line `t ↦ x + t (z - x)`: a polynomial in `w` whose
coefficients are polynomials in `t`. -/
noncomputable def lineRestrict {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℂ) (x z : Fin n → ℂ) :
    Polynomial (Polynomial ℂ) :=
  (lastVar P).map (aeval (linePoly x z)).toRingHom

theorem lineRestrict_eval {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℂ) (x z : Fin n → ℂ)
    (t w : ℂ) :
    ((lineRestrict P x z).map (Polynomial.evalRingHom t)).eval w =
      eval (Fin.snoc (fun i => x i + t * (z i - x i)) w : Fin (n + 1) → ℂ) P := by
  rw [eval_snoc_eq_lastVar, lineRestrict, Polynomial.map_map]
  congr 2
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro i
    simp [linePoly]

theorem lineRestrict_leadingCoeff_eval_zero {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℂ)
    (x z : Fin n → ℂ) (h : eval x (lastVar P).leadingCoeff ≠ 0) :
    (lineRestrict P x z).leadingCoeff.eval 0 = eval x (lastVar P).leadingCoeff := by
  have hval : (aeval (linePoly x z) (lastVar P).leadingCoeff).eval 0 =
      eval x (lastVar P).leadingCoeff := by
    rw [eval_aeval_linePoly]
    simp
  have hne : (aeval (linePoly x z)).toRingHom (lastVar P).leadingCoeff ≠ 0 := by
    intro h0
    apply h
    rw [← hval]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h0
    rw [h0, Polynomial.eval_zero]
  rw [lineRestrict, Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hne]
  simpa using hval

end Submission.Obl.k4_algebraic_sheet_bound
