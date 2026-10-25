import Submission.Obl.k4_sign_projection.ParametricIndex

namespace Submission.Obl.k4_sign_projection

open Polynomial
open scoped BigOperators

variable {ι α : Type}

/-- Finite tests can always be indexed by `Fin n`. -/
lemma SignDetermined.fin {f : (ι → ℝ) → α} (hf : SignDetermined f) :
    ∃ (n : ℕ) (q : Fin n → MvPolynomial ι ℝ), ∀ x y,
      (fun i => SignType.sign (MvPolynomial.eval x (q i))) =
        (fun i => SignType.sign (MvPolynomial.eval y (q i))) → f x = f y := by
  classical
  obtain ⟨η, hη, p, hp⟩ := hf
  let := hη
  let e := Fintype.equivFin η
  refine ⟨Fintype.card η, fun i => p (e.symm i), ?_⟩
  intro x y hxy
  apply hp x y
  intro i
  simpa only [Equiv.symm_apply_apply] using congrFun hxy (e i)

/-- Coefficient polynomials as real parameter functions. -/
noncomputable def RFun.fromPolynomial : MvPolynomial ι ℝ →+* RFun ι where
  toFun := RFun.polynomial
  map_zero' := by ext x; simp [RFun.polynomial]
  map_one' := by ext x; simp [RFun.polynomial]
  map_add' p q := by ext x; simp [RFun.polynomial]
  map_mul' p q := by ext x; simp [RFun.polynomial]

lemma specialize_fromPolynomial (p : Polynomial (MvPolynomial ι ℝ)) (x : ι → ℝ) :
    specialize (p.map RFun.fromPolynomial) x = p.map (MvPolynomial.eval x) := by
  rw [specialize, Polynomial.map_map]
  rfl

/-- Tarski queries of rational-on-cells polynomial families are finitely sign determined. -/
theorem specialize_tarski_query_int (p g : Polynomial (RFun ι)) :
    SignDetermined (fun x => ∑ a ∈ (specialize p x).roots.toFinset,
      zsign ((specialize g x).eval a)) := by
  apply SignDetermined.of_fibers (specialize_cauchyIndex (p.derivative * g) p)
  intro x y hxy
  have hx : specialize (p.derivative * g) x =
      (specialize p x).derivative * specialize g x := by
    simp [specialize, derivative_map]
  have hy : specialize (p.derivative * g) y =
      (specialize p y).derivative * specialize g y := by
    simp [specialize, derivative_map]
  change cauchyIndex (specialize (p.derivative * g) x) (specialize p x) =
    cauchyIndex (specialize (p.derivative * g) y) (specialize p y) at hxy
  rw [hx, hy, cauchyIndex_log_derivative, cauchyIndex_log_derivative] at hxy
  omega

theorem specialize_tarski_query (p g : Polynomial (RFun ι)) :
    SignDetermined (fun x => ∑ a ∈ (specialize p x).roots.toFinset,
      (SignType.sign ((specialize g x).eval a) : ℚ)) := by
  have h := (specialize_tarski_query_int p g).comp (fun z : ℤ => (z : ℚ))
  simpa only [Int.cast_sum, zsign, SignType.intCast_cast] using h

/-- Polynomial sign tests determine every parametric Tarski query, including degree drops. -/
theorem parametric_tarski_query (p g : Polynomial (MvPolynomial ι ℝ)) :
    ∃ (n : ℕ) (q : Fin n → MvPolynomial ι ℝ), ∀ x y,
      (fun i => SignType.sign (MvPolynomial.eval x (q i))) =
        (fun i => SignType.sign (MvPolynomial.eval y (q i))) →
      (∑ a ∈ (p.map (MvPolynomial.eval x)).roots.toFinset,
        (SignType.sign ((g.map (MvPolynomial.eval x)).eval a) : ℚ)) =
      (∑ a ∈ (p.map (MvPolynomial.eval y)).roots.toFinset,
        (SignType.sign ((g.map (MvPolynomial.eval y)).eval a) : ℚ)) := by
  have h := specialize_tarski_query (p.map RFun.fromPolynomial) (g.map RFun.fromPolynomial)
  simp only [specialize_fromPolynomial] at h
  exact h.fin

end Submission.Obl.k4_sign_projection
