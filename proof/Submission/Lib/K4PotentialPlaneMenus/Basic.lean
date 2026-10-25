/- Adapted from: here:o267
   General polynomial and trajectory notation used by x0945's plane-menu proofs.
   The elementary linePolyR/lineRestrR/evaluation/degree facts below were
   imported by that source from this LOT tree o210 (clean_cover_graph_atlas),
   Tests.lean at366dbc27, retaining its earlier attribution: o194/x0672@69d09a7b8755
   Tests.lean, earlier o173/x0598@6ded8016fe11 Tests.lean.
   totalDegree_bind_affine was imported from this tree's
   k4_quadratic_selector_sweep/SignFibers.lean atdfc4f44f.
   iteratedDeriv_polynomial_eval was imported from this tree's
   k4_algebraic_sheet_remez/PolynomialDerivatives.lean at86b9d1ea.
   All are elementary standalone polynomial identities, copied from the
   pinned workspace only, and renamed into this contribution's namespace. -/
import Mathlib
import Submission.Lib.K4ChartLifting.Sizes
import Submission.Lib.K4CubicTests.PolynomialTaylor
import Submission.Lib.K4ScalarCoreTools.Simulation.CoefficientBounds

namespace Submission.Lib.K4PotentialPlaneMenus

open MvPolynomial Set
open scoped BigOperators
noncomputable section

abbrev Line := ℕ × (Fin 6 → ℝ)
abbrev Event := Line × ℝ
abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Base := EuclideanSpace ℝ (Fin 3)
abbrev Quad := MvPolynomial (Fin 4) ℝ
abbrev Observation := Base × ℤ
abbrev point := fun (l : Line) (t : ℝ) => ![t,l.2 0+t*l.2 3,l.2 1+t*l.2 4,l.2 2+t*l.2 5]
abbrev observe := fun (B a : ℝ) (p : Event) =>
  (WithLp.toLp 2 ![p.2,(point p.1 p.2) 1,(point p.1 p.2) 2], ⌊B*(point p.1 p.2) 3/a⌋)

namespace PolynomialOwnRows
def lineDirection (l : Line) : Fin 4 → ℝ := ![1, l.2 3, l.2 4, l.2 5]
end PolynomialOwnRows

/-- The coordinates of a line `t ↦ v + t w` as real polynomials in `t`. -/
noncomputable def linePolyR {σ : Type*} (v w : σ → ℝ) (i : σ) : Polynomial ℝ :=
  Polynomial.C (v i) + Polynomial.X * Polynomial.C (w i)

/-- A real polynomial restricted to the line `t ↦ v + t w`. -/
noncomputable def lineRestrR {σ : Type*} (Q : MvPolynomial σ ℝ) (v w : σ → ℝ) : Polynomial ℝ :=
  MvPolynomial.eval₂ Polynomial.C (linePolyR v w) Q

theorem eval_lineRestrR {σ : Type*} (Q : MvPolynomial σ ℝ) (v w : σ → ℝ) (t : ℝ) :
    (lineRestrR Q v w).eval t = MvPolynomial.eval (fun i => v i + t * w i) Q := by
  rw [lineRestrR, ← Polynomial.coe_evalRingHom, MvPolynomial.eval₂_comp_left]
  simp only [MvPolynomial.eval]
  congr 1
  · ext r
    simp
  · ext i
    simp only [linePolyR, Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X, Function.comp_apply]

theorem natDegree_lineRestrR_le {σ : Type*} (Q : MvPolynomial σ ℝ) (v w : σ → ℝ) :
    (lineRestrR Q v w).natDegree ≤ Q.totalDegree := by
  classical
  rw [lineRestrR]
  conv_lhs => rw [Q.as_sum]
  rw [MvPolynomial.eval₂_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  rw [MvPolynomial.eval₂_monomial]
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  have hQ : ∀ i, (linePolyR v w i).natDegree ≤ 1 := by
    intro i
    rw [linePolyR]
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · simp
    · apply (Polynomial.natDegree_mul_le).trans
      simp
  calc
    (m.prod fun i e => linePolyR v w i ^ e).natDegree ≤
        m.sum (fun i e => (linePolyR v w i ^ e).natDegree) := Polynomial.natDegree_prod_le _ _
    _ ≤ m.sum (fun _ e => e) := by
        apply Finset.sum_le_sum
        intro i _
        apply (Polynomial.natDegree_pow_le).trans
        calc m i * (linePolyR v w i).natDegree ≤ m i * 1 := Nat.mul_le_mul_left _ (hQ i)
          _ = m i := mul_one _
    _ ≤ Q.totalDegree := le_totalDegree hm

/-- Affine substitution preserves a polynomial's total-degree bound. -/
theorem totalDegree_bind_affine {σ τ : Type*}
    (v : σ → MvPolynomial τ ℝ) (hv : ∀ i, (v i).totalDegree ≤ 1)
    (p : MvPolynomial σ ℝ) : (bind₁ v p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply totalDegree_finsetSum_le
  intro m hm
  rw [bind₁, aeval_monomial]
  change (C (p.coeff m) * m.support.prod (fun i => v i ^ m i)).totalDegree ≤ _
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  calc
    ∑ i ∈ m.support, (v i ^ m i).totalDegree
        ≤ ∑ i ∈ m.support, m i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (m i) (hv i))
    _ ≤ p.totalDegree := le_totalDegree hm

/-- Iterated real derivatives of a polynomial are evaluations of its formal
iterated derivatives. -/
theorem iteratedDeriv_polynomial_eval (p : Polynomial ℝ) (q : ℕ) :
    iteratedDeriv q (fun x : ℝ => p.eval x) =
      fun x => ((Polynomial.derivative^[q]) p).eval x := by
  induction q generalizing p with
  | zero => rfl
  | succ q ih =>
    rw [iteratedDeriv_succ']
    have he : deriv (fun x : ℝ => p.eval x) = fun x => p.derivative.eval x :=
      funext (fun _ => p.deriv)
    rw [he, ih]
    rfl


end

end Submission.Lib.K4PotentialPlaneMenus
