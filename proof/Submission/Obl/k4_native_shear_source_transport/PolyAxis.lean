-- Copied from LOT tree oai_074_kakeya_four_dimensions, obligation o075 (k4_joint_homogenization),
-- branch x0254, file Submission/Obl/k4_joint_homogenization/PolyAxis.lean (session x0254's own proofs), renamed into this namespace.
import Mathlib

/-!
# Polynomials restricted to a coordinate axis

A polynomial `P` composed with polynomial coordinates `g` and restricted to one axis of
the source is a univariate polynomial of degree at most `d · deg P`, where `d` bounds the
degrees of the `g l`. These restrictions supply the polynomial sign tables in the joint
base flattening bound.

`natDegree_eval₂_le_mul_totalDegree`, `coordinatePolynomial` and its two lemmas are adapted
from LOT tree oai_074_kakeya_four_dimensions, obligation o018
(k4_framework_from_matching_clustering_conic), branch x0048, file
`Submission/Obl/k4_framework_from_matching_clustering_conic/CoordinatePolynomials.lean`
(session x0048's own proofs), generalized from degree-one substitutions to degree `d`.
-/

namespace Submission.Obl.k4_native_shear_source_transport

open MvPolynomial

/-- Substituting univariate polynomials of degree at most `d` multiplies the total degree by
at most `d`. -/
theorem natDegree_eval₂_le_mul_totalDegree {σ : Type*} (P : MvPolynomial σ ℝ)
    (q : σ → Polynomial ℝ) (d : ℕ) (hq : ∀ i, (q i).natDegree ≤ d) :
    (MvPolynomial.eval₂ Polynomial.C q P).natDegree ≤ d * P.totalDegree := by
  classical
  rw [MvPolynomial.eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro s hs
  calc
    (Polynomial.C (P.coeff s) * ∏ i ∈ s.support, q i ^ s i).natDegree ≤
        (Polynomial.C (P.coeff s)).natDegree + (∏ i ∈ s.support, q i ^ s i).natDegree :=
      Polynomial.natDegree_mul_le
    _ = (∏ i ∈ s.support, q i ^ s i).natDegree := by rw [Polynomial.natDegree_C, zero_add]
    _ ≤ ∑ i ∈ s.support, (q i ^ s i).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ i ∈ s.support, d * s i := by
      apply Finset.sum_le_sum
      intro i _
      calc (q i ^ s i).natDegree ≤ s i * (q i).natDegree := Polynomial.natDegree_pow_le
        _ ≤ s i * d := Nat.mul_le_mul_left _ (hq i)
        _ = d * s i := Nat.mul_comm _ _
    _ = d * ∑ i ∈ s.support, s i := by rw [Finset.mul_sum]
    _ ≤ d * P.totalDegree := Nat.mul_le_mul_left _ (MvPolynomial.le_totalDegree hs)

/-- Fix all coordinates other than `j`, and leave coordinate `j` as a polynomial variable. -/
noncomputable def coordinatePolynomial {σ : Type*} [DecidableEq σ]
    (P : MvPolynomial σ ℝ) (a : σ → ℝ) (j : σ) : Polynomial ℝ :=
  MvPolynomial.eval₂ Polynomial.C
    (fun i => if i = j then Polynomial.X else Polynomial.C (a i)) P

theorem coordinatePolynomial_natDegree_le {σ : Type*} [DecidableEq σ]
    (P : MvPolynomial σ ℝ) (a : σ → ℝ) (j : σ) :
    (coordinatePolynomial P a j).natDegree ≤ P.totalDegree := by
  have h := natDegree_eval₂_le_mul_totalDegree P
    (fun i => if i = j then Polynomial.X else Polynomial.C (a i)) 1 (by
      intro i
      split_ifs <;> simp)
  rw [one_mul] at h
  exact h

theorem coordinatePolynomial_eval {σ : Type*} [DecidableEq σ]
    (P : MvPolynomial σ ℝ) (a : σ → ℝ) (j : σ) (t : ℝ) :
    (coordinatePolynomial P a j).eval t = MvPolynomial.eval (Function.update a j t) P := by
  change (Polynomial.evalRingHom t) (coordinatePolynomial P a j) = _
  rw [coordinatePolynomial, MvPolynomial.eval₂_comp_left]
  have hC : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id ℝ := by ext x; simp
  rw [hC]
  congr 1
  ext i
  by_cases hi : i = j <;> simp [hi, Function.update]

/-- `P ∘ g`, restricted to the axis `k` through `a`. -/
noncomputable def axisPolynomial {σ τ : Type*} [DecidableEq τ] (P : MvPolynomial σ ℝ)
    (g : σ → MvPolynomial τ ℝ) (a : τ → ℝ) (k : τ) : Polynomial ℝ :=
  MvPolynomial.eval₂ Polynomial.C (fun l => coordinatePolynomial (g l) a k) P

theorem axisPolynomial_eval {σ τ : Type*} [DecidableEq τ] (P : MvPolynomial σ ℝ)
    (g : σ → MvPolynomial τ ℝ) (a : τ → ℝ) (k : τ) (t : ℝ) :
    (axisPolynomial P g a k).eval t =
      MvPolynomial.eval (fun l => MvPolynomial.eval (Function.update a k t) (g l)) P := by
  change (Polynomial.evalRingHom t) (axisPolynomial P g a k) = _
  rw [axisPolynomial, MvPolynomial.eval₂_comp_left]
  have hC : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id ℝ := by ext x; simp
  rw [hC]
  congr 1
  ext l
  simp only [Function.comp_apply, Polynomial.coe_evalRingHom, coordinatePolynomial_eval]

theorem axisPolynomial_natDegree_le {σ τ : Type*} [DecidableEq τ] (P : MvPolynomial σ ℝ)
    (g : σ → MvPolynomial τ ℝ) (d : ℕ) (hg : ∀ l, (g l).totalDegree ≤ d) (a : τ → ℝ) (k : τ) :
    (axisPolynomial P g a k).natDegree ≤ d * P.totalDegree :=
  natDegree_eval₂_le_mul_totalDegree P _ d fun l =>
    (coordinatePolynomial_natDegree_le (g l) a k).trans (hg l)

end Submission.Obl.k4_native_shear_source_transport
