/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4CubicTests.ConicKernels
import Submission.Lib.K4CubicTests.LinearScalar

open MvPolynomial

namespace Submission.Lib.K4CubicTests

/-- Coordinate derivatives of multivariate polynomials commute. -/
theorem polynomial_pderiv_comm (F : MvPolynomial (Fin 3) ℝ) (i j : Fin 3) :
    pderiv i (pderiv j F) = pderiv j (pderiv i F) := by
  by_cases hij : i = j
  · subst j
    rfl
  ext m
  simp [coeff_pderiv, Finsupp.add_apply, Finsupp.single_apply, hij, Ne.symm hij,
    add_assoc, add_comm, add_left_comm] <;> ring

/-- A degree-one homogeneous polynomial is its linear coordinate expansion. -/
theorem homogeneous_one_eq_sum_linear (F : MvPolynomial (Fin 3) ℝ) (hF : F.IsHomogeneous 1) :
    F = ∑ i : Fin 3, C ((pderiv i F).coeff 0) * X i := by
  have hconst (i : Fin 3) : pderiv i F = C ((pderiv i F).coeff 0) := by
    have h : (pderiv i F).IsHomogeneous 0 := hF.pderiv
    rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at h
    exact h
  have hEuler := hF.sum_X_mul_pderiv
  simp only [one_smul] at hEuler
  calc
    F = ∑ i : Fin 3, X i * pderiv i F := hEuler.symm
    _ = _ := Finset.sum_congr rfl fun i _ => by
      calc
        X i * pderiv i F = X i * C ((pderiv i F).coeff 0) :=
          congrArg (fun P => X i * P) (hconst i)
        _ = _ := mul_comm _ _

/-- Four of the seven projective points, as a linear general-position family. -/
private theorem first_four_projective_independent (p : Fin 7 → Fin 3 → ℝ)
    (hp : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
      Matrix.det (Matrix.of ![p i, p j, p k]) ≠ 0) :
    ∃ e : Fin 4 → Fin 7, Function.Injective e ∧
      (∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k →
        LinearIndependent ℝ ![p (e i), p (e j), p (e k)]) ∧
      (∀ i : Fin 4, p (e i) ≠ 0) := by
  let e : Fin 4 → Fin 7 := fun i => ⟨i.val, lt_trans i.isLt (by decide : 4 < 7)⟩
  have he : Function.Injective e := fun i j h => Fin.ext (congrArg (fun z : Fin 7 => z.val) h)
  have hlin (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      LinearIndependent ℝ ![p (e i), p (e j), p (e k)] := by
    have h := Matrix.linearIndependent_rows_of_det_ne_zero (hp (e i) (e j) (e k)
      (he.ne hij) (he.ne hik) (he.ne hjk))
    convert h using 1
    funext a b
    rfl
  refine ⟨e, he, hlin, ?_⟩
  intro i
  fin_cases i
  · simpa using (hlin 0 1 2 (by decide) (by decide) (by decide)).ne_zero (0 : Fin 3)
  · simpa using (hlin 1 0 2 (by decide) (by decide) (by decide)).ne_zero (0 : Fin 3)
  · simpa using (hlin 2 0 1 (by decide) (by decide) (by decide)).ne_zero (0 : Fin 3)
  · simpa using (hlin 3 0 1 (by decide) (by decide) (by decide)).ne_zero (0 : Fin 3)

/-- The rank-four kernel in paper Lemma 6.6(3), with the conic's nondegenerate
gradient map made explicit. A quartic with vanishing first derivatives at the
seven points is a scalar multiple of the square of the conic. -/
theorem quartic_vanishing_eq_conic_sq (p : Fin 7 → Fin 3 → ℝ)
    (hp : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
      Matrix.det (Matrix.of ![p i, p j, p k]) ≠ 0)
    (q : MvPolynomial (Fin 3) ℝ) (hq : q.IsHomogeneous 2) (hne : q ≠ 0)
    (hqzero : ∀ i, MvPolynomial.eval (p i) q = 0)
    (B : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ))
    (hB : ∀ (x : Fin 3 → ℝ) (j : Fin 3), MvPolynomial.eval x (pderiv j q) = B x j)
    (F : MvPolynomial (Fin 3) ℝ) (hF : F.IsHomogeneous 4)
    (hFzero : ∀ i : Fin 7, ∀ j : Fin 3, MvPolynomial.eval (p i) (pderiv j F) = 0) :
    ∃ r : ℝ, F = C r * q ^ 2 := by
  classical
  have hexists (j : Fin 3) : ∃ L : MvPolynomial (Fin 3) ℝ,
      L.IsHomogeneous 1 ∧ pderiv j F = q * L :=
    cubic_vanishing_eq_conic_mul_linear p hp q hq hne hqzero (pderiv j F) hF.pderiv
      (fun i => hFzero i j)
  choose L hLhom hL using hexists
  let A : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) :=
    (Matrix.of fun j k : Fin 3 => (pderiv k (L j)).coeff 0).mulVecLin
  have hA (x : Fin 3 → ℝ) (j : Fin 3) : MvPolynomial.eval x (L j) = A x j := by
    rw [homogeneous_one_eq_sum_linear (L j) (hLhom j)]
    simp [A, Matrix.mulVec, dotProduct]
  have hcross (i : Fin 7) (j k : Fin 3) :
      B (p i) k * A (p i) j = B (p i) j * A (p i) k := by
    have hpoly := polynomial_pderiv_comm F k j
    rw [hL j, hL k, pderiv_mul, pderiv_mul] at hpoly
    have h := congrArg (MvPolynomial.eval (p i)) hpoly
    simpa only [map_add, map_mul, hqzero i, zero_mul, add_zero, hB, hA] using h
  obtain ⟨e, he, hlin, hp0⟩ := first_four_projective_independent p hp
  obtain ⟨r, hr⟩ := linearMap_proportional_of_four_cross_tests (fun i => p (e i)) hlin hp0 B A
    (fun i j k => hcross (e i) j k)
  have hLeq (j : Fin 3) : L j = C r * pderiv j q := by
    apply MvPolynomial.funext
    intro x
    have h := congrFun (LinearMap.congr_fun hr x) j
    calc
      MvPolynomial.eval x (L j) = A x j := hA x j
      _ = r * B x j := by simpa using h
      _ = MvPolynomial.eval x (C r * pderiv j q) := by simp [hB]
  refine ⟨r / 2, ?_⟩
  apply MvPolynomial.funext
  intro x
  have hFE := congrArg (MvPolynomial.eval x) hF.sum_X_mul_pderiv
  have hQE := congrArg (MvPolynomial.eval x) hq.sum_X_mul_pderiv
  simp only [map_sum, map_mul, eval_X, map_nsmul, nsmul_eq_mul, Nat.cast_ofNat] at hFE hQE
  simp only [hL, map_mul, hLeq, eval_C] at hFE
  have hsum : ∑ j : Fin 3, x j *
      (MvPolynomial.eval x q * (r * MvPolynomial.eval x (pderiv j q))) =
      r * MvPolynomial.eval x q * ∑ j : Fin 3, x j * MvPolynomial.eval x (pderiv j q) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hsum, hQE] at hFE
  norm_num at hFE
  simp only [map_mul, map_pow, eval_C]
  nlinarith [hFE]

/-- The rank-five kernel in paper Lemma 6.6(3): a homogeneous quintic with
vanishing second derivatives at the seven conic points is zero. -/
theorem quintic_vanishing_eq_zero (p : Fin 7 → Fin 3 → ℝ)
    (hp : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
      Matrix.det (Matrix.of ![p i, p j, p k]) ≠ 0)
    (q : MvPolynomial (Fin 3) ℝ) (hq : q.IsHomogeneous 2) (hne : q ≠ 0)
    (hqzero : ∀ i, MvPolynomial.eval (p i) q = 0)
    (B : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ))
    (hB : ∀ (x : Fin 3 → ℝ) (j : Fin 3), MvPolynomial.eval x (pderiv j q) = B x j)
    (F : MvPolynomial (Fin 3) ℝ) (hF : F.IsHomogeneous 5)
    (hFzero : ∀ i : Fin 7, ∀ j k : Fin 3,
      MvPolynomial.eval (p i) (pderiv k (pderiv j F)) = 0) : F = 0 := by
  classical
  have hexists (j : Fin 3) : ∃ r : ℝ, pderiv j F = C r * q ^ 2 :=
    quartic_vanishing_eq_conic_sq p hp q hq hne hqzero B hB (pderiv j F) hF.pderiv
      (fun i k => hFzero i j k)
  choose r hr using hexists
  have hcross (j k : Fin 3) : C (r j) * pderiv k q = C (r k) * pderiv j q := by
    have hpoly := polynomial_pderiv_comm F k j
    rw [hr j, hr k, pderiv_C_mul, pderiv_C_mul, pderiv_pow, pderiv_pow] at hpoly
    simp only [Nat.reduceSub, pow_one] at hpoly
    have h2 : (2 : MvPolynomial (Fin 3) ℝ) *
        (q * (C (r j) * pderiv k q - C (r k) * pderiv j q)) = 0 := by
      linear_combination hpoly
    have hz : q * (C (r j) * pderiv k q - C (r k) * pderiv j q) = 0 :=
      (mul_eq_zero.mp h2).resolve_left (by norm_num)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hne)
  have hrzero (j : Fin 3) : r j = 0 := by
    let k : Fin 3 := j.succAbove (0 : Fin 2)
    have hkj : k ≠ j := Fin.succAbove_ne _ _
    have h := congrArg (MvPolynomial.eval (B.symm (Pi.single k 1))) (hcross j k)
    simpa [hB, hkj, Ne.symm hkj] using h
  have hderiv (j : Fin 3) : pderiv j F = 0 := by
    rw [hr j, hrzero j]
    simp
  have hEuler := hF.sum_X_mul_pderiv
  simp only [hderiv, mul_zero, Finset.sum_const_zero] at hEuler
  apply MvPolynomial.funext
  intro x
  have h := congrArg (MvPolynomial.eval x) hEuler
  norm_num at h ⊢
  nlinarith

end Submission.Lib.K4CubicTests
