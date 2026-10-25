import Mathlib

/-!
# Quadratic tests as polynomials in their last variable

A test `P : MvPolynomial (Fin (n + 1)) 𝕜` of total degree at most two is, in its last
(hidden) variable `w`, the quadratic
`P(z, w) = γ(z) + β(z) w + (c / 2) w ^ 2`, where `c` is the constant second hidden derivative,
`β(z) = ∂_w P(z, 0)` and `γ(z) = P(z, 0)`.  Its hidden derivative is `β(z) + c w`, and at every
root `(P_w)^2` equals the discriminant `β(z)^2 - 2 c γ(z)`.
-/

namespace Submission.Lib.K4QuadraticSheets

open MvPolynomial

section Derivative

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- Differentiating an evaluated polynomial along one coordinate gives the evaluated partial
derivative. -/
theorem hasDerivAt_eval_update {σ : Type*} [DecidableEq σ] (Q : MvPolynomial σ 𝕜)
    (x : σ → 𝕜) (i : σ) (s : 𝕜) :
    HasDerivAt (fun s => eval (Function.update x i s) Q)
      (eval (Function.update x i s) (pderiv i Q)) s := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    simp only [eval_C, pderiv_C, map_zero]
    exact hasDerivAt_const s a
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p j hp =>
    simp only [map_mul, eval_X, pderiv_mul, map_add, pderiv_X]
    by_cases hj : j = i
    · subst hj
      have h1 : HasDerivAt (fun s => Function.update x j s j) 1 s := by
        simp only [Function.update_self]
        exact hasDerivAt_id s
      have := hp.mul h1
      convert this using 1
      simp
    · have h1 : HasDerivAt (fun s => Function.update x i s j) 0 s := by
        simp only [Function.update_of_ne hj]
        exact hasDerivAt_const s _
      have := hp.mul h1
      convert this using 1
      simp [hj]

end Derivative

section Snoc

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

theorem snoc_eq_update {n : ℕ} (z : Fin n → 𝕜) (w : 𝕜) :
    (Fin.snoc z w : Fin (n + 1) → 𝕜) =
      Function.update (Fin.snoc z 0 : Fin (n + 1) → 𝕜) (Fin.last n) w := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp
  · rw [Function.update_of_ne (Fin.castSucc_ne_last j)]
    simp

/-- The hidden derivative of an evaluated test. -/
theorem hasDerivAt_eval_snoc {n : ℕ} (Q : MvPolynomial (Fin (n + 1)) 𝕜) (z : Fin n → 𝕜)
    (w : 𝕜) :
    HasDerivAt (fun w => eval (Fin.snoc z w : Fin (n + 1) → 𝕜) Q)
      (eval (Fin.snoc z w : Fin (n + 1) → 𝕜) (pderiv (Fin.last n) Q)) w := by
  have h := hasDerivAt_eval_update Q (Fin.snoc z 0 : Fin (n + 1) → 𝕜) (Fin.last n) w
  simp only [← snoc_eq_update] at h
  exact h

end Snoc

section Degree

variable {R : Type*} [CommSemiring R]

/-- Partial differentiation lowers a total-degree bound by one. -/
theorem totalDegree_pderiv_le' {σ : Type*} (P : MvPolynomial σ R) (i : σ) {d : ℕ}
    (hP : P.totalDegree ≤ d + 1) : (pderiv i P).totalDegree ≤ d := by
  classical
  apply Finset.sup_le
  intro m hm
  have hcoeff : P.coeff (m + Finsupp.single i 1) ≠ 0 := by
    have h := MvPolynomial.mem_support_iff.mp hm
    rw [coeff_pderiv] at h
    intro h0
    rw [h0, zero_mul] at h
    exact h rfl
  have hdeg := (le_totalDegree (MvPolynomial.mem_support_iff.mpr hcoeff)).trans hP
  have heq : (m + Finsupp.single i 1).sum (fun _ e => e) = m.sum (fun _ e => e) + 1 := by
    rw [Finsupp.sum_add_index' (by simp) (by intros; rfl)]
    simp
  rw [heq] at hdeg
  omega

/-- A polynomial of total degree zero is a constant. -/
theorem eq_C_of_totalDegree_eq_zero {σ : Type*} (P : MvPolynomial σ R)
    (hP : P.totalDegree = 0) : P = C (P.coeff 0) := by
  rw [totalDegree_eq_zero_iff_eq_C] at hP
  exact hP

end Degree

section Quadratic

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The constant second hidden derivative of a test. -/
noncomputable def qc {n : ℕ} (P : MvPolynomial (Fin (n + 1)) 𝕜) : 𝕜 :=
  eval (0 : Fin (n + 1) → 𝕜) (pderiv (Fin.last n) (pderiv (Fin.last n) P))

/-- The hidden derivative at hidden value zero. -/
noncomputable def qb {n : ℕ} (P : MvPolynomial (Fin (n + 1)) 𝕜) (z : Fin n → 𝕜) : 𝕜 :=
  eval (Fin.snoc z 0 : Fin (n + 1) → 𝕜) (pderiv (Fin.last n) P)

/-- The value at hidden value zero. -/
noncomputable def qg {n : ℕ} (P : MvPolynomial (Fin (n + 1)) 𝕜) (z : Fin n → 𝕜) : 𝕜 :=
  eval (Fin.snoc z 0 : Fin (n + 1) → 𝕜) P

/-- The discriminant `β ^ 2 - 2 c γ` of a test, independent of the hidden value. -/
noncomputable def qdisc {n : ℕ} (P : MvPolynomial (Fin (n + 1)) 𝕜) (z : Fin n → 𝕜) : 𝕜 :=
  qb P z ^ 2 - 2 * qc P * qg P z

theorem eval_pderiv2_eq_qc {n : ℕ} (P : MvPolynomial (Fin (n + 1)) 𝕜) (hP : P.totalDegree ≤ 2)
    (x : Fin (n + 1) → 𝕜) :
    eval x (pderiv (Fin.last n) (pderiv (Fin.last n) P)) = qc P := by
  have h1 : (pderiv (Fin.last n) P).totalDegree ≤ 1 := totalDegree_pderiv_le' P _ hP
  have h0 : (pderiv (Fin.last n) (pderiv (Fin.last n) P)).totalDegree ≤ 0 :=
    totalDegree_pderiv_le' _ _ h1
  rw [qc, eq_C_of_totalDegree_eq_zero _ (Nat.le_zero.mp h0)]
  simp

/-- The hidden derivative of a test is affine in the hidden variable. -/
theorem eval_snoc_pderiv {n : ℕ} (P : MvPolynomial (Fin (n + 1)) 𝕜) (hP : P.totalDegree ≤ 2)
    (z : Fin n → 𝕜) (w : 𝕜) :
    eval (Fin.snoc z w : Fin (n + 1) → 𝕜) (pderiv (Fin.last n) P) = qb P z + qc P * w := by
  set φ : 𝕜 → 𝕜 := fun w => eval (Fin.snoc z w : Fin (n + 1) → 𝕜) (pderiv (Fin.last n) P)
    - qc P * w with hφ
  have hd : ∀ w, HasDerivAt φ 0 w := by
    intro w
    have h1 := hasDerivAt_eval_snoc (pderiv (Fin.last n) P) z w
    rw [eval_pderiv2_eq_qc P hP] at h1
    have h2 : HasDerivAt (fun w => qc P * w) (qc P) w := by
      simpa using (hasDerivAt_id w).const_mul (qc P)
    have h3 := h1.sub h2
    rw [sub_self] at h3
    exact h3
  have hconst := is_const_of_deriv_eq_zero (fun w => (hd w).differentiableAt)
    (fun w => (hd w).deriv) w 0
  simp only [hφ, mul_zero, sub_zero] at hconst
  rw [qb, ← hconst]
  ring

/-- A test of total degree at most two is a quadratic in its hidden variable. -/
theorem eval_snoc_quadratic {n : ℕ} (P : MvPolynomial (Fin (n + 1)) 𝕜) (hP : P.totalDegree ≤ 2)
    (z : Fin n → 𝕜) (w : 𝕜) :
    eval (Fin.snoc z w : Fin (n + 1) → 𝕜) P = qg P z + qb P z * w + qc P / 2 * w ^ 2 := by
  set φ : 𝕜 → 𝕜 := fun w => eval (Fin.snoc z w : Fin (n + 1) → 𝕜) P
    - (qb P z * w + qc P / 2 * w ^ 2) with hφ
  have hd : ∀ w, HasDerivAt φ 0 w := by
    intro w
    have h1 := hasDerivAt_eval_snoc P z w
    rw [eval_snoc_pderiv P hP] at h1
    have h2 : HasDerivAt (fun w => qb P z * w + qc P / 2 * w ^ 2) (qb P z + qc P * w) w := by
      have ha := (hasDerivAt_id' w).const_mul (qb P z)
      have hb := (hasDerivAt_pow 2 w).const_mul (qc P / 2)
      have hc := ha.add hb
      convert hc using 1
      simp only [mul_one, Nat.cast_ofNat]
      ring
    have h3 := h1.sub h2
    rw [sub_self] at h3
    exact h3
  have hconst := is_const_of_deriv_eq_zero (fun w => (hd w).differentiableAt)
    (fun w => (hd w).deriv) w 0
  simp only [hφ, mul_zero, add_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow] at hconst
  rw [qg, ← hconst]
  ring

/-- At a root, the square of the hidden derivative is the discriminant. -/
theorem pderiv_sq_eq_qdisc_of_root {n : ℕ} (P : MvPolynomial (Fin (n + 1)) 𝕜)
    (hP : P.totalDegree ≤ 2) (z : Fin n → 𝕜) (w : 𝕜)
    (hroot : eval (Fin.snoc z w : Fin (n + 1) → 𝕜) P = 0) :
    eval (Fin.snoc z w : Fin (n + 1) → 𝕜) (pderiv (Fin.last n) P) ^ 2 = qdisc P z := by
  rw [eval_snoc_pderiv P hP, qdisc]
  rw [eval_snoc_quadratic P hP] at hroot
  linear_combination (2 * qc P) * hroot

/-- In general the square of the hidden derivative is the discriminant plus `2 c P`. -/
theorem pderiv_sq_eq_qdisc_add {n : ℕ} (P : MvPolynomial (Fin (n + 1)) 𝕜)
    (hP : P.totalDegree ≤ 2) (z : Fin n → 𝕜) (w : 𝕜) :
    eval (Fin.snoc z w : Fin (n + 1) → 𝕜) (pderiv (Fin.last n) P) ^ 2 =
      qdisc P z + 2 * qc P * eval (Fin.snoc z w : Fin (n + 1) → 𝕜) P := by
  rw [eval_snoc_pderiv P hP, qdisc, eval_snoc_quadratic P hP]
  ring

end Quadratic

end Submission.Lib.K4QuadraticSheets
