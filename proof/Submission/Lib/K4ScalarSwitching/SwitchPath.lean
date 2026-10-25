/-
Adapted from: here:o062
Original proof: x0511, branch x0511, commit bf52299; retained source-credit comment follows.
Owned source: Submission/Obl/k4_scalar_mesh_projection/SwitchPath.lean.
-/

/- From o062 session x0511, branch x0511, commit bf52299;
original file Submission/Obl/k4_scalar_mesh_projection/SwitchPath.lean. -/

import Submission.Lib.K4ScalarSwitching.Switching
import Submission.Lib.K4PolynomialPotential

namespace Submission.Lib.K4ScalarSwitching.Switching

open MvPolynomial
open Submission.Lib.K4PolynomialPotential
open MeasureTheory

noncomputable def upperSubst {σ : Type*} (j : σ) :
    MvPolynomial (σ ⊕ Unit) ℝ →ₐ[ℝ] MvPolynomial σ ℝ :=
  aeval (Sum.elim X (fun _ => X j))

theorem eval_upperSubst {σ : Type*} (P : MvPolynomial (σ ⊕ Unit) ℝ)
    (j : σ) (x : σ → ℝ) :
    eval x (upperSubst j P) = eval (Sum.elim x (fun _ => x j)) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [upperSubst]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P k hP =>
    simp only [map_mul, hP]
    cases k <;> simp [upperSubst]

theorem eval_upperSubst_zero {σ : Type*} (P : MvPolynomial (σ ⊕ Unit) ℝ) (j : σ) :
    eval (0 : σ → ℝ) (upperSubst j P) = eval (0 : σ ⊕ Unit → ℝ) P := by
  rw [eval_upperSubst]
  have he : Sum.elim (0 : σ → ℝ) (fun _ : Unit => (0 : σ → ℝ) j) =
      (0 : σ ⊕ Unit → ℝ) := by
    funext z
    cases z <;> rfl
  rw [he]

theorem partial_upperSubst {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : MvPolynomial (σ ⊕ Unit) ℝ) (j i : σ) :
    pderiv i (upperSubst j P) = upperSubst j (pderiv (Sum.inl i) P) +
      (if i = j then upperSubst j (pderiv (Sum.inr ()) P) else 0) := by
  classical
  unfold upperSubst
  rw [partial_aeval, Fintype.sum_sum_type]
  simp [pderiv_X, Pi.single_apply, eq_comm]

noncomputable def upperPrimitive {σ : Type*} (j : σ)
    (P : MvPolynomial (σ ⊕ Unit) ℝ) : MvPolynomial σ ℝ :=
  upperSubst j (polynomialPrimitive (Sum.inr ()) P)

theorem eval_upperPrimitive_zero {σ : Type*} [Fintype σ]
    (P : MvPolynomial (σ ⊕ Unit) ℝ) (j : σ) :
    eval (0 : σ → ℝ) (upperPrimitive j P) = 0 := by
  rw [upperPrimitive, eval_upperSubst_zero]
  exact eval_polynomialPrimitive_zero _ _ _ rfl

theorem partial_upperPrimitive {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : MvPolynomial (σ ⊕ Unit) ℝ) (j i : σ) :
    pderiv i (upperPrimitive j P) = upperPrimitive j (pderiv (Sum.inl i) P) +
      (if i = j then upperSubst j P else 0) := by
  classical
  unfold upperPrimitive
  rw [partial_upperSubst,
    pderiv_polynomialPrimitive_of_ne P (by simp : (Sum.inl i : σ ⊕ Unit) ≠ Sum.inr ()),
    pderiv_polynomialPrimitive]

theorem eval_partial_upperPrimitive_zero {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : MvPolynomial (σ ⊕ Unit) ℝ) (j i : σ) :
    eval (0 : σ → ℝ) (pderiv i (upperPrimitive j P)) =
      if i = j then eval (0 : σ ⊕ Unit → ℝ) P else 0 := by
  classical
  rw [partial_upperPrimitive, map_add, eval_upperPrimitive_zero, zero_add]
  split_ifs <;> simp only [eval_upperSubst_zero, map_zero]

theorem eval_second_upperPrimitive_zero {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : MvPolynomial (σ ⊕ Unit) ℝ) (j i k : σ) :
    eval (0 : σ → ℝ) (pderiv i (pderiv k (upperPrimitive j P))) =
      (if i = j then eval (0 : σ ⊕ Unit → ℝ) (pderiv (Sum.inl k) P) else 0) +
      (if k = j then eval (0 : σ ⊕ Unit → ℝ) (pderiv (Sum.inl i) P) else 0) +
      (if i = j ∧ k = j then eval (0 : σ ⊕ Unit → ℝ) (pderiv (Sum.inr ()) P) else 0) := by
  classical
  rw [partial_upperPrimitive, map_add, map_add, eval_partial_upperPrimitive_zero]
  by_cases hi : i = j <;> by_cases hk : k = j <;>
    simp only [hi, hk, partial_upperSubst, eval_upperSubst_zero, map_add, map_zero,
      ite_true, ite_false, and_self, and_true, and_false, zero_add, add_zero]
    <;> ring

/-- Polynomial coordinates on the `j`th leg, before its endpoint increment
is substituted for the auxiliary integration variable. -/
noncomputable def legPoint (x : Fin 2 → ℝ) (v : Fin 4 → ℝ) (j : Fin 4)
    (d : Fin 2) : MvPolynomial (Fin 4 ⊕ Unit) ℝ :=
  C (x d) + (∑ k : Fin 4, if k.val < j.val then
    C ((![1, v k] : Fin 2 → ℝ) d) * X (Sum.inl k) else 0) +
      C ((![1, v j] : Fin 2 → ℝ) d) * X (Sum.inr ())

theorem eval_legPoint_zero (x : Fin 2 → ℝ) (v : Fin 4 → ℝ) (j : Fin 4)
    (d : Fin 2) : eval (0 : Fin 4 ⊕ Unit → ℝ) (legPoint x v j d) = x d := by
  simp [legPoint, apply_ite]

theorem partial_legPoint_control (x : Fin 2 → ℝ) (v : Fin 4 → ℝ) (j i : Fin 4)
    (d : Fin 2) : pderiv (Sum.inl i) (legPoint x v j d) =
      if i.val < j.val then C ((![1, v i] : Fin 2 → ℝ) d) else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [legPoint, Fin.sum_univ_succ, pderiv_C_mul, pderiv_X, Pi.single_apply]

theorem partial_legPoint_aux (x : Fin 2 → ℝ) (v : Fin 4 → ℝ) (j : Fin 4)
    (d : Fin 2) : pderiv (Sum.inr ()) (legPoint x v j d) =
      C ((![1, v j] : Fin 2 → ℝ) d) := by
  simp [legPoint, apply_ite]

theorem eval_substitution {σ τ : Type*} (P : MvPolynomial σ ℝ)
    (f : σ → MvPolynomial τ ℝ) (x : τ → ℝ) :
    eval x (aeval f P) = eval (fun j => eval x (f j)) P :=
  comp_aeval_apply f (aeval x) P

noncomputable def legField (A B : MvPolynomial (Fin 2) ℝ)
    (x : Fin 2 → ℝ) (v : Fin 4 → ℝ) (j : Fin 4) :
    MvPolynomial (Fin 4 ⊕ Unit) ℝ :=
  aeval (legPoint x v j) A + C (v j) * aeval (legPoint x v j) B

theorem eval_partial_legField_control (A B : MvPolynomial (Fin 2) ℝ)
    (x : Fin 2 → ℝ) (v : Fin 4 → ℝ) (j i : Fin 4) :
    eval (0 : Fin 4 ⊕ Unit → ℝ) (pderiv (Sum.inl i) (legField A B x v j)) =
      if i.val < j.val then eval x (pderiv 0 A) + v i * eval x (pderiv 1 A) +
        v j * eval x (pderiv 0 B) + v i * v j * eval x (pderiv 1 B) else 0 := by
  rw [legField, map_add, pderiv_C_mul]
  simp only [partial_aeval, Fin.sum_univ_two, partial_legPoint_control,
    map_add, map_mul, eval_C, eval_substitution, eval_legPoint_zero,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  split_ifs <;> simp only [eval_C, map_zero, mul_zero, mul_one, add_zero] <;> ring

theorem eval_partial_legField_aux (A B : MvPolynomial (Fin 2) ℝ)
    (x : Fin 2 → ℝ) (v : Fin 4 → ℝ) (j : Fin 4) :
    eval (0 : Fin 4 ⊕ Unit → ℝ) (pderiv (Sum.inr ()) (legField A B x v j)) =
      eval x (pderiv 0 A) + v j * eval x (pderiv 1 A) +
        v j * eval x (pderiv 0 B) + v j ^ 2 * eval x (pderiv 1 B) := by
  rw [legField, map_add, pderiv_C_mul]
  simp only [partial_aeval, Fin.sum_univ_two, partial_legPoint_aux,
    map_add, map_mul, eval_C, eval_substitution, eval_legPoint_zero,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- Accumulated height of four successive signed legs. Coordinate `j` is
the length of the leg in direction `(1,v_j)`. -/
noncomputable def brokenHeight (A B : MvPolynomial (Fin 2) ℝ)
    (x : Fin 2 → ℝ) (v : Fin 4 → ℝ) : MvPolynomial (Fin 4) ℝ :=
  ∑ j : Fin 4, upperPrimitive j (legField A B x v j)

/-- Earlier increments move the starting point of a later leg. At zero
increments, all other legs have zero duration, so there are no other mixed
terms in the Hessian. -/
theorem brokenHeight_hessian (A B : MvPolynomial (Fin 2) ℝ)
    (x : Fin 2 → ℝ) (v : Fin 4 → ℝ) (i j : Fin 4) (hij : i.val < j.val) :
    hessian (brokenHeight A B x v) 0 i j =
      eval x (pderiv 0 A) + v i * eval x (pderiv 1 A) +
        v j * eval x (pderiv 0 B) + v i * v j * eval x (pderiv 1 B) := by
  have hne : i ≠ j := by intro h; subst j; exact Nat.lt_irrefl _ hij
  have hnlt : ¬ j.val < i.val := Nat.not_lt.mpr hij.le
  have hleg (k : Fin 4) :
      eval (0 : Fin 4 → ℝ) (pderiv i (pderiv j (upperPrimitive k (legField A B x v k)))) =
        if k = j then
          eval x (pderiv 0 A) + v i * eval x (pderiv 1 A) +
            v j * eval x (pderiv 0 B) + v i * v j * eval x (pderiv 1 B) else 0 := by
    rw [eval_second_upperPrimitive_zero]
    by_cases hkj : k = j
    · subst k
      simp only [hne, ite_false, ite_true, false_and, zero_add, add_zero]
      rw [eval_partial_legField_control, ite_eq_left hij]
    · by_cases hki : k = i
      · subst k
        simp only [Ne.symm hne, hne, ite_false, ite_true, and_false, add_zero]
        rw [eval_partial_legField_control, ite_eq_right hnlt]
      · simp only [Ne.symm hki, Ne.symm hkj, hkj, ite_false, false_and, zero_add]
  unfold hessian brokenHeight
  simp only [map_sum, hleg]
  simp

/-- The curl is detected by actual polynomial endpoint minors of the
successive-leg construction, with no cross-Hessian premise remaining. -/
theorem brokenHeight_curl_bound (A B : MvPolynomial (Fin 2) ℝ)
    (x : Fin 2 → ℝ) (v : Fin 4 → ℝ) {K η : ℝ} (hK : 1 ≤ K) (hη : 0 ≤ η)
    (hv : ∀ i, |v i| ≤ K) (hdetI : 1 / K ≤ |v 1 - v 0|)
    (hdetJ : 1 / K ≤ |v 3 - v 2|)
    (hminor : ∀ i j : Fin 4, i.val < 2 → 2 ≤ j.val →
      |eval (0 : Fin 4 → ℝ) (pderiv i (endpointMinor (brokenHeight A B x v) v j))| ≤ η) :
    |eval x (pderiv 0 B - pderiv 1 A)| ≤ 8 * K ^ 4 * η := by
  have hcross (i j : Fin 4) (hi : i.val < 2) (hj : 2 ≤ j.val) :
      hessian (brokenHeight A B x v) 0 i j =
        eval x (pderiv 0 A) + v i * eval x (pderiv 1 A) +
          v j * eval x (pderiv 0 B) + v i * v j * eval x (pderiv 1 B) :=
    brokenHeight_hessian A B x v i j (hi.trans_le hj)
  have h := polynomial_curl_bound (brokenHeight A B x v) v 0
    (eval x (pderiv 0 A)) (eval x (pderiv 1 A))
    (eval x (pderiv 0 B)) (eval x (pderiv 1 B))
    hK hη hv hdetI hdetJ hcross hminor
  simpa only [map_sub] using h

/-- High curl supplies a large linear coefficient of an actual endpoint
minor. This is the normalization needed before applying polynomial sublevel
estimates to the increment variables. -/
theorem exists_large_minor_coefficient (A B : MvPolynomial (Fin 2) ℝ)
    (x : Fin 2 → ℝ) (v : Fin 4 → ℝ) {K η : ℝ} (hK : 1 ≤ K) (hη : 0 ≤ η)
    (hv : ∀ i, |v i| ≤ K) (hdetI : 1 / K ≤ |v 1 - v 0|)
    (hdetJ : 1 / K ≤ |v 3 - v 2|)
    (hskew : 8 * K ^ 4 * η < |eval x (pderiv 0 B - pderiv 1 A)|) :
    ∃ i j : Fin 4, i.val < 2 ∧ 2 ≤ j.val ∧
      η < |(endpointMinor (brokenHeight A B x v) v j).coeff (Finsupp.single i 1)| := by
  obtain ⟨i, j, hi, hj, hlarge⟩ := exists_large_minor_derivative
    (brokenHeight A B x v) v 0
    (eval x (pderiv 0 A)) (eval x (pderiv 1 A))
    (eval x (pderiv 0 B)) (eval x (pderiv 1 B)) hK hη hv hdetI hdetJ
    (fun i j hi hj => brokenHeight_hessian A B x v i j (hi.trans_le hj))
    (by simpa only [map_sub] using hskew)
  refine ⟨i, j, hi, hj, ?_⟩
  simpa only [partial_eval_zero_eq_coeff] using hlarge

/-- The coordinate slice used to integrate the auxiliary leg parameter. -/
theorem eval_auxCoordinate {σ : Type*} [DecidableEq σ]
    (P : MvPolynomial (σ ⊕ Unit) ℝ) (δ : σ → ℝ) (s : ℝ) :
    (coordinatePolynomialHom (Sum.elim δ (fun _ : Unit => 0)) (Sum.inr ()) P).eval s =
      eval (Sum.elim δ (fun _ : Unit => s)) P := by
  rw [eval_coordinatePolynomialHom]
  apply congrArg (fun f : σ ⊕ Unit → ℝ => eval f P)
  funext k
  cases k with
  | inl k => simp
  | inr k => cases k; simp

/-- The algebraic primitive is the signed line integral for either sign of
the leg length. -/
theorem eval_upperPrimitive_integral {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : MvPolynomial (σ ⊕ Unit) ℝ) (j : σ) (δ : σ → ℝ) :
    eval δ (upperPrimitive j P) =
      ∫ s in (0 : ℝ)..δ j, eval (Sum.elim δ (fun _ : Unit => s)) P := by
  let q := coordinatePolynomialHom (Sum.elim δ (fun _ : Unit => 0)) (Sum.inr ())
    (polynomialPrimitive (Sum.inr ()) P)
  have hqd : q.derivative =
      coordinatePolynomialHom (Sum.elim δ (fun _ : Unit => 0)) (Sum.inr ()) P := by
    dsimp [q]
    rw [derivative_coordinatePolynomialHom, pderiv_polynomialPrimitive]
  have hderiv (s : ℝ) : HasDerivAt (fun s => q.eval s)
      (eval (Sum.elim δ (fun _ : Unit => s)) P) s := by
    simpa only [hqd, eval_auxCoordinate] using q.hasDerivAt s
  have hcont : Continuous (fun s => eval (Sum.elim δ (fun _ : Unit => s)) P) := by
    have heq : (fun s => eval (Sum.elim δ (fun _ : Unit => s)) P) =
        (fun s => q.derivative.eval s) := by
      funext s
      rw [hqd, eval_auxCoordinate]
    rw [heq]
    exact q.derivative.continuous
  have hqzero : q.eval 0 = 0 := by
    dsimp only [q]
    rw [eval_auxCoordinate]
    exact eval_polynomialPrimitive_zero _ _ _ rfl
  have hqupper : q.eval (δ j) = eval δ (upperPrimitive j P) := by
    dsimp only [q]
    rw [eval_auxCoordinate, upperPrimitive, eval_upperSubst]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hderiv s) (hcont.intervalIntegrable 0 (δ j))
  rw [hqzero, sub_zero, hqupper] at h
  exact h.symm

theorem eval_legPoint (x : Fin 2 → ℝ) (v δ : Fin 4 → ℝ) (j : Fin 4)
    (d : Fin 2) (s : ℝ) :
    eval (Sum.elim δ (fun _ : Unit => s)) (legPoint x v j d) =
      x d + (∑ k : Fin 4, if k.val < j.val then
        ((![1, v k] : Fin 2 → ℝ) d) * δ k else 0) +
          ((![1, v j] : Fin 2 → ℝ) d) * s := by
  simp [legPoint, apply_ite]

/-- Exact accumulated height along the four signed affine legs. -/
theorem eval_brokenHeight (A B : MvPolynomial (Fin 2) ℝ)
    (x : Fin 2 → ℝ) (v δ : Fin 4 → ℝ) :
    eval δ (brokenHeight A B x v) = ∑ j : Fin 4,
      ∫ s in (0 : ℝ)..δ j, eval (Sum.elim δ (fun _ : Unit => s)) (legField A B x v j) := by
  rw [brokenHeight, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact eval_upperPrimitive_integral _ j δ

end Submission.Lib.K4ScalarSwitching.Switching
