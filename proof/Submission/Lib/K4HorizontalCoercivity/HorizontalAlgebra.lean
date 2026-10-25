/-
Adapted from: here:o107
Written in this tree by x0353, commits b38e8db through 29b5a36.
-/
import Mathlib

/-!
The commutator calculation in the affine approximation argument of paper Lemma 8.6.
Multiplication of endomorphisms is composition. The abstract ring formulation also
applies to differential operators on any invariant space of smooth functions.
-/

namespace Submission.Lib.K4HorizontalCoercivity

section Operators

variable {R : Type*} [Ring R] (X Z T : R)

/-- A differentiated symmetrized horizontal Hessian recovers `3 T X`. -/
theorem horizontal_commutator_X
    (hT : X * Z - Z * X = T) (hXT : Commute X T) :
    X * (X * Z + Z * X) - 2 * (Z * (X * X)) = 3 * (T * X) := by
  calc
    _ = X * (X * Z - Z * X) + 2 * ((X * Z - Z * X) * X) := by noncomm_ring
    _ = X * T + 2 * (T * X) := by rw [hT]
    _ = 3 * (T * X) := by rw [hXT.eq]; noncomm_ring

/-- The other differentiated horizontal Hessian recovers `-3 T Z`. -/
theorem horizontal_commutator_Z
    (hT : X * Z - Z * X = T) (hZT : Commute Z T) :
    Z * (X * Z + Z * X) - 2 * (X * (Z * Z)) = -(3 * (T * Z)) := by
  calc
    _ = -(Z * (X * Z - Z * X) + 2 * ((X * Z - Z * X) * Z)) := by noncomm_ring
    _ = -(Z * T + 2 * (T * Z)) := by rw [hT]
    _ = -(3 * (T * Z)) := by rw [hZT.eq]; noncomm_ring

/-- Centrality of the first commutator recovers the missing vertical Hessian. -/
theorem horizontal_commutator_T
    (hT : X * Z - Z * X = T) (hXT : Commute X T) (hZT : Commute Z T) :
    X * (T * Z) - Z * (T * X) = T * T := by
  calc
    _ = T * (X * Z - Z * X) := by
      simp only [← mul_assoc, hXT.eq, hZT.eq]
      noncomm_ring
    _ = T * T := by rw [hT]

/-- The vertical second derivative uses only two derivatives of horizontal Hessians. -/
theorem horizontal_commutator_TT
    (hT : X * Z - Z * X = T) (hXT : Commute X T) (hZT : Commute Z T) :
    3 * (T * T) =
      2 * (X * X * (Z * Z)) + 2 * (Z * Z * (X * X)) -
        X * Z * (X * Z + Z * X) - Z * X * (X * Z + Z * X) := by
  have hX := horizontal_commutator_X X Z T hT hXT
  have hZ : 3 * (T * Z) = 2 * (X * (Z * Z)) - Z * (X * Z + Z * X) := by
    calc
      _ = -(Z * (X * Z + Z * X) - 2 * (X * (Z * Z))) := by
        rw [horizontal_commutator_Z X Z T hT hZT, neg_neg]
      _ = _ := by abel
  calc
    _ = X * (3 * (T * Z)) - Z * (3 * (T * X)) := by
      rw [← horizontal_commutator_T X Z T hT hXT hZT]
      noncomm_ring
    _ = _ := by rw [hZ, ← hX]; noncomm_ring

end Operators

section Kernel

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
  (X Z T : Module.End ℝ V)

/-- Vanishing horizontal Hessians imply vanishing mixed vertical derivatives. -/
theorem horizontal_kernel_vertical (hT : X * Z - Z * X = T)
    (hXT : Commute X T) (hZT : Commute Z T) (f : V)
    (hXX : X (X f) = 0) (hZZ : Z (Z f) = 0)
    (hXZ : X (Z f) + Z (X f) = 0) :
    T (X f) = 0 ∧ T (Z f) = 0 ∧ T (T f) = 0 := by
  have hTX : (3 : ℝ) • T (X f) = 0 := by
    have h := congrArg (fun L : Module.End ℝ V => L f)
      (horizontal_commutator_X X Z T hT hXT)
    simpa [Module.End.mul_apply, hXX, hXZ,
      ← Nat.cast_smul_eq_nsmul ℝ] using h.symm
  have hTZ : (3 : ℝ) • T (Z f) = 0 := by
    have h := congrArg (fun L : Module.End ℝ V => L f)
      (horizontal_commutator_Z X Z T hT hZT)
    simpa [Module.End.mul_apply, hZZ, hXZ,
      ← Nat.cast_smul_eq_nsmul ℝ] using congrArg Neg.neg h.symm
  have hTX0 : T (X f) = 0 := (smul_eq_zero.mp hTX).resolve_left (by norm_num)
  have hTZ0 : T (Z f) = 0 := (smul_eq_zero.mp hTZ).resolve_left (by norm_num)
  refine ⟨hTX0, hTZ0, ?_⟩
  have h := congrArg (fun L : Module.End ℝ V => L f)
    (horizontal_commutator_T X Z T hT hXT hZT)
  simpa [Module.End.mul_apply, hTX0, hTZ0] using h.symm

end Kernel

section EvaluatedBounds

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
  (X Z T : Module.End ℝ V) (ev : V →ₗ[ℝ] ℝ)

/-- Quantitative recovery of the vertical derivatives from differentiated horizontal Hessians. -/
theorem horizontal_vertical_bounds (hT : X * Z - Z * X = T)
    (hXT : Commute X T) (hZT : Commute Z T) (f : V) (E : ℝ)
    (hXsym : |ev (X (X (Z f) + Z (X f)))| ≤ E)
    (hZXX : |ev (Z (X (X f)))| ≤ E)
    (hZsym : |ev (Z (X (Z f) + Z (X f)))| ≤ E)
    (hXZZ : |ev (X (Z (Z f)))| ≤ E)
    (hXXZZ : |ev (X (X (Z (Z f))))| ≤ E)
    (hZZXX : |ev (Z (Z (X (X f))))| ≤ E)
    (hXZsym : |ev (X (Z (X (Z f) + Z (X f))))| ≤ E)
    (hZXsym : |ev (Z (X (X (Z f) + Z (X f))))| ≤ E) :
    |ev (T (X f))| ≤ E ∧ |ev (T (Z f))| ≤ E ∧ |ev (T (T f))| ≤ 2 * E := by
  have hX := congrArg (fun L : Module.End ℝ V => ev (L f))
    (horizontal_commutator_X X Z T hT hXT)
  have hZ := congrArg (fun L : Module.End ℝ V => ev (L f))
    (horizontal_commutator_Z X Z T hT hZT)
  have hTT := congrArg (fun L : Module.End ℝ V => ev (L f))
    (horizontal_commutator_TT X Z T hT hXT hZT)
  simp [Module.End.mul_apply] at hX hZ hTT
  simp only [map_add] at hXsym hZsym hXZsym hZXsym
  rcases abs_le.mp hXsym with ⟨hXs0, hXs1⟩
  rcases abs_le.mp hZXX with ⟨hZx0, hZx1⟩
  rcases abs_le.mp hZsym with ⟨hZs0, hZs1⟩
  rcases abs_le.mp hXZZ with ⟨hXz0, hXz1⟩
  rcases abs_le.mp hXXZZ with ⟨hXxz0, hXxz1⟩
  rcases abs_le.mp hZZXX with ⟨hZzx0, hZzx1⟩
  rcases abs_le.mp hXZsym with ⟨hXzs0, hXzs1⟩
  rcases abs_le.mp hZXsym with ⟨hZxs0, hZxs1⟩
  refine ⟨abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩⟩ <;>
    linarith

end EvaluatedBounds

section PolynomialOperators

noncomputable section

open MvPolynomial

abbrev HorizontalPoly := MvPolynomial (Fin 3) ℝ

/-- Ordinary partial derivatives commute; this follows directly from their coefficient formula. -/
theorem pderiv_commute (i j : Fin 3) (P : HorizontalPoly) :
    pderiv i (pderiv j P) = pderiv j (pderiv i P) := by
  ext m
  simp only [coeff_pderiv]
  by_cases h : i = j
  · subst j; rfl
  · simp only [Finsupp.add_apply, Finsupp.single_eq_of_ne h,
      Finsupp.single_eq_of_ne (Ne.symm h), add_zero]
    rw [show m + Finsupp.single i 1 + Finsupp.single j 1 =
      m + Finsupp.single j 1 + Finsupp.single i 1 by ac_rfl]
    ring

/-- The horizontal field `∂t - Z ∂Y`. -/
def horizontalX : Module.End ℝ HorizontalPoly :=
  (pderiv 0).toLinearMap - (X 1 : HorizontalPoly) • (pderiv 2).toLinearMap

/-- The horizontal field `∂Z + t ∂Y`. -/
def horizontalZ : Module.End ℝ HorizontalPoly :=
  (pderiv 1).toLinearMap + (X 0 : HorizontalPoly) • (pderiv 2).toLinearMap

/-- The vertical field `2 ∂Y`. -/
def horizontalT : Module.End ℝ HorizontalPoly :=
  (2 : ℝ) • (pderiv 2).toLinearMap

theorem horizontalX_apply (P : HorizontalPoly) :
    horizontalX P = pderiv 0 P - X 1 * pderiv 2 P := rfl

theorem horizontalZ_apply (P : HorizontalPoly) :
    horizontalZ P = pderiv 1 P + X 0 * pderiv 2 P := rfl

theorem horizontalT_apply (P : HorizontalPoly) :
    horizontalT P = 2 * pderiv 2 P := by
  simp [horizontalT, Algebra.smul_def, map_ofNat]

theorem horizontal_bracket :
    horizontalX * horizontalZ - horizontalZ * horizontalX = horizontalT := by
  apply LinearMap.ext
  intro P
  simp only [LinearMap.sub_apply, Module.End.mul_apply, horizontalX_apply,
    horizontalZ_apply, horizontalT_apply, map_sub, map_add, pderiv_mul]
  simp only [pderiv_X, Pi.single_apply, Fin.reduceEq, ite_true, ite_false,
    one_mul, zero_mul, zero_add]
  rw [pderiv_commute 1 0 P, pderiv_commute 2 0 P, pderiv_commute 2 1 P]
  ring

theorem horizontalT_central_X : Commute horizontalX horizontalT := by
  apply LinearMap.ext
  intro P
  simp only [Module.End.mul_apply, horizontalX_apply, horizontalT_apply,
    map_sub, pderiv_mul]
  simp only [pderiv_X, Pi.single_apply, Fin.reduceEq, ite_false,
    zero_mul, zero_add]
  simp only [show ∀ i : Fin 3, pderiv i (2 : HorizontalPoly) = 0 from
    fun i => (pderiv i).map_natCast 2, zero_mul, zero_add]
  rw [pderiv_commute 2 0 P]
  ring

theorem horizontalT_central_Z : Commute horizontalZ horizontalT := by
  apply LinearMap.ext
  intro P
  simp only [Module.End.mul_apply, horizontalZ_apply, horizontalT_apply,
    map_add, pderiv_mul]
  simp only [pderiv_X, Pi.single_apply, Fin.reduceEq, ite_false,
    zero_mul, zero_add]
  simp only [show ∀ i : Fin 3, pderiv i (2 : HorizontalPoly) = 0 from
    fun i => (pderiv i).map_natCast 2, zero_mul, zero_add]
  rw [pderiv_commute 2 1 P]
  ring

end

end PolynomialOperators

end Submission.Lib.K4HorizontalCoercivity
