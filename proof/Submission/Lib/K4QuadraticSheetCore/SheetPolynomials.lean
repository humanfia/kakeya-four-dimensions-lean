import Mathlib
import Submission.Lib.K4HiddenQuadratic
import Submission.Lib.K4HorizontalCoercivity.HorizontalAlgebra
import Submission.Lib.K4QuadraticSheetCore.SheetAlgebra

/-! Adapted from: here:o223 (session x0777, branch x0777). -/

/-!
# The projected second fundamental form as base polynomials

For `β` of total degree at most one and `γ` of total degree at most two in the three base
variables, `sffPoly α β γ i j` is the `(i,j)` entry of the projected second fundamental form
of the quadratic test `γ + β w + α w²`; it has total degree at most two. Along polynomial
vector fields `U, V` the bilinear combination `sffBP` evaluates to `sffB` at the local data,
and its directional derivatives evaluate to `sffD` plus the terms coming from the moving
fields. These are the polynomial objects to which Remez and coefficient bounds apply.
-/

namespace Submission.Lib.K4QuadraticSheetCore

open MvPolynomial

noncomputable section

/-- Polynomials in the three base variables `(t, Z, Y)`. -/
abbrev BasePoly := MvPolynomial (Fin 3) ℝ

/-- Directional derivative of a base polynomial at `p` along `W`. -/
def dirD (W : Fin 3 → ℝ) (P : BasePoly) (p : Fin 3 → ℝ) : ℝ :=
  W 0 * eval p (pderiv 0 P) + W 1 * eval p (pderiv 1 P) + W 2 * eval p (pderiv 2 P)

/-- Evaluation of a polynomial vector field. -/
def evalVec (p : Fin 3 → ℝ) (U : Fin 3 → BasePoly) : Fin 3 → ℝ := fun i => eval p (U i)

/-- Directional derivative of a polynomial vector field. -/
def dirVec (W : Fin 3 → ℝ) (U : Fin 3 → BasePoly) (p : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => dirD W (U i) p

/-- Gradient of a base polynomial at `p`. -/
def gradAt (P : BasePoly) (p : Fin 3 → ℝ) : Fin 3 → ℝ := fun i => eval p (pderiv i P)

/-- Hessian of a base polynomial at `p`. -/
def hessAt (P : BasePoly) (p : Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun i j => eval p (pderiv i (pderiv j P))

section Vanishing

variable (β γ : BasePoly)

theorem pderiv_pderiv_eq_zero_of_deg_le_one (hβ : β.totalDegree ≤ 1) (i k : Fin 3) :
    pderiv k (pderiv i β) = 0 := by
  have h1 := Submission.Lib.K4HiddenQuadratic.totalDegree_pderiv_le_pred β i
  have h0 : (pderiv i β).totalDegree = 0 := by omega
  rw [totalDegree_eq_zero_iff_eq_C.mp h0, pderiv_C]

theorem pderiv_pderiv_pderiv_eq_zero_of_deg_le_two (hγ : γ.totalDegree ≤ 2) (i j k : Fin 3) :
    pderiv k (pderiv i (pderiv j γ)) = 0 := by
  have h1 := Submission.Lib.K4HiddenQuadratic.totalDegree_pderiv_le_pred γ j
  have h2 := Submission.Lib.K4HiddenQuadratic.totalDegree_pderiv_le_pred (pderiv j γ) i
  have h0 : (pderiv i (pderiv j γ)).totalDegree = 0 := by omega
  rw [totalDegree_eq_zero_iff_eq_C.mp h0, pderiv_C]

theorem hessAt_symm (γ : BasePoly) (p : Fin 3 → ℝ) : SymH (hessAt γ p) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [hessAt, Submission.Lib.K4HorizontalCoercivity.pderiv_commute]

end Vanishing

section Form

variable (α : ℝ) (β γ : BasePoly)

/-- Entry `(i,j)` of the projected second fundamental form. -/
def sffPoly (i j : Fin 3) : BasePoly :=
  C 2 * γ * pderiv i β * pderiv j β - β * (pderiv i β * pderiv j γ + pderiv i γ * pderiv j β) +
    C (2 * α) * pderiv i γ * pderiv j γ + (β ^ 2 - C (4 * α) * γ) * pderiv i (pderiv j γ)

/-- The bilinear combination along polynomial vector fields. -/
def sffBP (U V : Fin 3 → BasePoly) : BasePoly :=
  ∑ i, ∑ j, U i * V j * sffPoly α β γ i j

/-- The discriminant polynomial `β² - 4αγ`. -/
def discP : BasePoly := β ^ 2 - C (4 * α) * γ

theorem eval_sffBP (U V : Fin 3 → BasePoly) (p : Fin 3 → ℝ) :
    eval p (sffBP α β γ U V) =
      sffB α (eval p γ) (eval p β) (gradAt γ p) (gradAt β p) (hessAt γ p)
        (evalVec p U) (evalVec p V) := by
  simp only [sffBP, sffPoly, Fin.sum_univ_three, map_add, map_sub, map_mul, map_pow, eval_C,
    sffB, dot3, bil3, gradAt, hessAt, evalVec]
  ring

theorem eval_discP (p : Fin 3 → ℝ) :
    eval p (discP α β γ) = discV α (eval p γ) (eval p β) := by
  simp only [discP, discV, map_sub, map_mul, map_pow, eval_C]

theorem dirD_discP (W p : Fin 3 → ℝ) :
    dirD W (discP α β γ) p = discD α (eval p β) (gradAt γ p) (gradAt β p) W := by
  simp only [dirD, discP, discD, dot3, gradAt, map_sub, map_mul, pderiv_mul, pderiv_C,
    pow_two, map_add, eval_C, zero_mul, add_zero, mul_zero, zero_add]
  ring

theorem dirD_sffBP (hβ : β.totalDegree ≤ 1) (hγ : γ.totalDegree ≤ 2)
    (U V : Fin 3 → BasePoly) (W p : Fin 3 → ℝ) :
    dirD W (sffBP α β γ U V) p =
      sffD α (eval p β) (gradAt γ p) (gradAt β p) (hessAt γ p) W (evalVec p U) (evalVec p V) +
      sffB α (eval p γ) (eval p β) (gradAt γ p) (gradAt β p) (hessAt γ p)
        (dirVec W U p) (evalVec p V) +
      sffB α (eval p γ) (eval p β) (gradAt γ p) (gradAt β p) (hessAt γ p)
        (evalVec p U) (dirVec W V p) := by
  have hb : ∀ i k : Fin 3, pderiv k (pderiv i β) = 0 :=
    fun i k => pderiv_pderiv_eq_zero_of_deg_le_one β hβ i k
  have hg : ∀ i j k : Fin 3, pderiv k (pderiv i (pderiv j γ)) = 0 :=
    fun i j k => pderiv_pderiv_pderiv_eq_zero_of_deg_le_two γ hγ i j k
  simp only [dirD, sffBP, sffPoly, Fin.sum_univ_three, map_add, map_sub, pderiv_mul,
    pow_two, pderiv_C, hb, hg, map_mul, eval_C, zero_mul, mul_zero, add_zero, zero_add,
    sub_zero, sffD, sffB, dot3, bil3, gradAt, hessAt, evalVec, dirVec]
  ring

end Form

end

end Submission.Lib.K4QuadraticSheetCore
