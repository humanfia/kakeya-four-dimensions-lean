/- Adapted from this LOT tree, o197, session x0690, Window/Normalize.lean,
   branch snapshot f7206748; preserving original attributions below. -/
import Submission.Obl.k4_raw_localized_native_systems.Definitions
import Submission.Lib.K4ChartLifting

/-!
# Normalized coordinates of an earlier witness chart

An earlier (true) chart with time block `[t₀, t₀ + q]`, center `c + t u` and
spatial frame `D` normalizes a graph point `(t, y, w)` to
`((t - t₀) / q, D⁻¹ (y - c - t u), B w)`.  The hidden coordinate is scaled by
the native derivative scale `B`, so that tests of the original problem become
tests whose hidden derivatives are of unit size.

`hsubst F B` expresses the original coordinates through the normalized ones;
substituting it into a test gives the normalized test, with the same values,
total degree at most that of the test, and hidden derivatives divided by `B`.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.Window

open MeasureTheory MvPolynomial
open Submission.Lib.K4ChartLifting

noncomputable section

/-- Original graph coordinates through normalized ones:
`t = t₀ + q τ`, `y = c + t u + D z`, `w = h / B`. -/
def hsubst (F : Frame) (B : ℝ) : Fin 4 → MvPolynomial (Fin 4) ℝ :=
  ![C F.t₀ + C F.q * X 0,
    C (F.c 0) + (C F.t₀ + C F.q * X 0) * C (F.u 0) + C (F.D 0 0) * X 1 + C (F.D 0 1) * X 2,
    C (F.c 1) + (C F.t₀ + C F.q * X 0) * C (F.u 1) + C (F.D 1 0) * X 1 + C (F.D 1 1) * X 2,
    C B⁻¹ * X 3]

/-- The normalized point of an original graph point. -/
def normPt (F : Frame) (B : ℝ) (v : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![(v 0 - F.t₀) / F.q,
    F.D⁻¹ 0 0 * (v 1 - F.c 0 - v 0 * F.u 0) + F.D⁻¹ 0 1 * (v 2 - F.c 1 - v 0 * F.u 1),
    F.D⁻¹ 1 0 * (v 1 - F.c 0 - v 0 * F.u 0) + F.D⁻¹ 1 1 * (v 2 - F.c 1 - v 0 * F.u 1),
    B * v 3]

theorem continuous_normPt (F : Frame) (B : ℝ) : Continuous (normPt F B) := by
  unfold normPt
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp <;> fun_prop

/-- The substitution evaluated at the normalized point returns the original point. -/
theorem eval_hsubst_normPt (F : Frame) {B : ℝ} (hq : F.q ≠ 0) (hD : IsUnit F.D.det)
    (hB : B ≠ 0) (v : Fin 4 → ℝ) :
    (fun i => eval (normPt F B v) (hsubst F B i)) = v := by
  have hDD : F.D * F.D⁻¹ = 1 := Matrix.mul_nonsing_inv _ hD
  have h00 : F.D 0 0 * F.D⁻¹ 0 0 + F.D 0 1 * F.D⁻¹ 1 0 = 1 := by
    have := congrFun (congrFun hDD 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h01 : F.D 0 0 * F.D⁻¹ 0 1 + F.D 0 1 * F.D⁻¹ 1 1 = 0 := by
    have := congrFun (congrFun hDD 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h10 : F.D 1 0 * F.D⁻¹ 0 0 + F.D 1 1 * F.D⁻¹ 1 0 = 0 := by
    have := congrFun (congrFun hDD 1) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h11 : F.D 1 0 * F.D⁻¹ 0 1 + F.D 1 1 * F.D⁻¹ 1 1 = 1 := by
    have := congrFun (congrFun hDD 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  funext i
  fin_cases i
  · simp [hsubst, normPt]
    field_simp
    ring
  · simp [hsubst, normPt]
    field_simp
    linear_combination (v 1 - F.c 0 - v 0 * F.u 0) * h00 + (v 2 - F.c 1 - v 0 * F.u 1) * h01
  · simp [hsubst, normPt]
    field_simp
    linear_combination (v 1 - F.c 0 - v 0 * F.u 0) * h10 + (v 2 - F.c 1 - v 0 * F.u 1) * h11
  · simp [hsubst, normPt]
    field_simp

theorem totalDegree_hsubst_le (F : Frame) (B : ℝ) (i : Fin 4) :
    (hsubst F B i).totalDegree ≤ 1 := by
  have hX : ∀ i : Fin 4, (X i : MvPolynomial (Fin 4) ℝ).totalDegree ≤ 1 := fun i => deg1_X i
  have ht : (C F.t₀ + C F.q * X 0 : MvPolynomial (Fin 4) ℝ).totalDegree ≤ 1 :=
    deg1_add (deg1_C _) (deg1_C_mul _ (hX 0))
  fin_cases i
  · exact ht
  · exact deg1_add (deg1_add (deg1_add (deg1_C _) (deg1_mul_C _ ht)) (deg1_C_mul _ (hX 1)))
      (deg1_C_mul _ (hX 2))
  · exact deg1_add (deg1_add (deg1_add (deg1_C _) (deg1_mul_C _ ht)) (deg1_C_mul _ (hX 1)))
      (deg1_C_mul _ (hX 2))
  · exact deg1_C_mul _ (hX 3)

theorem pderiv_three_hsubst_three (F : Frame) (B : ℝ) :
    pderiv (3 : Fin 4) (hsubst F B 3) = C B⁻¹ := by
  simp [hsubst]

theorem pderiv_three_hsubst_of_ne (F : Frame) (B : ℝ) (j : Fin 4) (hj : j ≠ 3) :
    pderiv (3 : Fin 4) (hsubst F B j) = 0 := by
  fin_cases j <;> simp_all [hsubst, pderiv_X]

/-- The normalized test: the original test written in normalized coordinates. -/
def normalizedTest (F : Frame) (B : ℝ) (R : MvPolynomial (Fin 4) ℝ) : MvPolynomial (Fin 4) ℝ :=
  bind₁ (hsubst F B) R

theorem totalDegree_normalizedTest_le (F : Frame) (B : ℝ) (R : MvPolynomial (Fin 4) ℝ) :
    (normalizedTest F B R).totalDegree ≤ R.totalDegree :=
  totalDegree_bind₁_le_of_le_one _ (totalDegree_hsubst_le F B) R

theorem pderiv_normalizedTest (F : Frame) (B : ℝ) (R : MvPolynomial (Fin 4) ℝ) :
    pderiv (3 : Fin 4) (normalizedTest F B R) =
      normalizedTest F B (pderiv (3 : Fin 4) R) * C B⁻¹ := by
  rw [normalizedTest, pderiv_bind₁, Finset.sum_eq_single (3 : Fin 4)]
  · rw [pderiv_three_hsubst_three, normalizedTest]
  · intro j _ hj
    rw [pderiv_three_hsubst_of_ne F B j hj, mul_zero]
  · simp

theorem eval_normalizedTest (F : Frame) {B : ℝ} (hq : F.q ≠ 0) (hD : IsUnit F.D.det)
    (hB : B ≠ 0) (R : MvPolynomial (Fin 4) ℝ) (v : Fin 4 → ℝ) :
    eval (normPt F B v) (normalizedTest F B R) = eval v R := by
  rw [normalizedTest, eval_bind₁', eval_hsubst_normPt F hq hD hB v]

/-- Values and both hidden derivatives of a normalized test, at a normalized point. -/
theorem normalizedTest_bounds (F : Frame) {B : ℝ} (hq : F.q ≠ 0) (hD : IsUnit F.D.det)
    (hB : 0 < B) (R : MvPolynomial (Fin 4) ℝ) (v : Fin 4 → ℝ) :
    eval (normPt F B v) (normalizedTest F B R) = eval v R ∧
    eval (normPt F B v) (pderiv (3 : Fin 4) (normalizedTest F B R)) =
      eval v (pderiv (3 : Fin 4) R) / B ∧
    eval (normPt F B v) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) (normalizedTest F B R))) =
      eval v (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) R)) / B ^ 2 := by
  have hB0 : B ≠ 0 := hB.ne'
  refine ⟨eval_normalizedTest F hq hD hB0 R v, ?_, ?_⟩
  · rw [pderiv_normalizedTest, MvPolynomial.eval_mul, eval_C,
      eval_normalizedTest F hq hD hB0]
    field_simp
  · rw [pderiv_normalizedTest, Derivation.leibniz, pderiv_C, smul_zero, zero_add,
      smul_eq_mul, pderiv_normalizedTest]
    simp only [MvPolynomial.eval_mul, eval_C, eval_normalizedTest F hq hD hB0]
    field_simp

end
end Submission.Obl.k4_raw_localized_native_systems.Window
