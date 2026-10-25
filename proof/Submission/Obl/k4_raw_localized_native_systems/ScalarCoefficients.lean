/- Adapted from this LOT tree, o197, session x0690, ScalarCoefficients.lean,
   branch snapshot 9f1b6476; preserving original attributions below. -/
import Submission.Obl.k4_raw_localized_native_systems.Definitions
import Submission.Obl.k4_raw_localized_native_systems.Pairing.VelocityPinning
import Submission.Obl.k4_horizon_chart_assembly.NativeGeometry

namespace Submission.Obl.k4_raw_localized_native_systems

open MeasureTheory Set
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section
set_option maxRecDepth 4096

/-- The frozen three-coordinate tangent has zero time component. -/
def planarTangent (e : Plane) : Fin 3 → ℝ := ![0, e 0, e 1]

def tangentValue (e : Plane) (l : Line) (t : ℝ) : ℝ := inner ℝ (y l t) e

def fullTimeCoefficients (P : MvPolynomial (Fin 4) ℝ) (e : Plane)
    (A : Set Line) : Line → Fin 5 → ℝ := nativeCoeff P 0 1 0 (planarTangent e) A

def rawFullTimeCoefficients (P : MvPolynomial (Fin 4) ℝ) (e : Plane)
    (l : Line) : Fin 5 → ℝ :=
  ![tangentValue e l 0, tangentValue e l 1 - tangentValue e l 0,
    MvPolynomial.eval (x l 0) P,
    4 * MvPolynomial.eval (x l (1 / 2)) P - 3 * MvPolynomial.eval (x l 0) P -
      MvPolynomial.eval (x l 1) P,
    2 * (MvPolynomial.eval (x l 1) P + MvPolynomial.eval (x l 0) P -
      2 * MvPolynomial.eval (x l (1 / 2)) P)]

theorem fullTimeCoefficients_eq_indicator (P : MvPolynomial (Fin 4) ℝ)
    (e : Plane) (A : Set Line) :
    fullTimeCoefficients P e A = A.indicator (rawFullTimeCoefficients P e) := by
  classical
  funext l
  by_cases hl : l ∈ A
  · simp only [fullTimeCoefficients, nativeCoeff, hl, ite_true, indicator_of_mem hl,
      zero_add, add_zero]
    congr 1 <;> simp [planarTangent, tangentValue, Pairing.inner_fin2, y, x,
      Fin.sum_univ_three] <;> ring
  · simp only [fullTimeCoefficients, nativeCoeff, hl, ite_false, indicator_of_notMem hl]

theorem measurable_fullTimeCoefficients (P : MvPolynomial (Fin 4) ℝ)
    (e : Plane) {A : Set Line} (hA : MeasurableSet A) :
    Measurable (fullTimeCoefficients P e A) := by
  have hX (t : ℝ) : Measurable (fun l : Line => MvPolynomial.eval (x l t) P) := by
    apply (MvPolynomial.continuous_eval P).measurable.comp
    unfold x
    fun_prop
  have hY (t : ℝ) : Measurable (fun l : Line => tangentValue e l t) := by
    unfold tangentValue y x
    fun_prop
  rw [fullTimeCoefficients_eq_indicator]
  apply Measurable.indicator _ hA
  apply Measurable.of_eval
  intro i
  fin_cases i <;> simp only [rawFullTimeCoefficients, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val, Fin.reduceSucc]
  · exact hY 0
  · exact (hY 1).sub (hY 0)
  · exact hX 0
  · exact (((hX (1 / 2)).const_mul 4).sub ((hX 0).const_mul 3)).sub (hX 1)
  · exact (((hX 1).add (hX 0)).sub ((hX (1 / 2)).const_mul 2)).const_mul 2

/-- The scalar interpolation of a native degree-two signal is exact at all times. -/
theorem trace_quadratic (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2) (l : Line) :
    k4_eligibility_sign_description.Quadratic (fun t => MvPolynomial.eval (x l t) P) := by
  have h := k4_eligibility_sign_description.Quadratic.mv_line P hP (x l 0)
    ![1, l.2 3, l.2 4, l.2 5]
  convert h using 1
  funext t
  apply congrArg (fun z : Fin 4 → ℝ => MvPolynomial.eval z P)
  funext i
  fin_cases i <;> simp [x]

theorem fullTimeCoefficients_signal (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (e : Plane) {A : Set Line} {l : Line} (hl : l ∈ A) (t : ℝ) :
    scalarX (fullTimeCoefficients P e A l) t = MvPolynomial.eval (x l t) P := by
  rw [fullTimeCoefficients_eq_indicator, indicator_of_mem hl]
  have h := k4_horizon_chart_assembly.quadraticCoefficients_eval (trace_quadratic P hP l) t
  convert h using 1
  simp [scalarX, rawFullTimeCoefficients,
    k4_horizon_chart_assembly.quadraticCoefficients,
    k4_scalar_coefficient_clustering.quadratic]
  ring

theorem fullTimeCoefficients_position (P : MvPolynomial (Fin 4) ℝ)
    (e : Plane) {A : Set Line} {l : Line} (hl : l ∈ A) (t : ℝ) :
    scalarY (fullTimeCoefficients P e A l) t = tangentValue e l t := by
  rw [fullTimeCoefficients_eq_indicator, indicator_of_mem hl]
  simp [scalarY, rawFullTimeCoefficients, tangentValue, Pairing.inner_fin2, y, x]
  ring

/-- Whole-time signal and tangent bounds give global bounds after clipping
outside the full original assignment. -/
theorem fullTimeCoefficients_bound (P : MvPolynomial (Fin 4) ℝ) (e : Plane)
    (A : Set Line) {K : ℝ} (hK : 0 ≤ K)
    (hY : ∀ l ∈ A, ∀ t ∈ Icc (0 : ℝ) 1, |tangentValue e l t| ≤ K)
    (hX : ∀ l ∈ A, ∀ t ∈ Icc (0 : ℝ) 1, |MvPolynomial.eval (x l t) P| ≤ K) :
    ∀ l i, |fullTimeCoefficients P e A l i| ≤ 8 * K := by
  intro l i
  rw [fullTimeCoefficients_eq_indicator]
  by_cases hl : l ∈ A
  · rw [indicator_of_mem hl]
    have hy0 := abs_le.mp (hY l hl 0 (by norm_num))
    have hy1 := abs_le.mp (hY l hl 1 (by norm_num))
    have hx0 := abs_le.mp (hX l hl 0 (by norm_num))
    have hxm := abs_le.mp (hX l hl (1 / 2) (by norm_num))
    have hx1 := abs_le.mp (hX l hl 1 (by norm_num))
    fin_cases i <;> dsimp [rawFullTimeCoefficients] <;>
      rw [abs_le] <;> constructor <;> linarith
  · simp only [indicator_of_notMem hl, Pi.zero_apply, abs_zero]
    positivity

end
end Submission.Obl.k4_raw_localized_native_systems
