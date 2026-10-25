-- Adapted from this LOT tree, o241, session x0834, branch x0834 at 511ef044.
-- Original file: Submission/Obl/k4_contact_equal_rate_affine_palettes/LabelChart.lean
import Mathlib
import Submission.Lib.K4ContactNormalization
import Submission.Lib.K4ChartLifting.PolyAlgebra
import Submission.Lib.K4ChartLifting.Normalize
import Submission.Obl.k4_stable_native_signal_oscillation.BasePolynomials
import Submission.Lib.K4QuadraticSheetCore.SheetLines

/-!
# The label chart: from a true block to the normalized unit cube

A true block has left time `t₀`, length `q`, horizontal centre `Z₀` and transverse centre
`Y₀`. Its chart is the Heisenberg zoom `t ↦ (t - t₀)/q`, `Z ↦ (Z - Z₀)/q`,
`Y ↦ (Y - Y₀ + Z₀ (t - t₀) - t₀ (Z - Z₀))/q²`, followed by the contact scaling of `(Z, Y)` by
`1/μ` and the contact translation `Z ↦ Z + 1/2`, `Y ↦ Y - t/2 + 3/4`. All three steps send
contact lines to contact lines; together they send the true box into the unit cube once `μ` is
large compared to its normalized horizontal and transverse extent. The hidden coordinate is
divided by the hidden width `a`.

* `chartCoeff`: the new line coefficients; the velocity is divided by `μ`
  (`chartCoeff_three`) and the contact defect by `q μ` (`chartCoeff_contact`).
* `chartInv`: the original base point of a normalized one, with
  `chartInv (lineP (chartCoeff b) σ)` the original base point at time `t₀ + q σ`.
* `chartGamma`, `chartBeta`, `chartAlpha`: the test of the label in the chart, so that
  `testVal` and `testDer` of the new line are the original test divided by `a` and the
  original hidden derivative at time `t₀ + q σ`.

These are exact identities; the bounds are in `LabelAdapter`.
-/

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover

open Submission.Lib.K4QuadraticSheetCore

open MvPolynomial Set
open Submission.Lib.K4ContactNormalization
open Submission.Lib.K4ChartLifting
open Submission.Obl.k4_stable_native_signal_oscillation
open Submission.Obl.k4_quadratic_atlas_normalization

noncomputable section

section Chart

variable (t₀ q μ Z₀ Y₀ a : ℝ)

/-- The normalized base point of an original base point `(t, Z, Y)`. -/
def chartPoint (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![(x 0 - t₀) / q,
    (x 1 - Z₀) / (q * μ) + 1 / 2,
    (x 2 - Y₀ + Z₀ * (x 0 - t₀) - t₀ * (x 1 - Z₀)) / (q ^ 2 * μ) - (x 0 - t₀) / (2 * q) +
      3 / 4]

/-- The original base point of a normalized base point. -/
def chartInv (p : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![t₀ + q * p 0,
    Z₀ + q * μ * (p 1 - 1 / 2),
    Y₀ - Z₀ * (q * p 0) + t₀ * (q * μ * (p 1 - 1 / 2)) +
      q ^ 2 * μ * (p 2 + p 0 / 2 - 3 / 4)]

/-- The substitution giving the original coordinates as affine polynomials in the new ones. -/
def chartSubst : Fin 3 → BasePoly :=
  ![C t₀ + C q * X 0,
    C Z₀ + C (q * μ) * (X 1 - C (1 / 2)),
    C Y₀ - C Z₀ * (C q * X 0) + C t₀ * (C (q * μ) * (X 1 - C (1 / 2))) +
      C (q ^ 2 * μ) * (X 2 + C (1 / 2) * X 0 - C (3 / 4))]

/-- The line coefficients of a trajectory in the chart (time `σ` stands for `t₀ + q σ`). -/
def chartCoeff (b : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![(b 0 + t₀ * b 3 - Z₀) / (q * μ) + 1 / 2,
    (b 1 + t₀ * b 4 - Y₀ - t₀ * b 0 - t₀ ^ 2 * b 3 + t₀ * Z₀) / (q ^ 2 * μ) + 3 / 4,
    (b 2 + t₀ * b 5) / a,
    b 3 / μ,
    (b 4 + Z₀ - t₀ * b 3) / (q * μ) - 1 / 2,
    q * b 5 / a]

/-- The original base point of a trajectory at time `t`. -/
def basePt (b : Fin 6 → ℝ) (t : ℝ) : Fin 3 → ℝ := ![t, b 0 + t * b 3, b 1 + t * b 4]

theorem eval_chartSubst (p : Fin 3 → ℝ) :
    (fun i => eval p (chartSubst t₀ q μ Z₀ Y₀ i)) = chartInv t₀ q μ Z₀ Y₀ p := by
  funext i
  fin_cases i <;> simp only [chartSubst, chartInv, Matrix.cons_val, map_add, map_sub, map_mul,
    eval_C, eval_X, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> ring

theorem chartSubst_degree (i : Fin 3) : (chartSubst t₀ q μ Z₀ Y₀ i).totalDegree ≤ 1 := by
  fin_cases i
  · exact deg1_add (deg1_C _) (deg1_mul_C' (deg1_X _))
  · exact deg1_add (deg1_C _) (deg1_C_mul _ (deg1_sub (deg1_X _) (deg1_C _)))
  · exact deg1_add (deg1_add (deg1_sub (deg1_C _) (deg1_C_mul _ (deg1_C_mul _ (deg1_X _))))
      (deg1_C_mul _ (deg1_C_mul _ (deg1_sub (deg1_X _) (deg1_C _)))))
      (deg1_C_mul _ (deg1_sub (deg1_add (deg1_X _) (deg1_C_mul _ (deg1_X _))) (deg1_C _)))
where
  deg1_mul_C' {p : BasePoly} (hp : p.totalDegree ≤ 1) : (C q * p).totalDegree ≤ 1 :=
    deg1_C_mul q hp

theorem chartInv_chartPoint (hq : q ≠ 0) (hμ : μ ≠ 0) (x : Fin 3 → ℝ) :
    chartInv t₀ q μ Z₀ Y₀ (chartPoint t₀ q μ Z₀ Y₀ x) = x := by
  funext i
  fin_cases i <;> simp [chartInv, chartPoint] <;> field_simp <;> ring

theorem chartPoint_chartInv (hq : q ≠ 0) (hμ : μ ≠ 0) (p : Fin 3 → ℝ) :
    chartPoint t₀ q μ Z₀ Y₀ (chartInv t₀ q μ Z₀ Y₀ p) = p := by
  funext i
  fin_cases i <;> simp [chartInv, chartPoint] <;> field_simp <;> ring

/-- The chart sends the trajectory at time `t₀ + q σ` to the new line at time `σ`. -/
theorem lineP_chartCoeff (hq : q ≠ 0) (hμ : μ ≠ 0) (b : Fin 6 → ℝ) (σ : ℝ) :
    lineP (chartCoeff t₀ q μ Z₀ Y₀ a b) σ =
      chartPoint t₀ q μ Z₀ Y₀ (basePt b (t₀ + q * σ)) := by
  funext i
  fin_cases i <;> simp [lineP, chartCoeff, chartPoint, basePt] <;> field_simp <;> ring

theorem chartInv_lineP_chartCoeff (hq : q ≠ 0) (hμ : μ ≠ 0) (b : Fin 6 → ℝ) (σ : ℝ) :
    chartInv t₀ q μ Z₀ Y₀ (lineP (chartCoeff t₀ q μ Z₀ Y₀ a b) σ) = basePt b (t₀ + q * σ) := by
  rw [lineP_chartCoeff t₀ q μ Z₀ Y₀ a hq hμ, chartInv_chartPoint t₀ q μ Z₀ Y₀ hq hμ]

theorem lineW_chartCoeff (ha : a ≠ 0) (b : Fin 6 → ℝ) (σ : ℝ) :
    a * lineW (chartCoeff t₀ q μ Z₀ Y₀ a b) σ = b 2 + (t₀ + q * σ) * b 5 := by
  simp only [lineW, chartCoeff, Matrix.cons_val]
  field_simp
  ring

@[simp] theorem chartCoeff_three (b : Fin 6 → ℝ) :
    chartCoeff t₀ q μ Z₀ Y₀ a b 3 = b 3 / μ := by
  simp [chartCoeff]

theorem chartCoeff_contact (hq : q ≠ 0) (hμ : μ ≠ 0) (b : Fin 6 → ℝ) :
    chartCoeff t₀ q μ Z₀ Y₀ a b 4 + chartCoeff t₀ q μ Z₀ Y₀ a b 0 = (b 4 + b 0) / (q * μ) := by
  simp only [chartCoeff, Matrix.cons_val]
  field_simp
  ring

/-- The frozen point is the base point with the hidden value appended. -/
theorem point_eq_snoc (b : Fin 6 → ℝ) (t : ℝ) :
    point b t = Fin.snoc (basePt b t) (b 2 + t * b 5) := by
  funext i
  fin_cases i <;> rfl

end Chart

section Test

/-- The hidden derivative of a quadratic test is affine in the hidden coordinate, with base
slope `restrictBase (pderiv 3 P)`. Inlined from `Submission.Obl.k4_stable_native_signal_oscillation`
(file `LinearAlgebra.lean`, lemma `eval_baseSlope`), whose module is not in that obligation's
import closure. -/
theorem eval_snoc_pderiv_hidden (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (x : Fin 3 → ℝ) (w : ℝ) :
    eval (Fin.snoc x w) (pderiv 3 P) =
      eval x (restrictBase (pderiv 3 P)) + curvature P 3 * w := by
  have hh := quadratic_coordinate_derivative P hP (Fin.snoc x 0) 3 w
  have hlast : (Fin.snoc x (0 : ℝ) : Fin 4 → ℝ) 3 = 0 := by rfl
  rw [hlast, zero_add] at hh
  rw [show Function.update (Fin.snoc x (0 : ℝ) : Fin 4 → ℝ) 3 w = Fin.snoc x w by
    exact update_snoc_hidden _ _ _] at hh
  simpa only [eval_restrictBase] using hh

variable (t₀ q μ Z₀ Y₀ a : ℝ) (F : MvPolynomial (Fin 4) ℝ)

/-- The hidden-free part of the label test in the chart, divided by the hidden width. -/
def chartGamma : BasePoly := C a⁻¹ * bind₁ (chartSubst t₀ q μ Z₀ Y₀) (restrictBase F)

/-- The hidden slope of the label test in the chart. -/
def chartBeta : BasePoly := bind₁ (chartSubst t₀ q μ Z₀ Y₀) (restrictBase (pderiv 3 F))

/-- The hidden curvature of the label test in the chart, times the hidden width. -/
def chartAlpha : ℝ := a * curvature F 3 / 2

theorem chartGamma_degree (hF : F.totalDegree ≤ 2) :
    (chartGamma t₀ q μ Z₀ Y₀ a F).totalDegree ≤ 2 := by
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  exact (totalDegree_bind₁_le_of_le_one _ (chartSubst_degree t₀ q μ Z₀ Y₀) _).trans
    ((totalDegree_restrictBase _).trans hF)

theorem chartBeta_degree (hF : F.totalDegree ≤ 2) :
    (chartBeta t₀ q μ Z₀ Y₀ F).totalDegree ≤ 1 := by
  refine (totalDegree_bind₁_le_of_le_one _ (chartSubst_degree t₀ q μ Z₀ Y₀) _).trans
    ((totalDegree_restrictBase _).trans ?_)
  have h := Submission.Obl.k4_quadratic_slope_volume.totalDegree_pderiv_le F 3
  omega

theorem eval_chartGamma (p : Fin 3 → ℝ) :
    eval p (chartGamma t₀ q μ Z₀ Y₀ a F) =
      a⁻¹ * eval (chartInv t₀ q μ Z₀ Y₀ p) (restrictBase F) := by
  rw [chartGamma, eval_mul, eval_C, eval_bind₁', eval_chartSubst]

theorem eval_chartBeta (p : Fin 3 → ℝ) :
    eval p (chartBeta t₀ q μ Z₀ Y₀ F) =
      eval (chartInv t₀ q μ Z₀ Y₀ p) (restrictBase (pderiv 3 F)) := by
  rw [chartBeta, eval_bind₁', eval_chartSubst]

/-- The test in the chart is the original test divided by the hidden width. -/
theorem chart_test_eval (hF : F.totalDegree ≤ 2) (ha : a ≠ 0) (p : Fin 3 → ℝ) (w : ℝ) :
    eval p (chartGamma t₀ q μ Z₀ Y₀ a F) + eval p (chartBeta t₀ q μ Z₀ Y₀ F) * w +
        chartAlpha a F * w ^ 2 =
      eval (Fin.snoc (chartInv t₀ q μ Z₀ Y₀ p) (a * w)) F / a := by
  have hlast : (Fin.last 3 : Fin 4) = 3 := rfl
  rw [eval_snoc_quadratic F hF, eval_chartGamma, eval_chartBeta, chartAlpha, hlast]
  field_simp

/-- The hidden derivative in the chart is the original hidden derivative. -/
theorem chart_testDer_eval (hF : F.totalDegree ≤ 2) (p : Fin 3 → ℝ) (w : ℝ) :
    eval p (chartBeta t₀ q μ Z₀ Y₀ F) + 2 * chartAlpha a F * w =
      eval (Fin.snoc (chartInv t₀ q μ Z₀ Y₀ p) (a * w)) (pderiv 3 F) := by
  rw [eval_snoc_pderiv_hidden F hF, eval_chartBeta, chartAlpha]
  ring

/-- The curvature in the chart is the original second hidden derivative times `a / 2`. -/
theorem two_chartAlpha (hF : F.totalDegree ≤ 2) (x : Fin 4 → ℝ) :
    2 * chartAlpha a F = a * eval x (pderiv 3 (pderiv 3 F)) := by
  rw [second_pderiv_eq_curvature F hF, eval_C, chartAlpha]
  ring

/-- Along a transported line, the chart test is the original test along the trajectory. -/
theorem testVal_chartCoeff (hF : F.totalDegree ≤ 2) (hq : q ≠ 0) (hμ : μ ≠ 0) (ha : a ≠ 0)
    (b : Fin 6 → ℝ) (σ : ℝ) :
    testVal (chartAlpha a F) (chartBeta t₀ q μ Z₀ Y₀ F) (chartGamma t₀ q μ Z₀ Y₀ a F)
        (chartCoeff t₀ q μ Z₀ Y₀ a b) σ =
      eval (point b (t₀ + q * σ)) F / a := by
  rw [testVal, chart_test_eval t₀ q μ Z₀ Y₀ a F hF ha,
    chartInv_lineP_chartCoeff t₀ q μ Z₀ Y₀ a hq hμ, lineW_chartCoeff t₀ q μ Z₀ Y₀ a ha,
    point_eq_snoc]

theorem testDer_chartCoeff (hF : F.totalDegree ≤ 2) (hq : q ≠ 0) (hμ : μ ≠ 0) (ha : a ≠ 0)
    (b : Fin 6 → ℝ) (σ : ℝ) :
    testDer (chartAlpha a F) (chartBeta t₀ q μ Z₀ Y₀ F) (chartCoeff t₀ q μ Z₀ Y₀ a b) σ =
      eval (point b (t₀ + q * σ)) (pderiv 3 F) := by
  rw [testDer, chart_testDer_eval t₀ q μ Z₀ Y₀ a F hF,
    chartInv_lineP_chartCoeff t₀ q μ Z₀ Y₀ a hq hμ, lineW_chartCoeff t₀ q μ Z₀ Y₀ a ha,
    point_eq_snoc]

end Test

end

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover
