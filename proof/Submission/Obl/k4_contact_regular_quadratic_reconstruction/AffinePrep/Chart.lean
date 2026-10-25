import Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer.UnitContactBox
import Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer.ContactChart
import Submission.Lib.K4ContactNormalization.ResidualNormalization
import Submission.Lib.K4AffineMeshCaps.Transport
import Submission.Lib.K4QuadraticSheetCore

/-!
# The normalized chart of a coarse label block

The base chart is the Heisenberg zoom of the block `[t₀, t₀ + q]` followed by the unit-box
contact map `unitContactBase B`; it is an affine map `z ↦ normMat z + normOff`.
A line is normalized by first subtracting an affine hidden predictor `L'` and dividing by the fine
width `c`, then applying the base chart; the normalized time is `σ = (t - t₀) / q`.

The shifted test `G` (written in the coordinates `(t, Z, Y, w - L)` with `L' = L + γ`) becomes
* `tildeTest G` in normalized base coordinates and the unscaled residual `w - L'`;
* `hatTest G = c⁻¹ G(…, c y + γ)` in normalized base coordinates and the scaled residual
  `y = (w - L') / c`, which is the test fed to the affine-sheet core.
-/

namespace Submission.Obl.k4_contact_regular_quadratic_reconstruction.AffinePrep

open MvPolynomial Set
open Submission.Lib.K4ContactNormalization
open Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer

noncomputable section

/-- Parameters of a normalized chart: block start `t₀`, block length `q`, centre `(Z₀, Y₀)`,
unit-box size `B`, fine width `c`, the affine predictor `L` of the shifted candidate and the
quarter-band shift `γ`. -/
structure ChartData where
  t₀ : ℝ
  q : ℝ
  Z₀ : ℝ
  Y₀ : ℝ
  B : ℝ
  c : ℝ
  L : Fin 4 → ℝ
  γ : ℝ

/-- The base point of an original line at time `t`. -/
def basePt (b : Fin 6 → ℝ) (t : ℝ) : Fin 3 → ℝ := ![t, b 0 + t * b 3, b 1 + t * b 4]

namespace ChartData

variable (D : ChartData)

/-- The shifted predictor `L' = L + γ`. -/
def L' : Fin 4 → ℝ := ![D.L 0 + D.γ, D.L 1, D.L 2, D.L 3]

/-- The normalized base point of an original base point. -/
def normBase (z : Fin 3 → ℝ) : Fin 3 → ℝ :=
  unitContactBase D.B (contactBaseFrame D.t₀ D.q D.Z₀ D.Y₀ z)

def normMat : Matrix (Fin 3) (Fin 3) ℝ :=
  unitContactMatrix D.B * contactFrameMatrix D.t₀ D.q D.Z₀

def normOff : Fin 3 → ℝ :=
  (unitContactMatrix D.B).mulVec (contactFrameOffset D.t₀ D.q D.Z₀ D.Y₀) + ![0, 1 / 4, 1 / 2]

theorem normBase_eq_affine (z : Fin 3 → ℝ) :
    D.normBase z = Submission.Lib.K4AffineMeshCaps.affineBase D.normMat D.normOff z := by
  unfold normBase Submission.Lib.K4AffineMeshCaps.affineBase normMat normOff
  rw [unitContactBase_eq_affine, contactBaseFrame_eq_affine, Matrix.mulVec_add,
    Matrix.mulVec_mulVec]
  abel

theorem det_normMat : D.normMat.det = ((8 * D.B) ^ 2)⁻¹ * (D.q ^ 4)⁻¹ := by
  unfold normMat
  rw [Matrix.det_mul, det_unitContactMatrix, det_contactFrameMatrix]

/-- The normalized line of an original line. -/
def normLine (b : Fin 6 → ℝ) : Fin 6 → ℝ :=
  unitContactCoeff D.B (contactChartCoeff D.t₀ D.q D.Z₀ D.Y₀ (residualCoeff D.L' D.c b))

theorem normLine_lineP (hq : D.q ≠ 0) (hB : D.B ≠ 0) (b : Fin 6 → ℝ) (σ : ℝ) :
    Submission.Lib.K4QuadraticSheetCore.lineP (D.normLine b) σ =
      D.normBase (basePt b (D.t₀ + D.q * σ)) := by
  funext i
  fin_cases i <;>
    simp [Submission.Lib.K4QuadraticSheetCore.lineP, normLine, normBase, basePt,
      unitContactCoeff, unitContactBase, contactChartCoeff, contactBaseFrame, residualCoeff] <;>
    field_simp <;> ring

/-- The normalized hidden value is the scaled residual of the shifted predictor. -/
theorem normLine_lineW (hq : D.q ≠ 0) (b : Fin 6 → ℝ) (σ : ℝ) :
    Submission.Lib.K4QuadraticSheetCore.lineW (D.normLine b) σ =
      (point b (D.t₀ + D.q * σ) 3 - eval (point b (D.t₀ + D.q * σ)) (affineBase D.L')) / D.c := by
  simp [Submission.Lib.K4QuadraticSheetCore.lineW, normLine, unitContactCoeff,
    contactChartCoeff, residualCoeff, point, affineBase, L']
  ring

theorem normLine_velocity (b : Fin 6 → ℝ) :
    D.normLine b 3 = b 3 / (8 * D.B) := by
  simp [normLine, unitContactCoeff, contactChartCoeff, residualCoeff]

theorem normLine_contact (b : Fin 6 → ℝ) :
    D.normLine b 4 + D.normLine b 0 = (b 4 + b 0) / D.q / (8 * D.B) := by
  have h1 := unitContactCoeff_defect D.B (contactChartCoeff D.t₀ D.q D.Z₀ D.Y₀
    (residualCoeff D.L' D.c b))
  have h2 := contactChart_contact_error D.t₀ D.q D.Z₀ D.Y₀ (residualCoeff D.L' D.c b)
  simp only [normLine]
  rw [h1, h2]
  simp [residualCoeff]

/-! ## The inverse base chart as a substitution -/

/-- Original coordinates as degree-one polynomials in normalized base coordinates and a hidden
variable scaled by `κh` and shifted by `γ`. -/
def chartSubst (κh : ℝ) : Fin 4 → MvPolynomial (Fin 4) ℝ :=
  ![C D.t₀ + C D.q * X 0,
    C D.Z₀ + C (8 * D.B * D.q) * (X 1 - C (1 / 4)),
    C D.Y₀ - C D.Z₀ * (C D.t₀ + C D.q * X 0) + C D.t₀ * (C D.Z₀ + C (8 * D.B * D.q) * (X 1 - C (1 / 4))) +
      C (8 * D.B * D.q ^ 2) * (X 2 - C (1 / 2) + C (1 / 4) * X 0),
    C κh * X 3 + C D.γ]

/-- The original shifted coordinates of an original line at time `t`, as in the frozen
statement: `(t, Z, Y, w - L(t, Z, Y))`. -/
def shiftedVec (b : Fin 6 → ℝ) (t : ℝ) : Fin 4 → ℝ :=
  ![t, b 0 + t * b 3, b 1 + t * b 4,
    b 2 + t * b 5 - (D.L 0 + D.L 1 * t + D.L 2 * (b 0 + t * b 3) + D.L 3 * (b 1 + t * b 4))]

/-- Evaluating the substitution at a normalized line point gives the original shifted point. -/
theorem eval_chartSubst_normLine (hq : D.q ≠ 0) (hB : D.B ≠ 0) (hc : D.c ≠ 0)
    (b : Fin 6 → ℝ) (σ : ℝ) :
    (fun i => eval (point (D.normLine b) σ) (D.chartSubst D.c i)) =
      D.shiftedVec b (D.t₀ + D.q * σ) := by
  funext i
  fin_cases i <;>
    simp [chartSubst, shiftedVec, point, normLine, unitContactCoeff, contactChartCoeff,
      residualCoeff, L'] <;>
    field_simp <;> ring

/-- With an unscaled hidden variable, the substitution at `(normBase z, u)` gives
`(z, u + γ)`. -/
theorem eval_chartSubst_one (hq : D.q ≠ 0) (hB : D.B ≠ 0) (z : Fin 3 → ℝ) (u : ℝ) :
    (fun i => eval ![D.normBase z 0, D.normBase z 1, D.normBase z 2, u] (D.chartSubst 1 i)) =
      ![z 0, z 1, z 2, u + D.γ] := by
  funext i
  fin_cases i <;>
    simp [chartSubst, normBase, unitContactBase, contactBaseFrame] <;>
    field_simp <;> ring

theorem chartSubst_degree (κh : ℝ) (i : Fin 4) : (D.chartSubst κh i).totalDegree ≤ 1 := by
  open Submission.Lib.K4ChartLifting in
  fin_cases i
  · exact deg1_add (deg1_C _) (deg1_C_mul _ (deg1_X _))
  · exact deg1_add (deg1_C _) (deg1_C_mul _ (deg1_sub (deg1_X _) (deg1_C _)))
  · exact deg1_add (deg1_add (deg1_sub (deg1_C _) (deg1_C_mul _ (deg1_add (deg1_C _)
      (deg1_C_mul _ (deg1_X _))))) (deg1_C_mul _ (deg1_add (deg1_C _)
        (deg1_C_mul _ (deg1_sub (deg1_X _) (deg1_C _))))))
      (deg1_C_mul _ (deg1_add (deg1_sub (deg1_X _) (deg1_C _)) (deg1_C_mul _ (deg1_X _))))
  · exact deg1_add (deg1_C_mul _ (deg1_X _)) (deg1_C _)

/-- Only the hidden coordinate of the substitution depends on the hidden variable. -/
theorem pderiv_chartSubst (κh : ℝ) (i : Fin 4) :
    pderiv (3 : Fin 4) (D.chartSubst κh i) = if i = 3 then C κh else 0 := by
  fin_cases i <;> simp [chartSubst, pderiv_X]

/-- The normalized test with unscaled hidden residual. -/
def tildeTest (G : MvPolynomial (Fin 4) ℝ) : MvPolynomial (Fin 4) ℝ :=
  bind₁ (D.chartSubst 1) G

/-- The normalized test with hidden residual scaled by the fine width. -/
def hatTest (G : MvPolynomial (Fin 4) ℝ) : MvPolynomial (Fin 4) ℝ :=
  C D.c⁻¹ * bind₁ (D.chartSubst D.c) G

theorem tildeTest_degree (G : MvPolynomial (Fin 4) ℝ) :
    (D.tildeTest G).totalDegree ≤ G.totalDegree :=
  Submission.Lib.K4ChartLifting.totalDegree_bind₁_le_of_le_one _ (D.chartSubst_degree 1) G

theorem hatTest_degree (G : MvPolynomial (Fin 4) ℝ) :
    (D.hatTest G).totalDegree ≤ G.totalDegree := by
  unfold hatTest
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  exact Submission.Lib.K4ChartLifting.totalDegree_bind₁_le_of_le_one _
    (D.chartSubst_degree D.c) G

theorem pderiv_bind₁_chartSubst (κh : ℝ) (G : MvPolynomial (Fin 4) ℝ) :
    pderiv (3 : Fin 4) (bind₁ (D.chartSubst κh) G) =
      C κh * bind₁ (D.chartSubst κh) (pderiv 3 G) := by
  rw [Submission.Lib.K4ChartLifting.pderiv_bind₁, Finset.sum_eq_single (3 : Fin 4)]
  · rw [pderiv_chartSubst, if_pos rfl, mul_comm]
  · intro i _ hi
    rw [pderiv_chartSubst, if_neg hi, mul_zero]
  · simp

theorem pderiv_hatTest (hc : D.c ≠ 0) (G : MvPolynomial (Fin 4) ℝ) :
    pderiv (3 : Fin 4) (D.hatTest G) = bind₁ (D.chartSubst D.c) (pderiv 3 G) := by
  unfold hatTest
  rw [Derivation.leibniz, pderiv_C, smul_zero, add_zero, pderiv_bind₁_chartSubst, smul_eq_mul,
    ← mul_assoc, ← C_mul, inv_mul_cancel₀ hc, C_1, one_mul]

theorem pderiv_pderiv_hatTest (hc : D.c ≠ 0) (G : MvPolynomial (Fin 4) ℝ) :
    pderiv (3 : Fin 4) (pderiv 3 (D.hatTest G)) =
      C D.c * bind₁ (D.chartSubst D.c) (pderiv 3 (pderiv 3 G)) := by
  rw [pderiv_hatTest D hc, pderiv_bind₁_chartSubst]

theorem pderiv_tildeTest (G : MvPolynomial (Fin 4) ℝ) :
    pderiv (3 : Fin 4) (D.tildeTest G) = D.tildeTest (pderiv 3 G) := by
  unfold tildeTest
  rw [pderiv_bind₁_chartSubst, C_1, one_mul]

/-- The scaled normalized test along a normalized line is the shifted test divided by `c`. -/
theorem eval_hatTest_normLine (hq : D.q ≠ 0) (hB : D.B ≠ 0) (hc : D.c ≠ 0)
    (G : MvPolynomial (Fin 4) ℝ) (b : Fin 6 → ℝ) (σ : ℝ) :
    eval (point (D.normLine b) σ) (D.hatTest G) =
      D.c⁻¹ * eval (D.shiftedVec b (D.t₀ + D.q * σ)) G := by
  rw [hatTest, eval_mul, eval_C, Submission.Lib.K4ChartLifting.eval_bind₁',
    D.eval_chartSubst_normLine hq hB hc]

theorem eval_pderiv_hatTest_normLine (hq : D.q ≠ 0) (hB : D.B ≠ 0) (hc : D.c ≠ 0)
    (G : MvPolynomial (Fin 4) ℝ) (b : Fin 6 → ℝ) (σ : ℝ) :
    eval (point (D.normLine b) σ) (pderiv 3 (D.hatTest G)) =
      eval (D.shiftedVec b (D.t₀ + D.q * σ)) (pderiv 3 G) := by
  rw [pderiv_hatTest D hc, Submission.Lib.K4ChartLifting.eval_bind₁',
    D.eval_chartSubst_normLine hq hB hc]

theorem eval_pderiv_pderiv_hatTest_normLine (hq : D.q ≠ 0) (hB : D.B ≠ 0) (hc : D.c ≠ 0)
    (G : MvPolynomial (Fin 4) ℝ) (b : Fin 6 → ℝ) (σ : ℝ) :
    eval (point (D.normLine b) σ) (pderiv 3 (pderiv 3 (D.hatTest G))) =
      D.c * eval (D.shiftedVec b (D.t₀ + D.q * σ)) (pderiv 3 (pderiv 3 G)) := by
  rw [pderiv_pderiv_hatTest D hc, eval_mul, eval_C, Submission.Lib.K4ChartLifting.eval_bind₁',
    D.eval_chartSubst_normLine hq hB hc]

/-- The unscaled normalized test at `(normBase z, u)` is the shifted test at `(z, u + γ)`. -/
theorem eval_tildeTest (hq : D.q ≠ 0) (hB : D.B ≠ 0) (G : MvPolynomial (Fin 4) ℝ)
    (z : Fin 3 → ℝ) (u : ℝ) :
    eval ![D.normBase z 0, D.normBase z 1, D.normBase z 2, u] (D.tildeTest G) =
      eval ![z 0, z 1, z 2, u + D.γ] G := by
  rw [tildeTest, Submission.Lib.K4ChartLifting.eval_bind₁', D.eval_chartSubst_one hq hB]

/-! ## Pulling an affine function of the normalized base back -/

/-- `L' + c · (a₀ + a · normBase z)` as an original affine predictor. -/
def pullAffine (a₀ : ℝ) (a : Fin 3 → ℝ) : Fin 4 → ℝ :=
  ![D.L' 0 + D.c * (a₀ + Submission.Lib.K4QuadraticSheetCore.dot3 a D.normOff),
    D.L' 1 + D.c * (D.normMat.transpose.mulVec a 0),
    D.L' 2 + D.c * (D.normMat.transpose.mulVec a 1),
    D.L' 3 + D.c * (D.normMat.transpose.mulVec a 2)]

theorem eval_pullAffine (a₀ : ℝ) (a : Fin 3 → ℝ) (x : Fin 4 → ℝ) :
    eval x (affineBase (D.pullAffine a₀ a)) =
      eval x (affineBase D.L') +
        D.c * Submission.Lib.K4QuadraticSheetCore.affineFn a₀ a (D.normBase ![x 0, x 1, x 2]) := by
  rw [normBase_eq_affine]
  simp [pullAffine, affineBase, Submission.Lib.K4QuadraticSheetCore.affineFn,
    Submission.Lib.K4QuadraticSheetCore.dot3, Submission.Lib.K4AffineMeshCaps.affineBase,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.transpose_apply, L']
  ring


/-! ## Coefficient budget of the substitution -/

section Budget

open Submission.Lib.K4ChartLifting

theorem coeffL1_lin (a b : ℝ) (j : Fin 4) :
    coeffL1 (C a + C b * X j : MvPolynomial (Fin 4) ℝ) ≤ |a| + |b| := by
  have h1 := coeffL1_add_le (C a : MvPolynomial (Fin 4) ℝ) (C b * X j)
  have h2 := coeffL1_C_mul_le b (X j : MvPolynomial (Fin 4) ℝ)
  rw [coeffL1_C] at h1
  rw [coeffL1_X, mul_one] at h2
  linarith

theorem coeffL1_shift (a : ℝ) (j : Fin 4) :
    coeffL1 (X j - C a : MvPolynomial (Fin 4) ℝ) ≤ 1 + |a| := by
  have h := coeffL1_sub_le (X j : MvPolynomial (Fin 4) ℝ) (C a)
  rwa [coeffL1_X, coeffL1_C] at h

theorem coeffL1_cs1 (Z₀ e : ℝ) :
    coeffL1 (C Z₀ + C e * (X 1 - C (1 / 4)) : MvPolynomial (Fin 4) ℝ) ≤ |Z₀| + |e| * (5 / 4) := by
  have h1 := coeffL1_add_le (C Z₀ : MvPolynomial (Fin 4) ℝ) (C e * (X 1 - C (1 / 4)))
  have h2 := coeffL1_C_mul_le e (X 1 - C (1 / 4) : MvPolynomial (Fin 4) ℝ)
  have h3 := coeffL1_shift (1 / 4) 1
  rw [coeffL1_C] at h1
  have h4 : |e| * coeffL1 (X 1 - C (1 / 4) : MvPolynomial (Fin 4) ℝ) ≤ |e| * (5 / 4) := by
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg e)
    norm_num at h3 ⊢
    linarith
  linarith

theorem coeffL1_cs2tail (e : ℝ) :
    coeffL1 (C e * (X 2 - C (1 / 2) + C (1 / 4) * X 0) : MvPolynomial (Fin 4) ℝ) ≤
      |e| * (7 / 4) := by
  have h1 := coeffL1_C_mul_le e (X 2 - C (1 / 2) + C (1 / 4) * X 0 : MvPolynomial (Fin 4) ℝ)
  have h2 := coeffL1_add_le (X 2 - C (1 / 2) : MvPolynomial (Fin 4) ℝ) (C (1 / 4) * X 0)
  have h3 := coeffL1_shift (1 / 2) 2
  have h4 := coeffL1_C_mul_le (1 / 4) (X 0 : MvPolynomial (Fin 4) ℝ)
  rw [coeffL1_X, mul_one] at h4
  have h5 : coeffL1 (X 2 - C (1 / 2) + C (1 / 4) * X 0 : MvPolynomial (Fin 4) ℝ) ≤ 7 / 4 := by
    norm_num at h3 h4 ⊢
    linarith
  exact h1.trans (mul_le_mul_of_nonneg_left h5 (abs_nonneg e))

theorem coeffL1_cs2 (Y₀ Z₀ t₀ q e e' : ℝ) :
    coeffL1 (C Y₀ - C Z₀ * (C t₀ + C q * X 0) + C t₀ * (C Z₀ + C e * (X 1 - C (1 / 4))) +
      C e' * (X 2 - C (1 / 2) + C (1 / 4) * X 0) : MvPolynomial (Fin 4) ℝ) ≤
      |Y₀| + |Z₀| * (|t₀| + |q|) + |t₀| * (|Z₀| + |e| * (5 / 4)) + |e'| * (7 / 4) := by
  have e1 := coeffL1_add_le (C Y₀ - C Z₀ * (C t₀ + C q * X 0) + C t₀ * (C Z₀ +
    C e * (X 1 - C (1 / 4))) : MvPolynomial (Fin 4) ℝ) (C e' * (X 2 - C (1 / 2) + C (1 / 4) * X 0))
  have e2 := coeffL1_add_le (C Y₀ - C Z₀ * (C t₀ + C q * X 0) : MvPolynomial (Fin 4) ℝ)
    (C t₀ * (C Z₀ + C e * (X 1 - C (1 / 4))))
  have e3 := coeffL1_sub_le (C Y₀ : MvPolynomial (Fin 4) ℝ) (C Z₀ * (C t₀ + C q * X 0))
  have e4 := coeffL1_C_mul_le Z₀ (C t₀ + C q * X 0 : MvPolynomial (Fin 4) ℝ)
  have e5 := coeffL1_C_mul_le t₀ (C Z₀ + C e * (X 1 - C (1 / 4)) : MvPolynomial (Fin 4) ℝ)
  have e6 := coeffL1_cs2tail e'
  have e7 := mul_le_mul_of_nonneg_left (coeffL1_lin t₀ q 0) (abs_nonneg Z₀)
  have e8 := mul_le_mul_of_nonneg_left (coeffL1_cs1 Z₀ e) (abs_nonneg t₀)
  rw [coeffL1_C] at e3
  linarith

theorem coeffL1_cs3 (κh γ : ℝ) :
    coeffL1 (C κh * X 3 + C γ : MvPolynomial (Fin 4) ℝ) ≤ |κh| + |γ| := by
  have h1 := coeffL1_add_le (C κh * X 3 : MvPolynomial (Fin 4) ℝ) (C γ)
  have h2 := coeffL1_C_mul_le κh (X 3 : MvPolynomial (Fin 4) ℝ)
  rw [coeffL1_X, mul_one] at h2
  rw [coeffL1_C] at h1
  linarith

end Budget

/-- A common budget for the coefficient norms of the substitution polynomials. -/
def substBudget (κh : ℝ) : ℝ :=
  1 + (|D.t₀| + |D.q|) + (|D.Z₀| + |8 * D.B * D.q| * (5 / 4)) +
    (|D.Y₀| + |D.Z₀| * (|D.t₀| + |D.q|) + |D.t₀| * (|D.Z₀| + |8 * D.B * D.q| * (5 / 4)) +
      |8 * D.B * D.q ^ 2| * (7 / 4)) + (|κh| + |D.γ|)

theorem substBudget_parts (κh : ℝ) :
    0 ≤ |D.t₀| + |D.q| ∧ 0 ≤ |D.Z₀| + |8 * D.B * D.q| * (5 / 4) ∧
    0 ≤ |D.Y₀| + |D.Z₀| * (|D.t₀| + |D.q|) + |D.t₀| * (|D.Z₀| + |8 * D.B * D.q| * (5 / 4)) +
      |8 * D.B * D.q ^ 2| * (7 / 4) ∧ 0 ≤ |κh| + |D.γ| := by
  refine ⟨by positivity, by positivity, by positivity, by positivity⟩

theorem one_le_substBudget (κh : ℝ) : 1 ≤ D.substBudget κh := by
  obtain ⟨h0, h1, h2, h3⟩ := D.substBudget_parts κh
  unfold substBudget
  linarith

theorem coeffL1_chartSubst_le (κh : ℝ) (i : Fin 4) :
    Submission.Lib.K4ChartLifting.coeffL1 (D.chartSubst κh i) ≤ D.substBudget κh := by
  obtain ⟨h0, h1, h2, h3⟩ := D.substBudget_parts κh
  fin_cases i
  · have := coeffL1_lin D.t₀ D.q 0
    change Submission.Lib.K4ChartLifting.coeffL1
      (C D.t₀ + C D.q * X 0 : MvPolynomial (Fin 4) ℝ) ≤ _
    unfold substBudget
    linarith
  · have := coeffL1_cs1 D.Z₀ (8 * D.B * D.q)
    change Submission.Lib.K4ChartLifting.coeffL1
      (C D.Z₀ + C (8 * D.B * D.q) * (X 1 - C (1 / 4)) : MvPolynomial (Fin 4) ℝ) ≤ _
    unfold substBudget
    linarith
  · have := coeffL1_cs2 D.Y₀ D.Z₀ D.t₀ D.q (8 * D.B * D.q) (8 * D.B * D.q ^ 2)
    change Submission.Lib.K4ChartLifting.coeffL1
      (C D.Y₀ - C D.Z₀ * (C D.t₀ + C D.q * X 0) + C D.t₀ * (C D.Z₀ +
        C (8 * D.B * D.q) * (X 1 - C (1 / 4))) + C (8 * D.B * D.q ^ 2) *
          (X 2 - C (1 / 2) + C (1 / 4) * X 0) : MvPolynomial (Fin 4) ℝ) ≤ _
    unfold substBudget
    linarith
  · have := coeffL1_cs3 κh D.γ
    change Submission.Lib.K4ChartLifting.coeffL1
      (C κh * X 3 + C D.γ : MvPolynomial (Fin 4) ℝ) ≤ _
    unfold substBudget
    linarith

theorem coeffL1_tildeTest_le (G : MvPolynomial (Fin 4) ℝ) (hG : G.totalDegree ≤ 2) :
    Submission.Lib.K4ChartLifting.coeffL1 (D.tildeTest G) ≤
      Submission.Lib.K4ChartLifting.coeffL1 G * D.substBudget 1 ^ 2 := by
  have h := Submission.Lib.K4ChartLifting.coeffL1_bind₁_le (D.chartSubst 1) (D.substBudget 1)
    (D.one_le_substBudget 1) (D.coeffL1_chartSubst_le 1) G
  refine h.trans ?_
  apply mul_le_mul_of_nonneg_left _ (Submission.Lib.K4ChartLifting.coeffL1_nonneg G)
  exact pow_le_pow_right₀ (D.one_le_substBudget 1) hG

end ChartData

end

end Submission.Obl.k4_contact_regular_quadratic_reconstruction.AffinePrep
