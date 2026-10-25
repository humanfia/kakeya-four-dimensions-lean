/- Adapted from this LOT tree, obligation o212, session x0762, commit ecff5a0a89fd,
   Submission/Obl/k4_critical_intercept_concentration/Inherited/AffinePrimitive.lean.
   Existing source attributions below are preserved. -/
/- Adapted from this LOT tree, obligation o201, session x0697, commit 74bd9a876bac,
   Submission/Obl/k4_horizontal_critical_rate_candidates/Inherited/AffinePrimitive.lean.
   Original source attributions below are preserved. -/
-- Adapted from the same LOT tree, o107, session x0353, commit 2dadd64f9c576ee68d49917fce08111798f9ad02
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/AffinePrimitive.lean
-- Unaccepted helper shared on origin/x0353; namespace and local imports renamed.
import Submission.Obl.k4_critical_switching_state_preparation.Inherited.HeavyIntercept
import Submission.Lib.K4XInterface.Basic

/-! The affine primitive of a fitted skew row, and its whole-trajectory hidden test. -/

namespace Submission.Obl.k4_critical_switching_state_preparation.Inherited

noncomputable section

open MvPolynomial MeasureTheory Set

def primitiveCoefficients (B : Fin 2 → ℝ) (lam H t₀ Z₀ : ℝ) : Fin 4 → ℝ :=
  ![0, B 0 + lam * Z₀ / H, B 1 - lam * t₀ / H, lam / H]

def affineResidualIntercept (A : Fin 4 → ℝ) (b : Fin 6 → ℝ) : ℝ :=
  b 2 - A 0 - A 2 * b 0 - A 3 * b 1

def affineResidualSlope (A : Fin 4 → ℝ) (b : Fin 6 → ℝ) : ℝ :=
  b 5 - A 1 - A 2 * b 3 - A 3 * b 4

/-- The skew row-fit output has an affine primitive along native trajectories.
The remaining error is bounded by the row errors and the horizontal defect. -/
theorem row_fit_primitive_slope_bound
    (b : Fin 6 → ℝ) (T B : Fin 2 → ℝ) (lam H t₀ Z₀ t K L E F ε : ℝ)
    (hH : 0 < H) (hv : |b 3| ≤ K) (hlam : |lam| ≤ L)
    (hdefect : |b 4 + b 0| ≤ ε)
    (hlinear : |b 5 - T 0 - b 3 * T 1| ≤ E)
    (hrow0 : |T 0 - B 0 + lam * ((b 0 + t * b 3 - Z₀) / H)| ≤ F)
    (hrow1 : |T 1 - B 1 - lam * ((t - t₀) / H)| ≤ F) :
    |affineResidualSlope (primitiveCoefficients B lam H t₀ Z₀) b| ≤
      E + (1 + K) * F + L * ε / H := by
  have hK : 0 ≤ K := (abs_nonneg _).trans hv
  have hL : 0 ≤ L := (abs_nonneg _).trans hlam
  have hF : 0 ≤ F := (abs_nonneg _).trans hrow0
  have hε : 0 ≤ ε := (abs_nonneg _).trans hdefect
  have hm : |b 3 * (T 1 - B 1 - lam * ((t - t₀) / H))| ≤ K * F := by
    rw [abs_mul]
    exact mul_le_mul hv hrow1 (abs_nonneg _) hK
  have hd : |(lam / H) * (b 4 + b 0)| ≤ L * ε / H := by
    calc
      _ = (|lam| / H) * |b 4 + b 0| := by rw [abs_mul, abs_div, abs_of_pos hH]
      _ ≤ (L / H) * ε :=
        mul_le_mul (div_le_div_of_nonneg_right hlam hH.le) hdefect (abs_nonneg _)
          (div_nonneg hL hH.le)
      _ = _ := by ring
  have hsum : |(b 5 - T 0 - b 3 * T 1) +
      (T 0 - B 0 + lam * ((b 0 + t * b 3 - Z₀) / H)) +
      b 3 * (T 1 - B 1 - lam * ((t - t₀) / H))| ≤ E + F + K * F :=
    (abs_add_le _ _).trans
      (add_le_add ((abs_add_le _ _).trans (add_le_add hlinear hrow0)) hm)
  have heq : affineResidualSlope (primitiveCoefficients B lam H t₀ Z₀) b =
      ((b 5 - T 0 - b 3 * T 1) +
        (T 0 - B 0 + lam * ((b 0 + t * b 3 - Z₀) / H)) +
        b 3 * (T 1 - B 1 - lam * ((t - t₀) / H))) - (lam / H) * (b 4 + b 0) := by
    simp [affineResidualSlope, primitiveCoefficients]
    ring
  rw [heq]
  exact (abs_sub _ _).trans ((add_le_add hsum hd).trans_eq (by ring))

def affineHiddenTest (A : Fin 4 → ℝ) (offset : ℝ) : MvPolynomial (Fin 4) ℝ :=
  X 3 - C (A 0 + offset) - C (A 1) * X 0 - C (A 2) * X 1 - C (A 3) * X 2

theorem affineHiddenTest_totalDegree (A : Fin 4 → ℝ) (offset : ℝ) :
    (affineHiddenTest A offset).totalDegree ≤ 1 := by
  have hlin (a : ℝ) (i : Fin 4) : (C a * X i : MvPolynomial (Fin 4) ℝ).totalDegree ≤ 1 :=
    (totalDegree_mul _ _).trans (by simp)
  unfold affineHiddenTest
  refine (totalDegree_sub _ _).trans (max_le ?_ (hlin _ _))
  refine (totalDegree_sub _ _).trans (max_le ?_ (hlin _ _))
  refine (totalDegree_sub _ _).trans (max_le ?_ (hlin _ _))
  exact (totalDegree_sub _ _).trans (by
    simp only [totalDegree_X, totalDegree_C, max_zero]
    exact le_rfl)

theorem affineHiddenTest_hidden_derivative (A : Fin 4 → ℝ) (offset : ℝ) :
    pderiv (3 : Fin 4) (affineHiddenTest A offset) = 1 := by
  simp [affineHiddenTest, map_sub]

theorem affineHiddenTest_hidden_second (A : Fin 4 → ℝ) (offset : ℝ) :
    pderiv (3 : Fin 4) (pderiv (3 : Fin 4) (affineHiddenTest A offset)) = 0 := by
  rw [affineHiddenTest_hidden_derivative]
  simp

theorem affineHiddenTest_native_eval
    (A : Fin 4 → ℝ) (offset : ℝ) (b : Fin 6 → ℝ) (t : ℝ) :
    eval (Submission.Lib.K4XInterface.gx (0, b) t) (affineHiddenTest A offset) =
      affineResidualIntercept A b + t * affineResidualSlope A b - offset := by
  simp [affineHiddenTest, Submission.Lib.K4XInterface.gx,
    affineResidualIntercept, affineResidualSlope]
  ring

/-- A single small-slope condition and the exact midpoint bin give a hidden
test valid throughout the original selected block. -/
theorem affineHiddenTest_whole_block
    (A : Fin 4 → ℝ) (b : Fin 6 → ℝ) (a E L t₀ : ℝ) (j : ℤ)
    (ha : 0 < a) (hE : 0 ≤ E) (hL : 0 ≤ L) (hslope : |affineResidualSlope A b| ≤ E)
    (hbin : ⌊(affineResidualIntercept A b + (t₀ + L / 2) * affineResidualSlope A b) / a⌋ = j) :
    ∀ t ∈ Set.Icc t₀ (t₀ + L),
      |eval (Submission.Lib.K4XInterface.gx (0, b) t) (affineHiddenTest A (a * j))| ≤ E * L + a := by
  intro t ht
  rw [affineHiddenTest_native_eval]
  have h := binned_affine_whole_block_fit a E L t₀ (affineResidualIntercept A b)
    (affineResidualSlope A b) ha hE hL hslope t ht
  simpa only [hbin] using h

theorem measurable_affineResidualSlope
    {α : Type*} [MeasurableSpace α] (b : α → Fin 6 → ℝ) (hb : Measurable b) (A : Fin 4 → ℝ) :
    Measurable (fun l => affineResidualSlope A (b l)) := by
  unfold affineResidualSlope
  fun_prop

/-- The fitted trajectory family is defined by an explicit measurable slope
condition, so no projection of a measurable event set is needed. -/
theorem measurableSet_affineResidualSlope
    {α : Type*} [MeasurableSpace α] (b : α → Fin 6 → ℝ) (hb : Measurable b)
    (A : Fin 4 → ℝ) (E : ℝ) :
    MeasurableSet {l | |affineResidualSlope A (b l)| ≤ E} :=
  measurableSet_le (measurable_affineResidualSlope b hb A).abs measurable_const

end

end Submission.Obl.k4_critical_switching_state_preparation.Inherited
