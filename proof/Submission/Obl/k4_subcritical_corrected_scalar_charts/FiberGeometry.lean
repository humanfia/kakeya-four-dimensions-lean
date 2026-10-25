/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/FiberGeometry.lean`. Original attributions are retained below. -/
import Submission.Lib.K4FullTimeLayers.Geometry

/-! Parameter-fiber algebra for Proposition 9.6. The definitions and exact fiber
identity adapt this LOT tree's o202/x0698, file
`Submission/Obl/k4_horizontal_subcritical_rate_candidates/FiberCollapse.lean`
(commit aacc14fa). The directional comparison estimates below are new here. -/

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set

/-- The six-coefficient predictor in the endpoint engine. -/
abbrev parameterPredictor := Submission.Lib.K4FullTimeLayers.parameterPredictor

/-- The scalar coordinate transverse to `(1,2t)`. -/
def fiberCoordinate (t p q : ℝ) : ℝ := q - 2 * t * p

/-- The derivative of a parameter-affine predictor along `(1,2t)`. -/
def fiberDerivative (h : Fin 6 → ℝ) (t : ℝ) : ℝ :=
  h 2 + (h 3 + 2 * h 4) * t + 2 * h 5 * t ^ 2

/-- A quadratic time signal has a primitive within the endpoint predictor class. -/
noncomputable def fiberCorrection (β : Fin 3 → ℝ) : Fin 6 → ℝ :=
  ![0, 0, β 0, β 1, 0, β 2 / 2]

theorem fiberDerivative_correction (β : Fin 3 → ℝ) (t : ℝ) :
    fiberDerivative (fiberCorrection β) t = β 0 + β 1 * t + β 2 * t ^ 2 := by
  dsimp [fiberDerivative, fiberCorrection]
  ring

theorem parameterPredictor_sub (h h' : Fin 6 → ℝ) (t p q : ℝ) :
    parameterPredictor (h - h') t p q =
      parameterPredictor h t p q - parameterPredictor h' t p q := by
  simp only [parameterPredictor, Submission.Lib.K4FullTimeLayers.parameterPredictor, Pi.sub_apply]
  ring

theorem fiberDerivative_sub (h h' : Fin 6 → ℝ) (t : ℝ) :
    fiberDerivative (h - h') t = fiberDerivative h t - fiberDerivative h' t := by
  simp only [fiberDerivative, Pi.sub_apply]
  ring

theorem parameterPredictor_fiber_identity (h : Fin 6 → ℝ) (t p q : ℝ) :
    parameterPredictor h t p q - parameterPredictor h t 0 (fiberCoordinate t p q) =
      p * fiberDerivative h t := by
  unfold parameterPredictor Submission.Lib.K4FullTimeLayers.parameterPredictor fiberCoordinate fiberDerivative
  ring

/-- A small directional derivative permits evaluation on the scalar section `p=0`. -/
theorem parameterPredictor_fiber_bound {h : Fin 6 → ℝ} {t p q K E : ℝ}
    (hp : |p| ≤ K) (hd : |fiberDerivative h t| ≤ E) :
    |parameterPredictor h t p q - parameterPredictor h t 0 (fiberCoordinate t p q)| ≤
      K * E := by
  rw [parameterPredictor_fiber_identity, abs_mul]
  exact mul_le_mul hp hd (abs_nonneg _) ((abs_nonneg _).trans hp)

/-- Subtraction of the fitted time correction gives the required scalar-section error. -/
theorem corrected_parameter_fiber_bound {h : Fin 6 → ℝ} {β : Fin 3 → ℝ}
    {t p q K E : ℝ} (hp : |p| ≤ K)
    (hd : |fiberDerivative h t - (β 0 + β 1 * t + β 2 * t ^ 2)| ≤ E) :
    |parameterPredictor (h - fiberCorrection β) t p q -
      parameterPredictor (h - fiberCorrection β) t 0 (fiberCoordinate t p q)| ≤ K * E := by
  apply parameterPredictor_fiber_bound hp
  simpa only [fiberDerivative_sub, fiberDerivative_correction] using hd

/-- True affine coefficients in the static horizontal parameters with velocity `v`. -/
abbrev horizontalLift := Submission.Lib.K4FullTimeLayers.liftAffine

theorem horizontalLift_eval (L : Fin 4 → ℝ) (v t p q : ℝ) :
    parameterPredictor (horizontalLift L v) t p q =
      L 0 + L 1 * t + L 2 * (p + t * v) + L 3 * (q - t * p) := by
  exact Submission.Lib.K4FullTimeLayers.liftAffine_eval L v t p q

theorem horizontalLift_fiberDerivative (L : Fin 4 → ℝ) (v t : ℝ) :
    fiberDerivative (horizontalLift L v) t = L 2 + t * L 3 := by
  simp [fiberDerivative, horizontalLift, Submission.Lib.K4FullTimeLayers.liftAffine]
  ring

/-- The correction has no larger coefficient bound than its quadratic time signal. -/
theorem fiberCorrection_coeff_bound {β : Fin 3 → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hβ : ∀ i, |β i| ≤ K) (i : Fin 6) :
    |fiberCorrection β i| ≤ K := by
  fin_cases i <;> simp [fiberCorrection, abs_div] <;>
    linarith [hβ 0, hβ 1, hβ 2]

/-- Three values in a tilted box control the horizontal derivative at a nearby time.
The horizontal and transverse increments have the true-box scales `h` and `h²`. -/
theorem horizontal_slope_of_three_values {a b c z y m t h E L : ℝ}
    (hh : 0 < h) (hL : 0 ≤ L) (ht : |t - m| ≤ L * h)
    (h0 : |a + b * z + c * y| ≤ E)
    (h1 : |a + b * (z + h) + c * (y + m * h)| ≤ E)
    (h2 : |a + b * z + c * (y + h ^ 2)| ≤ E) :
    |b + t * c| ≤ 2 * (1 + L) * E / h := by
  have hE : 0 ≤ E := (abs_nonneg _).trans h0
  have hh2 : 0 < h ^ 2 := sq_pos_of_pos hh
  have hc : |c| * h ^ 2 ≤ 2 * E := by
    calc
      _ = |c * h ^ 2| := by rw [abs_mul, abs_of_pos hh2]
      _ = |(a + b * z + c * (y + h ^ 2)) - (a + b * z + c * y)| := by
        congr 1
        ring
      _ ≤ |a + b * z + c * (y + h ^ 2)| + |a + b * z + c * y| := abs_sub _ _
      _ ≤ 2 * E := by linarith
  have hb : |b + m * c| * h ≤ 2 * E := by
    calc
      _ = |(b + m * c) * h| := by rw [abs_mul, abs_of_pos hh]
      _ = |(a + b * (z + h) + c * (y + m * h)) -
          (a + b * z + c * y)| := by
        congr 1
        ring
      _ ≤ |a + b * (z + h) + c * (y + m * h)| + |a + b * z + c * y| := abs_sub _ _
      _ ≤ 2 * E := by linarith
  have htri : |b + t * c| ≤ |b + m * c| + |t - m| * |c| := by
    calc
      _ = |(b + m * c) + (t - m) * c| := by congr 1; ring
      _ ≤ _ := by simpa only [abs_mul] using abs_add_le (b + m * c) ((t - m) * c)
  apply (le_div_iff₀ hh).2
  have hmul := mul_le_mul_of_nonneg_right htri hh.le
  have hinc : |t - m| * |c| * h ≤ 2 * L * E := by
    calc
      _ ≤ (L * h) * |c| * h := by gcongr
      _ = L * (|c| * h ^ 2) := by ring
      _ ≤ L * (2 * E) := mul_le_mul_of_nonneg_left hc hL
      _ = _ := by ring
  nlinarith

/-- Passing a directional estimate from a coarse affine fit to a finer one costs
only the horizontal derivative of their difference, multiplied by the chart scale. -/
theorem corrected_directional_comparison {Li L0 : Fin 4 → ℝ} {H0 : Fin 6 → ℝ}
    {β : Fin 3 → ℝ} {v t D A E δ : ℝ}
    (hDA : 0 ≤ D / A)
    (hdiff : |(Li 2 + t * Li 3) - (L0 2 + t * L0 3)| ≤ E)
    (hsignal : |D / A * (L0 2 + t * L0 3 - fiberDerivative H0 t) -
      (β 0 + β 1 * t + β 2 * t ^ 2)| ≤ δ) :
    |D / A * (fiberDerivative (horizontalLift Li v) t - fiberDerivative H0 t) -
      (β 0 + β 1 * t + β 2 * t ^ 2)| ≤ D / A * E + δ := by
  rw [horizontalLift_fiberDerivative]
  calc
    _ = |D / A * ((Li 2 + t * Li 3) - (L0 2 + t * L0 3)) +
        (D / A * (L0 2 + t * L0 3 - fiberDerivative H0 t) -
          (β 0 + β 1 * t + β 2 * t ^ 2))| := by congr 1; ring
    _ ≤ |D / A * ((Li 2 + t * Li 3) - (L0 2 + t * L0 3))| +
        |D / A * (L0 2 + t * L0 3 - fiberDerivative H0 t) -
          (β 0 + β 1 * t + β 2 * t ^ 2)| := abs_add_le _ _
    _ ≤ D / A * E + δ := by
      rw [abs_mul, abs_of_nonneg hDA]
      exact add_le_add (mul_le_mul_of_nonneg_left hdiff hDA) hsignal

end Submission.Obl.k4_subcritical_corrected_scalar_charts
