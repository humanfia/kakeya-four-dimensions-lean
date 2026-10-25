/-
Adapted from: here:o204
Original o204 sources and file-level provenance are recorded below.
-/
/- Original provenance: here:o204, session x0706, CoreBasePolynomials.lean, commitd013eb32. -/
import Submission.Lib.K4OriginalGeometricReference.BasePotentialPullback
import Submission.Lib.K4ChartLifting.NormDensityFormula

/-!
Actual affine polynomial coordinates from a fine comparison core back to
the original physical base. These transport a fixed potential at unchanged
degree, without any estimate of its coefficient height or derivatives.
-/

namespace Submission.Lib.K4OriginalGeometricReference.Analytic

open MvPolynomial
open Submission.Lib.K4ChartLifting

noncomputable section

abbrev Base := EuclideanSpace ℝ (Fin 3)

/-- The SAME affine native unit-base convention, with time unscaled. -/
def coreUnitBase (κ : ℝ) (z : Base) : Base :=
  WithLp.toLp 2 ![z 0, (z 1 + κ) / (2 * κ), (z 2 + κ) / (2 * κ)]

def coreBaseShift (F : Frame) (κ : ℝ) (center : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![F.t₀ + F.q * center 0,
    F.c 0 + (F.t₀ + F.q * center 0) * F.u 0 +
      F.D 0 0 * (2 * κ * center 1 - κ) + F.D 0 1 * (2 * κ * center 2 - κ),
    F.c 1 + (F.t₀ + F.q * center 0) * F.u 1 +
      F.D 1 0 * (2 * κ * center 1 - κ) + F.D 1 1 * (2 * κ * center 2 - κ)]

def coreBaseMatrix (F : Frame) (κ scale : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![F.q * scale, 0, 0],
    ![F.q * scale * F.u 0, 2 * κ * scale * F.D 0 0, 2 * κ * scale * F.D 0 1],
    ![F.q * scale * F.u 1, 2 * κ * scale * F.D 1 0, 2 * κ * scale * F.D 1 1]]

def coreBaseCoordinates (F : Frame) (κ : ℝ) (center : Fin 3 → ℝ) (scale : ℝ) :
    Fin 3 → MvPolynomial (Fin 3) ℝ :=
  affineBaseCoordinates (coreBaseShift F κ center) (coreBaseMatrix F κ scale)

theorem coreBaseCoordinates_degree (F : Frame) (κ : ℝ)
    (center : Fin 3 → ℝ) (scale : ℝ) (i : Fin 3) :
    (coreBaseCoordinates F κ center scale i).totalDegree ≤ 1 :=
  affineBaseCoordinates_degree _ _ _

/-- The coordinate polynomials evaluate to the explicit inverse original
observation map, with the SAME core center and scale. -/
theorem coreBaseCoordinates_eval (F : Frame) (κ : ℝ)
    (center : Fin 3 → ℝ) (scale : ℝ) (z : Base) (i : Fin 3) :
    eval (fun j => z j) (coreBaseCoordinates F κ center scale i) =
      (F.obsBaseInv (WithLp.toLp 2 ![center 0 + scale * z 0,
        2 * κ * (center 1 + scale * z 1) - κ,
        2 * κ * (center 2 + scale * z 2) - κ])) i := by
  rw [coreBaseCoordinates, affineBaseCoordinates_eval]
  fin_cases i <;>
    simp [coreBaseShift, coreBaseMatrix, Frame.obsBaseInv, Fin.sum_univ_three] <;> ring

/-- An ACTUAL original base point reconstructed by the native core gives
exact physical polynomial coordinates. The hypotheses are the original
frame inverses and the core identity; no polynomial size test is used. -/
theorem coreBaseCoordinates_original (F : Frame) (hq : F.q ≠ 0)
    (hD : IsUnit F.D.det) {κ : ℝ} (hκ : κ ≠ 0)
    (center : Fin 3 → ℝ) (scale : ℝ) (z original : Base)
    (hcore : coreUnitBase κ (F.obsBase original) =
      WithLp.toLp 2 (fun j => center j + scale * z j)) :
    ∀ i, eval (fun j => z j) (coreBaseCoordinates F κ center scale i) = original i := by
  let normalized : Base := WithLp.toLp 2 ![center 0 + scale * z 0,
    2 * κ * (center 1 + scale * z 1) - κ,
    2 * κ * (center 2 + scale * z 2) - κ]
  have hn : F.obsBase original = normalized := by
    have h₀ := congrArg (fun v : Base => v 0) hcore
    have h₁ := congrArg (fun v : Base => v 1) hcore
    have h₂ := congrArg (fun v : Base => v 2) hcore
    simp [coreUnitBase] at h₀ h₁ h₂
    ext i
    fin_cases i
    · exact h₀
    · change (F.obsBase original) 1 = 2 * κ * (center 1 + scale * z 1) - κ
      have hh := (div_eq_iff (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hκ)).mp h₁
      linarith
    · change (F.obsBase original) 2 = 2 * κ * (center 2 + scale * z 2) - κ
      have hh := (div_eq_iff (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hκ)).mp h₂
      linarith
  have hinv := F.obsBaseInv_obsBase hq hD original
  rw [hn] at hinv
  intro i
  rw [coreBaseCoordinates_eval]
  exact congrArg (fun v : Base => v i) hinv

def coreBasePotential (F : Frame) (κ : ℝ) (center : Fin 3 → ℝ) (scale signalScale : ℝ)
    (P : MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 3) ℝ :=
  basePotentialPullback (coreBaseCoordinates F κ center scale) signalScale P

theorem coreBasePotential_degree (F : Frame) (κ : ℝ) (center : Fin 3 → ℝ)
    (scale signalScale : ℝ) (P : MvPolynomial (Fin 3) ℝ) :
    (coreBasePotential F κ center scale signalScale P).totalDegree ≤ P.totalDegree :=
  basePotentialPullback_degree _ (coreBaseCoordinates_degree F κ center scale) _ _

/-- The fixed old potential is evaluated at the SAME original physical
base, in the requested original signal unit. -/
theorem coreBasePotential_original_eval (F : Frame) (hq : F.q ≠ 0)
    (hD : IsUnit F.D.det) {κ : ℝ} (hκ : κ ≠ 0)
    (center : Fin 3 → ℝ) (scale signalScale : ℝ) (P : MvPolynomial (Fin 3) ℝ)
    (z original : Base)
    (hcore : coreUnitBase κ (F.obsBase original) =
      WithLp.toLp 2 (fun j => center j + scale * z j)) :
    eval (fun j => z j) (coreBasePotential F κ center scale signalScale P) =
      signalScale * eval (fun j => original j) P := by
  rw [coreBasePotential, basePotentialPullback_eval]
  have hh := coreBaseCoordinates_original F hq hD hκ center scale z original hcore
  rw [funext hh]

end

end Submission.Lib.K4OriginalGeometricReference.Analytic
