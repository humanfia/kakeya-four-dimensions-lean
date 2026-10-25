/-
Adapted from: here:o204
Original o204 sources and file-level provenance are recorded below.
-/
/- Original provenance: here:o204, session x0706, BasePotentialPullback.lean, commit2156fa88. -/
import Mathlib
import Submission.Lib.K4ChartLifting.PolyAlgebra

/-!
Pull a fixed old base potential into a fine comparison core without any
coefficient or derivative envelope. Affine coordinates preserve its degree,
and the original whole-row own-intercept error transfers exactly.
-/

namespace Submission.Lib.K4OriginalGeometricReference.Analytic

open MvPolynomial

noncomputable section

def affineBaseCoordinates (c : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ)
    (i : Fin 3) : MvPolynomial (Fin 3) ℝ :=
  C (c i) + ∑ j, C (M i j) * X j

/-- The actual affine coordinate polynomials have degree at most one. -/
theorem affineBaseCoordinates_degree (c : Fin 3 → ℝ)
    (M : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) :
    (affineBaseCoordinates c M i).totalDegree ≤ 1 := by
  apply (totalDegree_add _ _).trans
  exact max_le (by simp) (totalDegree_finsetSum_le fun j _ =>
    (totalDegree_mul _ _).trans (by simp))

theorem affineBaseCoordinates_eval (c : Fin 3 → ℝ)
    (M : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) (z : Fin 3 → ℝ) :
    eval z (affineBaseCoordinates c M i) = c i + ∑ j, M i j * z j := by
  simp [affineBaseCoordinates]

def basePotentialPullback (coords : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (signalScale : ℝ) (P : MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 3) ℝ :=
  C signalScale * bind₁ coords P

/-- The potential degree is unchanged by the fine affine base change
and the fixed original signal-unit conversion. -/
theorem basePotentialPullback_degree
    (coords : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hcoords : ∀ i, (coords i).totalDegree ≤ 1)
    (signalScale : ℝ) (P : MvPolynomial (Fin 3) ℝ) :
    (basePotentialPullback coords signalScale P).totalDegree ≤ P.totalDegree := by
  apply (totalDegree_mul _ _).trans
  simpa only [totalDegree_C, zero_add] using
    Submission.Lib.K4ChartLifting.totalDegree_bind₁_le_of_le_one coords hcoords P

/-- Evaluation keeps the SAME original base value, with no estimate of
its absolute height. -/
theorem basePotentialPullback_eval (coords : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (signalScale : ℝ) (P : MvPolynomial (Fin 3) ℝ) (z : Fin 3 → ℝ) :
    eval z (basePotentialPullback coords signalScale P) =
      signalScale * eval (fun i => eval z (coords i)) P := by
  simp only [basePotentialPullback, map_mul, eval_C]
  congr 1
  change eval₂Hom (RingHom.id ℝ) z (bind₁ coords P) = _
  rw [eval₂Hom_bind₁]
  rfl

/-- A pointwise original own-intercept fit transfers to the actual fine
prediction with exactly the root-comparison error plus the old error in
fine signal units. No potential derivative bound is introduced. -/
theorem basePotentialPullback_own_intercept_fit
    {Ω : Type*} (coords : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (localBase originalBase : Ω → Fin 3 → ℝ)
    (oldSignal prediction intercept : Ω → ℝ) (P : MvPolynomial (Fin 3) ℝ)
    {signalUnit rootError oldError : ℝ} (hunit : 0 < signalUnit)
    (hbase : ∀ p i, eval (localBase p) (coords i) = originalBase p i)
    (hprediction : ∀ p, |prediction p - oldSignal p / signalUnit| ≤ rootError)
    (hfit : ∀ p, |oldSignal p - eval (originalBase p) P - intercept p| ≤ oldError) :
    ∀ p, |prediction p - eval (localBase p) (basePotentialPullback coords signalUnit⁻¹ P) -
      intercept p / signalUnit| ≤ rootError + oldError / signalUnit := by
  intro p
  have hcoords : (fun i => eval (localBase p) (coords i)) = originalBase p := funext (hbase p)
  rw [basePotentialPullback_eval, hcoords]
  have heq : prediction p - signalUnit⁻¹ * eval (originalBase p) P - intercept p / signalUnit =
      (prediction p - oldSignal p / signalUnit) +
        (oldSignal p - eval (originalBase p) P - intercept p) / signalUnit := by ring
  rw [heq]
  apply (abs_add_le _ _).trans
  apply add_le_add (hprediction p)
  rw [abs_div, abs_of_pos hunit]
  exact div_le_div_of_nonneg_right (hfit p) hunit.le

end

end Submission.Lib.K4OriginalGeometricReference.Analytic
