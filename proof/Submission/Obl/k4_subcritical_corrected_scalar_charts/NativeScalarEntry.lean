/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/NativeScalarEntry.lean`. Original attributions are retained below. -/
/- Adapted from this LOT tree, o218, session x0760, commit 771cc68c5af90206a38343b7b1bbe9d5343eaf47,
   `Submission/Obl/k4_horizontal_endpoint_wide_return/NativeScalarEntry.lean`.
   Predictor, lift and correction names use our existing accepted-library interfaces. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.FiberGeometry
import Submission.Obl.k4_subcritical_corrected_scalar_charts.QuadraticVariation

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set
open Submission.Obl.k4_fixed_budget_quadratic_recovery

noncomputable section

def nativeFiberSignal (H : Fin 6 → ℝ) (L : Fin 4 → ℝ) (D A t : ℝ) : ℝ :=
  D / A * (L 2 + t * L 3 - fiberDerivative H t)

def correctedNativeEntry (h₀ : Fin 6 → ℝ) (c : Fin 3 → ℝ) (L : Fin 4 → ℝ)
    (D A p₀ q₀ v t p q : ℝ) : ℝ :=
  (parameterPredictor (horizontalLift L v) t (p₀ + D * p) (q₀ + D * q) -
    parameterPredictor h₀ t (p₀ + D * p) (q₀ + D * q)) / A -
      parameterPredictor (fiberCorrection c) t p q

def nativeScalarEntry (h₀ : Fin 6 → ℝ) (c : Fin 3 → ℝ) (L : Fin 4 → ℝ)
    (D A p₀ q₀ v t R : ℝ) : ℝ :=
  correctedNativeEntry h₀ c L D A p₀ q₀ v t 0 R

/-- Directional collapse lets the entire native entry be evaluated at (0,R).
No coefficient bound and no small value offset between native fields is needed. -/
theorem correctedNativeEntry_fiber_identity (h₀ : Fin 6 → ℝ) (c : Fin 3 → ℝ)
    (L : Fin 4 → ℝ) (D A p₀ q₀ v t p q : ℝ) :
    correctedNativeEntry h₀ c L D A p₀ q₀ v t p q -
      nativeScalarEntry h₀ c L D A p₀ q₀ v t (q - 2 * t * p) =
        p * (nativeFiberSignal h₀ L D A t - (c 0 + c 1 * t + c 2 * t ^ 2)) := by
  simp only [correctedNativeEntry, nativeScalarEntry, horizontalLift,
    parameterPredictor, Submission.Lib.K4FullTimeLayers.parameterPredictor,
    Submission.Lib.K4FullTimeLayers.liftAffine, fiberCorrection, nativeFiberSignal, fiberDerivative,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, div_eq_mul_inv]
  ring

/-- Actual fitted points inherit one scalar entry, with the original native fit
error and the directional collapse error accounted for separately. -/
theorem nativeScalarEntry_fit (h₀ : Fin 6 → ℝ) (c : Fin 3 → ℝ) (L : Fin 4 → ℝ)
    {D A p₀ q₀ v t p q X err η : ℝ} (hA : 0 < A)
    (hfit : |X - parameterPredictor (horizontalLift L v)
      t (p₀ + D * p) (q₀ + D * q)| ≤ err)
    (hcollapse : |nativeFiberSignal h₀ L D A t - (c 0 + c 1 * t + c 2 * t ^ 2)| ≤ η) :
    |(X - parameterPredictor h₀ t (p₀ + D * p) (q₀ + D * q)) / A -
        parameterPredictor (fiberCorrection c) t p q -
          nativeScalarEntry h₀ c L D A p₀ q₀ v t (q - 2 * t * p)| ≤
      err / A + |p| * η := by
  have hfirst : |(X - parameterPredictor h₀ t (p₀ + D * p) (q₀ + D * q)) / A -
      parameterPredictor (fiberCorrection c) t p q -
        correctedNativeEntry h₀ c L D A p₀ q₀ v t p q| ≤ err / A := by
    have hid : (X - parameterPredictor h₀ t (p₀ + D * p) (q₀ + D * q)) / A -
        parameterPredictor (fiberCorrection c) t p q -
          correctedNativeEntry h₀ c L D A p₀ q₀ v t p q =
      (X - parameterPredictor (horizontalLift L v) t (p₀ + D * p) (q₀ + D * q)) / A := by
        unfold correctedNativeEntry
        ring
    rw [hid, abs_div, abs_of_pos hA]
    exact div_le_div_of_nonneg_right hfit hA.le
  have hsecond : |correctedNativeEntry h₀ c L D A p₀ q₀ v t p q -
      nativeScalarEntry h₀ c L D A p₀ q₀ v t (q - 2 * t * p)| ≤ |p| * η := by
    rw [correctedNativeEntry_fiber_identity, abs_mul]
    exact mul_le_mul_of_nonneg_left hcollapse (abs_nonneg _)
  exact (abs_sub_le _ _ _).trans (add_le_add hfirst hsecond)

/-- The scalar entry is a quadratic on the normalized (t,R/4) box. -/
def nativeScalarEntryCoeff (h₀ : Fin 6 → ℝ) (c : Fin 3 → ℝ) (L : Fin 4 → ℝ)
    (D A p₀ q₀ v : ℝ) : Fin 6 → ℝ :=
  ![(L 0 + L 2 * p₀ + L 3 * q₀ - h₀ 0 - h₀ 2 * p₀ - h₀ 4 * q₀) / A,
    (L 1 + v * L 2 - p₀ * L 3 - h₀ 1 - h₀ 3 * p₀ - h₀ 5 * q₀) / A,
    4 * D * (L 3 - h₀ 4) / A, 0, -4 * D * h₀ 5 / A - 2 * c 2, 0]

theorem nativeScalarEntryCoeff_eval (h₀ : Fin 6 → ℝ) (c : Fin 3 → ℝ) (L : Fin 4 → ℝ)
    (D A p₀ q₀ v t z : ℝ) :
    quadraticValue (nativeScalarEntryCoeff h₀ c L D A p₀ q₀ v) t z =
      nativeScalarEntry h₀ c L D A p₀ q₀ v t (4 * z) := by
  simp only [nativeScalarEntryCoeff, quadraticValue, nativeScalarEntry, correctedNativeEntry,
    horizontalLift, Submission.Lib.K4FullTimeLayers.liftAffine, parameterPredictor,
    Submission.Lib.K4FullTimeLayers.parameterPredictor, fiberCorrection,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, div_eq_mul_inv]
  ring

/-- Whole-domain norms control variation of a native scalar entry independently
of any separately displayed raw coefficient exponent. -/
theorem nativeScalarEntry_lipschitz (h₀ : Fin 6 → ℝ) (c : Fin 3 → ℝ) (L : Fin 4 → ℝ)
    (D A p₀ q₀ v E : ℝ)
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ Icc (-1 : ℝ) 1,
      |nativeScalarEntry h₀ c L D A p₀ q₀ v t (4 * z)| ≤ E)
    {t t' R R' : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (ht' : t' ∈ Icc (0 : ℝ) 1)
    (hR : |R| ≤ 4) (hR' : |R'| ≤ 4) :
    |nativeScalarEntry h₀ c L D A p₀ q₀ v t R -
      nativeScalarEntry h₀ c L D A p₀ q₀ v t' R'| ≤
        32 * E * (|t - t'| + |R - R'|) := by
  have hE : 0 ≤ E := (abs_nonneg _).trans (hbox 0 (by norm_num) 0 (by norm_num))
  have hcoeff : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ Icc (-1 : ℝ) 1,
      |quadraticValue (nativeScalarEntryCoeff h₀ c L D A p₀ q₀ v) t z| ≤ E := by
    simpa only [nativeScalarEntryCoeff_eval] using hbox
  have hz : R / 4 ∈ Icc (-1 : ℝ) 1 := by
    obtain ⟨hl, hu⟩ := abs_le.mp hR
    constructor <;> linarith
  have hz' : R' / 4 ∈ Icc (-1 : ℝ) 1 := by
    obtain ⟨hl, hu⟩ := abs_le.mp hR'
    constructor <;> linarith
  have hscaled : |R / 4 - R' / 4| ≤ |R - R'| := by
    rw [← sub_div, abs_div]
    norm_num
    exact div_le_self (abs_nonneg _) (by norm_num)
  have hbound := quadratic_box_lipschitz hcoeff ht ht' hz hz'
  simp only [nativeScalarEntryCoeff_eval, mul_div_cancel₀ _ (by norm_num : (4 : ℝ) ≠ 0)] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hscaled)
    (mul_nonneg (by norm_num) hE))

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
