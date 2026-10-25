/-
Adapted from this LOT tree o203, session x0699, commit 4341160d,
Submission/Obl/k4_horizontal_supercritical_rate_candidates/Geometry.lean (namespace
Submission.Obl.k4_horizontal_supercritical_rate_candidates renamed to
Submission.Obl.k4_horizontal_supercritical_three_projections.Parent).
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
Parameter coordinates for the supercritical branch of the supplied paper's
Proposition `prop:offcritical-wide`.
-/

namespace Submission.Obl.k4_horizontal_supercritical_three_projections.Parent

open Set

noncomputable section

def trajectory (b : Fin 6 → ℝ) (t : ℝ) : Fin 4 → ℝ :=
  ![t, b 0 + t * b 3, b 1 + t * b 4, b 2 + t * b 5]

def affineValue (L : Fin 4 → ℝ) (t Z Y : ℝ) : ℝ :=
  L 0 + L 1 * t + L 2 * Z + L 3 * Y

def parameterValue (L : Fin 4 → ℝ) (pc qc v D t p r : ℝ) : ℝ :=
  affineValue L t (pc + D * p + t * v) (qc + D * r - t * (pc + D * p))

def scalarParameter (t p r : ℝ) : ℝ := r - 2 * t * p

/-- The parameter projection discards precisely the direction `(1, 2t)`. -/
theorem parameterValue_fiber_difference (L : Fin 4 → ℝ) (pc qc v D t p r : ℝ) :
    parameterValue L pc qc v D t p r -
      parameterValue L pc qc v D t 0 (scalarParameter t p r) =
    D * p * (L 2 + t * L 3) := by
  unfold parameterValue affineValue scalarParameter
  ring

/-- The horizontal slope estimate controls the error of the scalar projection. -/
theorem parameterValue_fiber_bound (L : Fin 4 → ℝ) (pc qc v D t p r K a q B : ℝ)
    (hD : 0 ≤ D) (_hK : 0 ≤ K) (hp : |p| ≤ B)
    (hslope : |L 2 + t * L 3| ≤ K * (1 + a / q)) :
    |parameterValue L pc qc v D t p r -
      parameterValue L pc qc v D t 0 (scalarParameter t p r)| ≤
    D * B * (K * (1 + a / q)) := by
  rw [parameterValue_fiber_difference, abs_mul, abs_mul, abs_of_nonneg hD]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hp hD) hslope
    (abs_nonneg _) (mul_nonneg hD (le_trans (abs_nonneg p) hp))

/-- In the supercritical regime the parameter width is smaller than the
scalar thickness, so the discarded direction costs at most that thickness. -/
theorem directional_collapse (L : Fin 4 → ℝ) (pc qc v D t p r K a q B : ℝ)
    (hD : 0 ≤ D) (hK : 0 ≤ K) (hDa : D ≤ a) (hq : 0 < q) (haq : a ≤ q)
    (hp : |p| ≤ B) (hslope : |L 2 + t * L 3| ≤ K * (1 + a / q)) :
    |parameterValue L pc qc v D t p r -
      parameterValue L pc qc v D t 0 (scalarParameter t p r)| ≤
    2 * K * B * a := by
  have hB : 0 ≤ B := (abs_nonneg _).trans hp
  have ha : 0 ≤ a := hD.trans hDa
  have hratio : a / q ≤ 1 := (div_le_one hq).mpr haq
  calc
    _ ≤ D * B * (K * (1 + a / q)) :=
      parameterValue_fiber_bound L pc qc v D t p r K a q B hD hK hp hslope
    _ ≤ a * B * (2 * K) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right hDa hB
      · nlinarith
      · exact mul_nonneg hK (by positivity)
      · exact mul_nonneg ha hB
    _ = _ := by ring

/-- Replacing the true motion by the contact motion has two explicit errors:
velocity rounding and the horizontal residual. -/
theorem affineValue_contact_error (L : Fin 4 → ℝ) (b : Fin 6 → ℝ) (v t : ℝ) :
    affineValue L t (b 0 + t * b 3) (b 1 + t * b 4) -
      affineValue L t (b 0 + t * v) (b 1 - t * b 0) =
    L 2 * t * (b 3 - v) + L 3 * t * (b 4 + b 0) := by
  unfold affineValue
  ring

theorem affineValue_contact_bound (L : Fin 4 → ℝ) (b : Fin 6 → ℝ)
    (v t χ e H : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (hv : |b 3 - v| ≤ χ) (he : |b 4 + b 0| ≤ e)
    (hL2 : |L 2| ≤ H) (hL3 : |L 3| ≤ H) :
    |affineValue L t (b 0 + t * b 3) (b 1 + t * b 4) -
      affineValue L t (b 0 + t * v) (b 1 - t * b 0)| ≤ H * (χ + e) := by
  have hH : 0 ≤ H := (abs_nonneg _).trans hL2
  have hχ : 0 ≤ χ := (abs_nonneg _).trans hv
  have he0 : 0 ≤ e := (abs_nonneg _).trans he
  have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  rw [affineValue_contact_error]
  calc
    _ ≤ |L 2 * t * (b 3 - v)| + |L 3 * t * (b 4 + b 0)| := abs_add_le _ _
    _ ≤ H * 1 * χ + H * 1 * e := by
      simp only [abs_mul]
      exact add_le_add
        (mul_le_mul (mul_le_mul hL2 ht1 (abs_nonneg _) hH) hv
          (abs_nonneg _) (by positivity))
        (mul_le_mul (mul_le_mul hL3 ht1 (abs_nonneg _) hH) he
          (abs_nonneg _) (by positivity))
    _ = _ := by ring

theorem parameterValue_reconstruction (L : Fin 4 → ℝ) (b : Fin 6 → ℝ)
    (pc qc v D t : ℝ) (hD : D ≠ 0) :
    parameterValue L pc qc v D t ((b 0 - pc) / D) ((b 1 - qc) / D) =
      affineValue L t (b 0 + t * v) (b 1 - t * b 0) := by
  unfold parameterValue
  have hp : D * ((b 0 - pc) / D) = b 0 - pc := by field_simp
  have hr : D * ((b 1 - qc) / D) = b 1 - qc := by field_simp
  rw [hp, hr]
  congr 2 <;> ring

/-- The original line parameters provide affine scalar trajectories. -/
theorem scalarParameter_affine (b : Fin 6 → ℝ) (pc qc D t : ℝ) :
    scalarParameter t ((b 0 - pc) / D) ((b 1 - qc) / D) =
      (b 1 - qc) / D + t * (-2 * ((b 0 - pc) / D)) := by
  unfold scalarParameter
  ring

/-- After fixing the first intercept, the scalar parameter is affine in
the true variables `(t, Y)`. -/
theorem scalarParameter_return (b : Fin 6 → ℝ) (pc qc pa D t : ℝ) :
    ((b 1 + t * b 4) - qc + t * (2 * pc - pa)) / D -
      scalarParameter t ((b 0 - pc) / D) ((b 1 - qc) / D) =
    t * ((b 4 + b 0) + (b 0 - pa)) / D := by
  unfold scalarParameter
  ring

theorem scalarParameter_return_bound (b : Fin 6 → ℝ) (pc qc pa D t χ e : ℝ)
    (hD : 0 < D) (ht : t ∈ Icc (0 : ℝ) 1)
    (hp : |b 0 - pa| ≤ χ) (he : |b 4 + b 0| ≤ e) :
    |((b 1 + t * b 4) - qc + t * (2 * pc - pa)) / D -
      scalarParameter t ((b 0 - pc) / D) ((b 1 - qc) / D)| ≤ (e + χ) / D := by
  rw [scalarParameter_return, abs_div, abs_mul, abs_of_pos hD]
  apply div_le_div_of_nonneg_right _ hD.le
  have hsum : |(b 4 + b 0) + (b 0 - pa)| ≤ e + χ :=
    (abs_add_le _ _).trans (add_le_add he hp)
  have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  simpa using mul_le_mul ht1 hsum (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

end

end Submission.Obl.k4_horizontal_supercritical_three_projections.Parent
