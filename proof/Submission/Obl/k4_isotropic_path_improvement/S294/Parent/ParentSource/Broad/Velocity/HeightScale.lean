-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Velocity.HeightScale, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Velocity/HeightScale.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Velocity/HeightScale.lean.
All earlier source attributions below are retained. -/
import Submission.Lib.K4NativePreparationNumerics.Frames
import Mathlib

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity

open Matrix
open scoped BigOperators

noncomputable section

abbrev Space := EuclideanSpace ℝ (Fin 4)

def heightScale (a : ℝ) (x : Space) : Space :=
  WithLp.toLp 2 (fun j => if j = 3 then a * x j else x j)

def heightUnit (a : ℝ) (x : Space) : Space := ‖heightScale a x‖⁻¹ • heightScale a x

theorem heightScale_ne_zero {a : ℝ} (ha : a ≠ 0) {x : Space} (hx : x ≠ 0) :
    heightScale a x ≠ 0 := by
  intro hz
  apply hx
  ext j
  have hj := congrArg (fun y : Space => y j) hz
  by_cases h : j = 3
  · simpa only [heightScale, h, ite_true, PiLp.zero_apply,
      mul_eq_zero, ha, false_or] using hj
  · simpa only [heightScale, ite_eq_right h, PiLp.zero_apply] using hj

theorem norm_heightScale_le_four {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    {x : Space} (hx : ‖x‖ = 1) : ‖heightScale a x‖ ≤ 4 := by
  have hcoord (j : Fin 4) : |x j| ≤ 1 := by
    simpa only [hx, Real.norm_eq_abs] using PiLp.norm_apply_le x j
  have hs (j : Fin 4) : |heightScale a x j| ≤ 1 := by
    change |if j = 3 then a * x j else x j| ≤ 1
    split_ifs
    · rw [abs_mul, abs_of_nonneg ha]
      exact (mul_le_mul_of_nonneg_left (hcoord j) ha).trans (by simpa only [mul_one] using ha1)
    · exact hcoord j
  calc
    _ ≤ ∑ j : Fin 4, |heightScale a x j| :=
      Submission.Lib.K4NativePreparationNumerics.euclidean_norm_le_sum_abs _
    _ ≤ ∑ _j : Fin 4, (1 : ℝ) := Finset.sum_le_sum (fun j _ => hs j)
    _ = _ := by norm_num

theorem norm_heightUnit {a : ℝ} (ha : a ≠ 0) {x : Space} (hx : x ≠ 0) :
    ‖heightUnit a x‖ = 1 := by
  rw [heightUnit, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr (heightScale_ne_zero ha hx))]

theorem measurable_heightScale (a : ℝ) : Measurable (heightScale a) := by
  apply (WithLp.measurable_toLp 2 _).comp
  apply measurable_pi_iff.mpr
  intro j
  by_cases hj : j = 3
  · simp only [hj, ite_true]
    exact measurable_const.mul (PiLp.continuous_apply 2 _ 3).measurable
  · simp only [ite_eq_right hj]
    exact (PiLp.continuous_apply 2 _ j).measurable

theorem measurable_heightUnit (a : ℝ) : Measurable (heightUnit a) :=
  ((measurable_heightScale a).norm.inv).smul (measurable_heightScale a)

/-- Compressing only the hidden coordinate loses ONE determinant factor.
Normalizing the four directions costs a fixed constant. -/
theorem det_heightUnit_ge {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (v : Fin 4 → Space) (hv : ∀ i, ‖v i‖ = 1) :
    (a / 256) * |(Matrix.of fun i j => v i j).det| ≤
      |(Matrix.of fun i j => heightUnit a (v i) j).det| := by
  have hne (i : Fin 4) : v i ≠ 0 := norm_ne_zero_iff.mp (by rw [hv i]; norm_num)
  have hp (i : Fin 4) : 0 < ‖heightScale a (v i)‖ :=
    norm_pos_iff.mpr (heightScale_ne_zero ha.ne' (hne i))
  let D : Fin 4 → ℝ := fun j => if j = 3 then a else 1
  have hscaled : (Matrix.of fun i j => heightScale a (v i) j) =
      (Matrix.of fun i j => v i j) * Matrix.diagonal D := by
    ext i j
    rw [Matrix.mul_diagonal]
    by_cases hj : j = 3 <;> simp [heightScale, D, hj, mul_comm]
  have hunit : (Matrix.of fun i j => heightUnit a (v i) j) =
      Matrix.diagonal (fun i => ‖heightScale a (v i)‖⁻¹) *
        (Matrix.of fun i j => heightScale a (v i) j) := by
    ext i j
    simp [heightUnit, Matrix.diagonal_mul, PiLp.smul_apply]
  have hprod : 0 ≤ ∏ i : Fin 4, ‖heightScale a (v i)‖⁻¹ := by positivity
  have hdet : |(Matrix.of fun i j => heightUnit a (v i) j).det| =
      (∏ i : Fin 4, ‖heightScale a (v i)‖⁻¹) * |(Matrix.of fun i j => v i j).det| * a := by
    rw [hunit, hscaled, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_mul,
      Matrix.det_diagonal, abs_mul, abs_mul, abs_of_nonneg hprod]
    have hD : (∏ j : Fin 4, D j) = a := by simp [D]
    rw [hD, abs_of_pos ha]
    ring
  have hrow (i : Fin 4) : (1 / 4 : ℝ) ≤ ‖heightScale a (v i)‖⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (hp i)
      (norm_heightScale_le_four ha.le ha1 (hv i))
  have hlower : (1 / 256 : ℝ) ≤ ∏ i : Fin 4, ‖heightScale a (v i)‖⁻¹ := by
    have hh := Finset.prod_le_prod₀ (s := (Finset.univ : Finset (Fin 4)))
      (f := fun _ => (1 / 4 : ℝ)) (g := fun i => ‖heightScale a (v i)‖⁻¹)
      (fun _ _ => by norm_num) (fun i _ => hrow i)
    norm_num at hh
    simpa only [Finset.prod_inv_distrib] using hh
  rw [hdet]
  calc
    _ = (1 / 256 : ℝ) * |(Matrix.of fun i j => v i j).det| * a := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hlower (abs_nonneg _)) ha.le

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity
