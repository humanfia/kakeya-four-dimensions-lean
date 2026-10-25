/- Adapted from same-tree o105, session x0351, commit 735310f,
   Submission/Obl/k4_critical_path_framework/Narrowness.lean. -/
import Submission.Obl.k4_finite_width_critical_contradiction.Definitions

/-! The chart size condition makes logarithmic narrowness nonnegative,
up to the permitted subpower slack. -/

namespace Submission.Obl.k4_finite_width_critical_contradiction

/-- The two-dimensional determinant is bounded by the square of the entry sum. -/
theorem abs_det_le_entry_sum_sq (Q : Frame) :
    |Matrix.det Q| ≤ (∑ i : Fin 2, ∑ j : Fin 2, |Q i j|) ^ 2 := by
  have hdet : |Matrix.det Q| ≤ |Q 0 0| * |Q 1 1| + |Q 0 1| * |Q 1 0| := by
    simpa only [Matrix.det_fin_two, abs_mul] using
      abs_sub (Q 0 0 * Q 1 1) (Q 0 1 * Q 1 0)
  simp only [Fin.sum_univ_two]
  nlinarith [mul_nonneg (abs_nonneg (Q 0 0)) (abs_nonneg (Q 1 0)),
    mul_nonneg (abs_nonneg (Q 0 1)) (abs_nonneg (Q 1 1)),
    sq_nonneg (|Q 0 0| + |Q 0 1| - (|Q 1 0| + |Q 1 1|))]

/-- The dyadic time cost cancels the determinant scale of a genuine chart. -/
theorem determinant_time_bound {Q : Frame} {T : ℕ} {κ : ℝ} (hκ : 0 ≤ κ)
    (hsize : (∑ i : Fin 2, ∑ j : Fin 2, |Q i j|) ≤ κ / (2 : ℝ) ^ T) :
    |Matrix.det Q| * (4 : ℝ) ^ T ≤ κ ^ 2 := by
  let S : ℝ := ∑ i : Fin 2, ∑ j : Fin 2, |Q i j|
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hq : 0 < (2 : ℝ) ^ T := by positivity
  have hSq : S * (2 : ℝ) ^ T ≤ κ := (le_div_iff₀ hq).mp hsize
  have hfour : (4 : ℝ) ^ T = ((2 : ℝ) ^ T) ^ 2 := by
    calc
      (4 : ℝ) ^ T = ((2 : ℝ) ^ 2) ^ T := by norm_num
      _ = ((2 : ℝ) ^ T) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [hfour]
  calc
    |Matrix.det Q| * ((2 : ℝ) ^ T) ^ 2 ≤ S ^ 2 * ((2 : ℝ) ^ T) ^ 2 :=
      mul_le_mul_of_nonneg_right (abs_det_le_entry_sum_sq Q) (sq_nonneg _)
    _ = (S * (2 : ℝ) ^ T) ^ 2 := (mul_pow _ _ _).symm
    _ ≤ κ ^ 2 := (sq_le_sq₀ (mul_nonneg hS hq.le) hκ).mpr hSq

theorem Chart.narrowness_bound {Nk κ j r Bv : ℝ} {M D T : ℕ}
    {Ev : Set Incidence} {c u : Spatial} {Q : Frame} {R : Test}
    {A : Set Trajectory} {F : Set Incidence} {ex : Prop} (hκ : 0 ≤ κ)
    (hc : Chart Nk M D κ T j r Bv Ev c u Q R A F ex) :
    |Matrix.det Q| * (4 : ℝ) ^ T ≤ κ ^ 2 :=
  determinant_time_bound hκ hc.2.2.2.1

/-- A subpower slack gives precisely a vanishing error in the width exponent. -/
theorem Chart.narrowness_bound_rpow {Nk κ j r Bv ε : ℝ} {M D T : ℕ}
    {Ev : Set Incidence} {c u : Spatial} {Q : Frame} {R : Test}
    {A : Set Trajectory} {F : Set Incidence} {ex : Prop} (hNk : 0 ≤ Nk) (hκ : 0 ≤ κ)
    (hκN : κ ≤ Nk ^ ε) (hc : Chart Nk M D κ T j r Bv Ev c u Q R A F ex) :
    |Matrix.det Q| * (4 : ℝ) ^ T ≤ Nk ^ (2 * ε) := by
  calc
    |Matrix.det Q| * (4 : ℝ) ^ T ≤ κ ^ 2 := hc.narrowness_bound hκ
    _ ≤ (Nk ^ ε) ^ 2 := (sq_le_sq₀ hκ (Real.rpow_nonneg hNk _)).mpr hκN
    _ = Nk ^ (2 * ε) := by rw [mul_comm (2 : ℝ) ε, Real.rpow_mul hNk, Real.rpow_two]

/-- Polynomial control of the inverse frame gives a finite lower determinant bound. -/
theorem inverse_frame_det_lower {Nk : ℝ} {M : ℕ} {Q : Frame} (hNk : 0 < Nk)
    (hQdet : Matrix.det Q ≠ 0)
    (hframe : (∑ i : Fin 2, ∑ j : Fin 2, (|Q i j| + |Q⁻¹ i j|)) ≤ Nk ^ M) :
    (Nk ^ M)⁻¹ ^ 2 ≤ |Matrix.det Q| := by
  have hinv : (∑ i : Fin 2, ∑ j : Fin 2, |Q⁻¹ i j|) ≤ Nk ^ M := by
    apply le_trans _ hframe
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      le_add_of_nonneg_left (abs_nonneg _)
  have hsum : 0 ≤ ∑ i : Fin 2, ∑ j : Fin 2, |Q⁻¹ i j| :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hdetpos : 0 < |Matrix.det Q| := abs_pos.mpr hQdet
  have hbound : |Matrix.det Q|⁻¹ ≤ (Nk ^ M) ^ 2 := by
    calc
      |Matrix.det Q|⁻¹ = |Matrix.det Q⁻¹| := by rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv, abs_inv]
      _ ≤ (∑ i : Fin 2, ∑ j : Fin 2, |Q⁻¹ i j|) ^ 2 := abs_det_le_entry_sum_sq _
      _ ≤ (Nk ^ M) ^ 2 := (sq_le_sq₀ hsum (by positivity)).mpr hinv
  have hmul := mul_le_mul_of_nonneg_right hbound hdetpos.le
  have hone : 1 ≤ (Nk ^ M) ^ 2 * |Matrix.det Q| := by
    simpa only [inv_mul_cancel₀ hdetpos.ne'] using hmul
  rw [inv_pow, ← one_div]
  exact (div_le_iff₀ (by positivity : 0 < (Nk ^ M) ^ 2)).mpr (by nlinarith)

end Submission.Obl.k4_finite_width_critical_contradiction
