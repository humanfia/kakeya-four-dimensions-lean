/- Adapted from this LOT tree, o197, session x0690, MinorFrameInverse.lean,
   branch snapshot 9f1b6476; preserving original attributions below. -/
import Submission.Obl.k4_raw_localized_native_systems.NativeAxes
import Submission.Lib.K4ChartLifting.Bounds

namespace Submission.Obl.k4_raw_localized_native_systems

open Submission.Obl.k4_finite_width_output_exclusion
open Pairing

noncomputable section

theorem inverse_entry_le_minor {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0)
    (i j : Fin 2) : |Q⁻¹ i j| ≤ (minorWidth Q)⁻¹ := by
  have hL := longCol_norm_pos hQ
  have hd := abs_pos.mpr hQ
  have hentry (i j : Fin 2) : |Q i j| ≤ ‖longCol Q‖ := by
    fin_cases i <;> fin_cases j
    · exact (abs_coord_le_norm_fin2 (col0 Q) 0).trans (longCol_norm_ge Q).1
    · exact (abs_coord_le_norm_fin2 (col1 Q) 0).trans (longCol_norm_ge Q).2
    · exact (abs_coord_le_norm_fin2 (col0 Q) 1).trans (longCol_norm_ge Q).1
    · exact (abs_coord_le_norm_fin2 (col1 Q) 1).trans (longCol_norm_ge Q).2
  have he : (minorWidth Q)⁻¹ = |Q.det|⁻¹ * ‖longCol Q‖ := by
    simp [minorWidth, div_eq_mul_inv, mul_comm]
  rw [he, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j <;> dsimp <;>
    simp only [abs_mul, abs_inv, abs_neg] <;>
    apply mul_le_mul_of_nonneg_left (hentry _ _) (inv_nonneg.mpr (abs_nonneg _))

theorem inverse_action_le_minor {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0)
    (z : Plane) : ‖Matrix.toEuclideanLin Q⁻¹ z‖ ≤ (4 * (minorWidth Q)⁻¹) * ‖z‖ := by
  apply (Submission.Lib.K4ChartLifting.norm_toEuclideanLin_le Q⁻¹ z).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg z)
  calc
    (∑ i : Fin 2, ∑ j : Fin 2, |Q⁻¹ i j|) ≤
        ∑ _i : Fin 2, ∑ _j : Fin 2, (minorWidth Q)⁻¹ := by
      gcongr with i j
      exact inverse_entry_le_minor hQ i j
    _ = 4 * (minorWidth Q)⁻¹ := by simp; ring

theorem inverse_action_col0 {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0) :
    Matrix.toEuclideanLin Q⁻¹ (col0 Q) = WithLp.toLp 2 ![1, 0] := by
  ext i
  fin_cases i <;>
    simp [Submission.Lib.K4ChartLifting.toEuclideanLin_apply_two, Matrix.inv_def,
      Ring.inverse_eq_inv', Matrix.adjugate_fin_two, col0] <;>
    field_simp <;> simp [Matrix.det_fin_two] <;> ring

theorem inverse_action_col1 {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0) :
    Matrix.toEuclideanLin Q⁻¹ (col1 Q) = WithLp.toLp 2 ![0, 1] := by
  ext i
  fin_cases i <;>
    simp [Submission.Lib.K4ChartLifting.toEuclideanLin_apply_two, Matrix.inv_def,
      Ring.inverse_eq_inv', Matrix.adjugate_fin_two, col1] <;>
    field_simp <;> simp [Matrix.det_fin_two] <;> ring

theorem norm_inverse_longCol {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0) :
    ‖Matrix.toEuclideanLin Q⁻¹ (longCol Q)‖ = 1 := by
  unfold longCol
  split_ifs
  · rw [inverse_action_col0 hQ]
    norm_num [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  · rw [inverse_action_col1 hQ]
    norm_num [EuclideanSpace.norm_eq, Fin.sum_univ_two]

theorem tangentOfMinorNormal (Q : Matrix (Fin 2) (Fin 2) ℝ) :
    tangentOfNormal (minorNormal Q) = ‖longCol Q‖⁻¹ • longCol Q := by
  ext i
  fin_cases i <;> simp [tangentOfNormal, minorNormal, rot90]

theorem norm_inverse_minor_tangent {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0) :
    ‖Matrix.toEuclideanLin Q⁻¹ (tangentOfNormal (minorNormal Q))‖ = ‖longCol Q‖⁻¹ := by
  rw [tangentOfMinorNormal, map_smul, norm_smul, norm_inverse_longCol hQ,
    mul_one, Real.norm_eq_abs, abs_inv, abs_norm]

theorem tangentOfNormal_sub (n m : Plane) :
    tangentOfNormal (n - m) = tangentOfNormal n - tangentOfNormal m := by
  ext i
  fin_cases i <;> simp [tangentOfNormal, rot90] <;> ring

theorem tangentOfNormal_add (n m : Plane) :
    tangentOfNormal (n + m) = tangentOfNormal n + tangentOfNormal m := by
  ext i
  fin_cases i <;> simp [tangentOfNormal, rot90] <;> ring

/-- The inverse on an aligned full-time tangent spends the earlier major-axis
reciprocal and the angle divided by the minor width, rather than the unrestricted
inverse-frame budget. -/
theorem inverse_aligned_tangent {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0)
    {n : Plane} {θ : ℝ}
    (hangle : min ‖n - minorNormal Q‖ ‖n + minorNormal Q‖ ≤ θ) :
    ‖Matrix.toEuclideanLin Q⁻¹ (tangentOfNormal n)‖ ≤
      ‖longCol Q‖⁻¹ + (4 * (minorWidth Q)⁻¹) * θ := by
  have hfactor : 0 ≤ 4 * (minorWidth Q)⁻¹ :=
    mul_nonneg (by norm_num) (inv_nonneg.mpr (minorWidth_nonneg Q))
  rcases min_le_iff.mp hangle with h | h
  · have hd : ‖tangentOfNormal n - tangentOfNormal (minorNormal Q)‖ ≤ θ := by
      rw [← tangentOfNormal_sub, tangentOfNormal_norm]
      exact h
    have he : tangentOfNormal n = tangentOfNormal (minorNormal Q) +
        (tangentOfNormal n - tangentOfNormal (minorNormal Q)) := by abel
    rw [he, map_add]
    apply (norm_add_le _ _).trans
    rw [norm_inverse_minor_tangent hQ]
    exact add_le_add le_rfl ((inverse_action_le_minor hQ _).trans
      (mul_le_mul_of_nonneg_left hd hfactor))
  · have hd : ‖tangentOfNormal n + tangentOfNormal (minorNormal Q)‖ ≤ θ := by
      rw [← tangentOfNormal_add, tangentOfNormal_norm]
      exact h
    have he : tangentOfNormal n = -tangentOfNormal (minorNormal Q) +
        (tangentOfNormal n + tangentOfNormal (minorNormal Q)) := by abel
    rw [he, map_add, map_neg]
    apply (norm_add_le _ _).trans
    rw [norm_neg, norm_inverse_minor_tangent hQ]
    exact add_le_add le_rfl ((inverse_action_le_minor hQ _).trans
      (mul_le_mul_of_nonneg_left hd hfactor))

theorem normal_tangent_decomposition {n : Plane} (hn : ‖n‖ = 1) (v : Plane) :
    v = inner ℝ (tangentOfNormal n) v • tangentOfNormal n + inner ℝ n v • n := by
  have hs : n 0 ^ 2 + n 1 ^ 2 = 1 := by
    simpa only [hn, one_pow] using (norm_sq_fin2' n).symm
  ext i
  fin_cases i
  · simp [inner_fin2, tangentOfNormal, rot90]
    nlinarith [congrArg (fun x : ℝ => v 0 * x) hs]
  · simp [inner_fin2, tangentOfNormal, rot90]
    nlinarith [congrArg (fun x : ℝ => v 1 * x) hs]

/-- Comparison of an earlier center velocity with the current normal center
uses one common trajectory, the aligned tangent, and the current normal error. -/
theorem inverse_center_speed_le {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0)
    {n v u : Plane} {β K V ε θ : ℝ} (hn : ‖n‖ = 1)
    (hangle : min ‖n - minorNormal Q‖ ‖n + minorNormal Q‖ ≤ θ)
    (hv : ‖v‖ ≤ K) (hearlier : ‖Matrix.toEuclideanLin Q⁻¹ (v - u)‖ ≤ V)
    (hcurrent : |inner ℝ n (v - β • n)| ≤ ε) :
    ‖Matrix.toEuclideanLin Q⁻¹ (β • n - u)‖ ≤
      V + K * (‖longCol Q‖⁻¹ + (4 * (minorWidth Q)⁻¹) * θ) +
        ε * (4 * (minorWidth Q)⁻¹) := by
  have htangent := inverse_aligned_tangent hQ hangle
  have hninv : ‖Matrix.toEuclideanLin Q⁻¹ n‖ ≤ 4 * (minorWidth Q)⁻¹ := by
    simpa only [hn, mul_one] using inverse_action_le_minor hQ n
  have hK : 0 ≤ K := (norm_nonneg v).trans hv
  have he : ‖tangentOfNormal n‖ = 1 := (tangentOfNormal_norm n).trans hn
  have htv : |inner ℝ (tangentOfNormal n) v| ≤ K := by
    exact (abs_real_inner_le_norm _ _).trans (by simpa only [he, one_mul] using hv)
  have hself : inner ℝ n n = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
  have hnv : |β - inner ℝ n v| ≤ ε := by
    simpa only [inner_sub_right, real_inner_smul_right, hself, mul_one, abs_sub_comm] using hcurrent
  have hε : 0 ≤ ε := (abs_nonneg _).trans hnv
  have heq : β • n - u = (v - u) - inner ℝ (tangentOfNormal n) v • tangentOfNormal n +
      (β - inner ℝ n v) • n := by
    have hdecomp := normal_tangent_decomposition hn v
    calc
      _ = (inner ℝ (tangentOfNormal n) v • tangentOfNormal n + inner ℝ n v • n - u) -
          inner ℝ (tangentOfNormal n) v • tangentOfNormal n + (β - inner ℝ n v) • n := by module
      _ = _ := by rw [← hdecomp]
  rw [heq, map_add, map_sub, map_smul, map_smul]
  calc
    _ ≤ (‖Matrix.toEuclideanLin Q⁻¹ (v - u)‖ +
        |inner ℝ (tangentOfNormal n) v| * ‖Matrix.toEuclideanLin Q⁻¹ (tangentOfNormal n)‖) +
        |β - inner ℝ n v| * ‖Matrix.toEuclideanLin Q⁻¹ n‖ := by
      have ht :
          ‖(Matrix.toEuclideanLin Q⁻¹ (v - u) -
              inner ℝ (tangentOfNormal n) v • Matrix.toEuclideanLin Q⁻¹ (tangentOfNormal n)) +
            (β - inner ℝ n v) • Matrix.toEuclideanLin Q⁻¹ n‖ ≤
          (‖Matrix.toEuclideanLin Q⁻¹ (v - u)‖ +
              ‖inner ℝ (tangentOfNormal n) v • Matrix.toEuclideanLin Q⁻¹ (tangentOfNormal n)‖) +
            ‖(β - inner ℝ n v) • Matrix.toEuclideanLin Q⁻¹ n‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      simpa only [norm_smul, Real.norm_eq_abs] using ht
    _ ≤ _ := by gcongr

end
end Submission.Obl.k4_raw_localized_native_systems
