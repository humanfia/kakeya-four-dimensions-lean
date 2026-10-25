/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarHeavyGroups/ScalarBaseLines.lean at aca48c1.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
Original proof: session x0511, branch x0511, commit ccf90c32bd4af25c1ba009c960359aada67a01a5,
Submission/Obl/k4_scalar_mesh_projection/ScalarBaseLines.lean.
-/

import Submission.Lib.K4ContinuousKakeya.Continuous

namespace Submission.Lib.K4ScalarCoreTools.HeavyGroups.Switching
open Set

noncomputable def baseVelocity (v : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![1, v]

noncomputable def unitBaseDirection (v : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  ‖baseVelocity v‖⁻¹ • baseVelocity v

noncomputable def baseLinePoint (b v t : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![t, b + t * v]

theorem one_le_norm_baseVelocity (v : ℝ) : 1 ≤ ‖baseVelocity v‖ := by
  have h := Submission.Lib.K4ContinuousKakeya.abs_apply_le_norm (baseVelocity v) 0
  simpa [baseVelocity] using h

theorem norm_baseVelocity_sq (v : ℝ) : ‖baseVelocity v‖ ^ 2 = 1 + v ^ 2 := by
  rw [EuclideanSpace.norm_eq]
  simp only [baseVelocity, Fin.sum_univ_two, PiLp.toLp_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Real.norm_eq_abs, one_pow, abs_one]
  rw [Real.sq_sqrt (by positivity)]
  rw [sq_abs]

theorem norm_baseVelocity_le (v K : ℝ) (hK : 1 ≤ K) (hv : |v| ≤ K) :
    ‖baseVelocity v‖ ≤ 2 * K := by
  have hsq := norm_baseVelocity_sq v
  have hv2 := pow_le_pow_left₀ (abs_nonneg v) hv 2
  rw [sq_abs] at hv2
  have hnonneg := norm_nonneg (baseVelocity v)
  nlinarith

theorem norm_unitBaseDirection (v : ℝ) : ‖unitBaseDirection v‖ = 1 := by
  have hn : 0 < ‖baseVelocity v‖ := lt_of_lt_of_le one_pos (one_le_norm_baseVelocity v)
  rw [unitBaseDirection, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn),
    inv_mul_cancel₀ hn.ne']

theorem continuous_unitBaseDirection : Continuous unitBaseDirection := by
  have h : Continuous baseVelocity := by unfold baseVelocity; fun_prop
  exact (h.norm.inv₀ (fun v => ne_of_gt
    (lt_of_lt_of_le one_pos (one_le_norm_baseVelocity v)))).smul h

theorem unitBaseDirection_zero (v : ℝ) : unitBaseDirection v 0 = ‖baseVelocity v‖⁻¹ := by
  simp [unitBaseDirection, baseVelocity]

theorem unitBaseDirection_one (v : ℝ) : unitBaseDirection v 1 = ‖baseVelocity v‖⁻¹ * v := by
  simp [unitBaseDirection, baseVelocity]

theorem det_unitBaseDirection (v w : ℝ) :
    Matrix.det (Matrix.of fun i j : Fin 2 => unitBaseDirection (![v, w] i) j) =
      ‖baseVelocity v‖⁻¹ * ‖baseVelocity w‖⁻¹ * (w - v) := by
  simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, unitBaseDirection_zero, unitBaseDirection_one]
  ring

theorem abs_det_unitBaseDirection (v w : ℝ) :
    |Matrix.det (Matrix.of fun i j : Fin 2 => unitBaseDirection (![v, w] i) j)| =
      |v - w| / (‖baseVelocity v‖ * ‖baseVelocity w‖) := by
  rw [det_unitBaseDirection, abs_mul, abs_mul, abs_inv, abs_inv,
    abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _), abs_sub_comm w v]
  rw [div_eq_mul_inv, mul_inv]
  ring

theorem normalized_velocity_pair_bound (v w K : ℝ) (hK : 1 ≤ K)
    (hv : |v| ≤ K) (hw : |w| ≤ K) (hsep : 1 / K ≤ |v - w|) :
    1 / (4 * K ^ 3) ≤
      |Matrix.det (Matrix.of fun i j : Fin 2 => unitBaseDirection (![v, w] i) j)| := by
  have hKp : 0 < K := by linarith
  have hvp : 0 < ‖baseVelocity v‖ := lt_of_lt_of_le one_pos (one_le_norm_baseVelocity v)
  have hwp : 0 < ‖baseVelocity w‖ := lt_of_lt_of_le one_pos (one_le_norm_baseVelocity w)
  rw [abs_det_unitBaseDirection]
  apply (le_div_iff₀ (mul_pos hvp hwp)).mpr
  calc
    _ ≤ (1 / (4 * K ^ 3)) * ((2 * K) * (2 * K)) := by
      gcongr
      · exact norm_baseVelocity_le v K hK hv
      · exact norm_baseVelocity_le w K hK hw
    _ = 1 / K := by field_simp; ring
    _ ≤ |v - w| := hsep


/-- A two-coordinate box bound controls the Euclidean norm. -/
theorem norm_two_box_bound (x : EuclideanSpace ℝ (Fin 2)) (b : ℝ) (hb : 0 ≤ b)
    (hx : ∀ i : Fin 2, |x i| ≤ b) : ‖x‖ ≤ 2 * b := by
  have hnorm : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  have h0 := pow_le_pow_left₀ (abs_nonneg (x 0)) (hx 0) 2
  have h1 := pow_le_pow_left₀ (abs_nonneg (x 1)) (hx 1) 2
  rw [sq_abs] at h0 h1
  nlinarith [norm_nonneg x]

theorem baseLinePoint_on_unit_line (b v t : ℝ) :
    baseLinePoint b v t = baseLinePoint b v 0 +
      (t * ‖baseVelocity v‖) • unitBaseDirection v := by
  have hn : ‖baseVelocity v‖ ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le one_pos (one_le_norm_baseVelocity v))
  rw [unitBaseDirection, smul_smul, mul_assoc, mul_inv_cancel₀ hn, mul_one]
  ext i
  fin_cases i <;> simp [baseLinePoint, baseVelocity]

theorem mem_base_line_tube (b v t r : ℝ) (x : EuclideanSpace ℝ (Fin 2))
    (hx : ‖x - baseLinePoint b v t‖ < r) :
    x ∈ Submission.Lib.K4ContinuousKakeya.tube r (baseLinePoint b v 0)
      (unitBaseDirection v) := by
  apply Metric.mem_thickening_iff.mpr
  refine ⟨baseLinePoint b v t, ⟨t * ‖baseVelocity v‖, (baseLinePoint_on_unit_line b v t).symm⟩, ?_⟩
  simpa only [dist_eq_norm] using hx

/-- A base cell assigned by rounded state centers lies in every true
trajectory tube witnessing that state, once the state mesh is finer. -/
theorem rounded_base_cell_mem_tube (u v t ξ error : ℝ) (hξ : 0 < ξ)
    (herror : 0 ≤ error) (hfiner : 2 * error ≤ ξ)
    (center x : EuclideanSpace ℝ (Fin 2))
    (hcell : ∀ i : Fin 2, |x i - center i| ≤ ξ)
    (hstate : ∀ i : Fin 2, |center i - baseLinePoint u v t i| ≤ error) :
    x ∈ Submission.Lib.K4ContinuousKakeya.tube (4 * ξ) (baseLinePoint u v 0)
      (unitBaseDirection v) := by
  apply mem_base_line_tube
  have hcoord (i : Fin 2) : |(x - baseLinePoint u v t) i| ≤ ξ + error := by
    change |x i - baseLinePoint u v t i| ≤ ξ + error
    exact (abs_sub_le (x i) (center i) (baseLinePoint u v t i)).trans
      (add_le_add (hcell i) (hstate i))
  have hnorm := norm_two_box_bound (x - baseLinePoint u v t) (ξ + error) (by positivity) hcoord
  linarith

end Submission.Lib.K4ScalarCoreTools.HeavyGroups.Switching
