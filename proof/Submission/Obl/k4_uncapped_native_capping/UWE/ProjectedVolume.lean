/-
Adapted from this LOT tree o198, session x0693, commit b5c1b640df5e526ffc014739d6614359923ec044,
Submission/Obl/k4_balanced_native_packet_transport/UWE/ProjectedVolume.lean. Existing source attributions below are retained.
-/
/-
Adapted from this LOT tree, o120, session x0649, commit 99e461c8faeab846d12253887b2a587a38b5aa0e,
Submission/Obl/k4_unbounded_width_exclusion/ProjectedVolume.lean (namespace Submission.Obl.k4_unbounded_width_exclusion renamed to
Submission.Obl.k4_uncapped_native_capping.UWE).
-/
import Submission.Obl.k4_multilinear_kakeya.Plane
import Submission.Obl.k4_dk4_smoothed_problem.Spread.BoxSlice
import Submission.Obl.k4_scalar_coefficient_clustering.Geometry

noncomputable section

namespace Submission.Obl.k4_uncapped_native_capping.UWE

open MeasureTheory Set

private def otherAxis (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

private def projectionFrame (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (e : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![e 0, e 1; Q⁻¹ (otherAxis i) 0, Q⁻¹ (otherAxis i) 1]

/-- One row of the normalized packet frame supplies the missing coordinate
after projecting onto the full tangent. -/
private theorem projectionFrame_det (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.det ≠ 0)
    (e : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    |(projectionFrame Q e i).det| * |Q.det| =
      |(Matrix.toEuclideanLin Q.transpose e) i| := by
  have hIQ : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q (isUnit_iff_ne_zero.mpr hQ)
  have hrow₀ (j : Fin 2) : (projectionFrame Q e i * Q) 0 j =
      (Matrix.toEuclideanLin Q.transpose e) j := by
    fin_cases j <;>
      simp [projectionFrame, Matrix.mul_apply, Fin.sum_univ_two, Matrix.toEuclideanLin,
        Matrix.toLpLin_apply] <;> ring
  have hrow₁ (j : Fin 2) : (projectionFrame Q e i * Q) 1 j =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) (otherAxis i) j := by
    have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A (otherAxis i) j) hIQ
    simpa [projectionFrame, Matrix.mul_apply, Fin.sum_univ_two] using h
  rw [← abs_mul, ← Matrix.det_mul, Matrix.det_fin_two, hrow₀, hrow₁, hrow₀, hrow₁]
  fin_cases i
  · norm_num [otherAxis, Matrix.one_apply]
  · norm_num [otherAxis, Matrix.one_apply]
    rw [← neg_add, abs_neg, add_comm]

private def projectedBaseMatrix (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (e u : EuclideanSpace ℝ (Fin 2)) (q : ℝ) (i : Fin 2) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![q⁻¹, 0, 0; 0, q⁻¹ * e 0, q⁻¹ * e 1;
    -(Matrix.toEuclideanLin Q⁻¹ u) (otherAxis i), Q⁻¹ (otherAxis i) 0, Q⁻¹ (otherAxis i) 1]

private theorem projectedBaseMatrix_det (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (e u : EuclideanSpace ℝ (Fin 2)) (q : ℝ) (i : Fin 2) :
    (projectedBaseMatrix Q e u q i).det = q⁻¹ ^ 2 * (projectionFrame Q e i).det := by
  simp [projectedBaseMatrix, projectionFrame, Matrix.det_fin_three, Matrix.det_fin_two]
  ring

/-- Tangential fullness controls the inverse projection Jacobian, without
any lower bound on the minor axis of the packet. -/
private theorem exists_projectedBaseMatrix_jacobian
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.det ≠ 0)
    (e u : EuclideanSpace ℝ (Fin 2)) {K q : ℝ} (hK : 0 < K) (hq : 0 < q)
    (hfull : q / K ≤ ‖Matrix.toEuclideanLin Q.transpose e‖) :
    ∃ i : Fin 2, (projectedBaseMatrix Q e u q i).det ≠ 0 ∧
      |(projectedBaseMatrix Q e u q i).det⁻¹| ≤ 2 * K * q * |Q.det| := by
  let f := Matrix.toEuclideanLin Q.transpose e
  have hnorm : ‖f‖ ≤ |f 0| + |f 1| :=
    Submission.Obl.k4_scalar_coefficient_clustering.plane_norm_le_abs_add f
  have hi : ∃ i : Fin 2, q / (2 * K) ≤ |f i| := by
    by_cases h : q / (2 * K) ≤ |f 0|
    · exact ⟨0, h⟩
    · refine ⟨1, ?_⟩
      have heq : q / K = 2 * (q / (2 * K)) := by field_simp
      rw [heq] at hfull
      linarith
  obtain ⟨i, hi⟩ := hi
  have hfi : 0 < |f i| := (div_pos hq (by positivity : 0 < 2 * K)).trans_le hi
  have hdetR := projectionFrame_det Q hQ e i
  change |(projectionFrame Q e i).det| * |Q.det| = |f i| at hdetR
  have hR : (projectionFrame Q e i).det ≠ 0 := by
    intro h
    rw [h, abs_zero, zero_mul] at hdetR
    linarith
  have hA : (projectedBaseMatrix Q e u q i).det ≠ 0 := by
    rw [projectedBaseMatrix_det]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hq.ne')) hR
  have hprod : |(projectedBaseMatrix Q e u q i).det| * (q ^ 2 * |Q.det|) = |f i| := by
    rw [projectedBaseMatrix_det, abs_mul, abs_pow, abs_inv, abs_of_pos hq]
    calc
      _ = (q⁻¹ ^ 2 * q ^ 2) * (|(projectionFrame Q e i).det| * |Q.det|) := by ring
      _ = |f i| := by rw [← mul_pow, inv_mul_cancel₀ hq.ne', one_pow, one_mul, hdetR]
  have hJac : |(projectedBaseMatrix Q e u q i).det⁻¹| = q ^ 2 * |Q.det| / |f i| := by
    rw [abs_inv]
    have heq : |(projectedBaseMatrix Q e u q i).det| = |f i| / (q ^ 2 * |Q.det|) :=
      (eq_div_iff (mul_ne_zero (pow_ne_zero 2 hq.ne') (abs_ne_zero.mpr hQ))).2 hprod
    rw [heq, inv_div]
  refine ⟨i, hA, ?_⟩
  rw [hJac, div_le_iff₀ hfi]
  have hqi : q ≤ (2 * K) * |f i| := by
    simpa only [mul_comm] using (div_le_iff₀ (show 0 < 2 * K by positivity)).1 hi
  have hmul := mul_le_mul_of_nonneg_right hqi (mul_nonneg hq.le (abs_nonneg Q.det))
  convert hmul using 1 <;> ring

private theorem volume_projectedCylinder (U : Set (EuclideanSpace ℝ (Fin 2)))
    (hU : MeasurableSet U) (r : Fin 3 → ℝ) (K : ℝ) :
    volume {z : Fin 3 → ℝ |
      (WithLp.toLp 2 ![z 0 - r 0, z 1 - r 1] : EuclideanSpace ℝ (Fin 2)) ∈ U ∧
      |z 2 - r 2| ≤ K} = ENNReal.ofReal (2 * K) * volume U := by
  let B : Set (Fin 2 → ℝ) := {z | (WithLp.toLp 2 (z - ![r 0, r 1]) : EuclideanSpace ℝ (Fin 2)) ∈ U}
  have hpres : MeasurePreserving
      (fun z : Fin 2 → ℝ => (WithLp.toLp 2 (z - ![r 0, r 1]) : EuclideanSpace ℝ (Fin 2)))
      volume volume := by
    simpa only [Function.comp_def, sub_eq_add_neg] using
      (PiLp.volume_preserving_toLp (Fin 2)).comp
        (measurePreserving_add_right (volume : Measure (Fin 2 → ℝ)) (-(![r 0, r 1] : Fin 2 → ℝ)))
  have hBvol : volume B = volume U := hpres.measure_preimage hU.nullMeasurableSet
  have heq : {z : Fin 3 → ℝ |
      (WithLp.toLp 2 ![z 0 - r 0, z 1 - r 1] : EuclideanSpace ℝ (Fin 2)) ∈ U ∧
      |z 2 - r 2| ≤ K} =
      {z : Fin 3 → ℝ | Fin.init z ∈ B ∧ z 2 ∈ Icc (r 2 - K) (r 2 + K)} := by
    ext z
    have hcoord : (![z 0 - r 0, z 1 - r 1] : Fin 2 → ℝ) = Fin.init z - ![r 0, r 1] := by
      ext i; fin_cases i <;> rfl
    simp only [mem_ofPred_eq, hcoord, B, mem_Icc, abs_le]
    constructor <;> rintro ⟨hb, h₁, h₂⟩ <;> exact ⟨hb, by linarith, by linarith⟩
  rw [heq, Submission.Obl.k4_dk4_smoothed_problem.Spread.volume_cylinder, hBvol, Real.volume_Icc]
  congr 2
  ring

/-- Projection of a packet to its normalized time and full tangent has a
volume ceiling proportional to its ORIGINAL `q * |det Q|` budget. The spatial
frame may have an arbitrarily small minor axis. -/
theorem volume_packet_projected_base
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.det ≠ 0)
    (e c u : EuclideanSpace ℝ (Fin 2)) (t₀ Z : ℝ)
    {K q : ℝ} (hK : 0 < K) (hq : 0 < q)
    (hfull : q / K ≤ ‖Matrix.toEuclideanLin Q.transpose e‖)
    (U : Set (EuclideanSpace ℝ (Fin 2))) (hU : MeasurableSet U) :
    volume {z : EuclideanSpace ℝ (Fin 3) |
      ‖Matrix.toEuclideanLin Q⁻¹ (WithLp.toLp 2 ![z 1, z 2] - c - z 0 • u)‖ ≤ K ∧
      (WithLp.toLp 2 ![(z 0 - t₀) / q,
        (inner ℝ e (WithLp.toLp 2 ![z 1, z 2]) - Z) / q] : EuclideanSpace ℝ (Fin 2)) ∈ U} ≤
      ENNReal.ofReal (4 * K ^ 2 * q * |Q.det|) * volume U := by
  obtain ⟨i, hdet, hJac⟩ := exists_projectedBaseMatrix_jacobian Q hQ e u hK hq hfull
  let A := projectedBaseMatrix Q e u q i
  let r : Fin 3 → ℝ := ![t₀ / q, Z / q, (Matrix.toEuclideanLin Q⁻¹ c) (otherAxis i)]
  let T : Set (Fin 3 → ℝ) := {z |
    (WithLp.toLp 2 ![z 0 - r 0, z 1 - r 1] : EuclideanSpace ℝ (Fin 2)) ∈ U ∧ |z 2 - r 2| ≤ K}
  have hT : MeasurableSet T := by
    have hf : Measurable (fun z : Fin 3 → ℝ =>
      (WithLp.toLp 2 ![z 0 - r 0, z 1 - r 1] : EuclideanSpace ℝ (Fin 2))) := by fun_prop
    have hg : Measurable (fun z : Fin 3 → ℝ => |z 2 - r 2|) := by fun_prop
    exact (hU.preimage hf).inter (measurableSet_le hg measurable_const)
  have hbase (z : EuclideanSpace ℝ (Fin 3)) :
      (WithLp.toLp 2 ![(A.mulVec z.ofLp) 0 - r 0, (A.mulVec z.ofLp) 1 - r 1] :
        EuclideanSpace ℝ (Fin 2)) =
      WithLp.toLp 2 ![(z 0 - t₀) / q,
        (inner ℝ e (WithLp.toLp 2 ![z 1, z 2]) - Z) / q] := by
    ext j
    fin_cases j <;>
      simp [A, r, projectedBaseMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        PiLp.inner_apply, Fin.sum_univ_two, div_eq_mul_inv] <;> ring
  have htrans (z : EuclideanSpace ℝ (Fin 3)) :
      (A.mulVec z.ofLp) 2 - r 2 =
      (Matrix.toEuclideanLin Q⁻¹ (WithLp.toLp 2 ![z 1, z 2] - c - z 0 • u)) (otherAxis i) := by
    fin_cases i <;>
      simp [A, r, projectedBaseMatrix, otherAxis, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
        Matrix.vecHead, Matrix.vecTail, Function.comp_def, Pi.smul_apply, smul_eq_mul] <;> ring
  have hsub : {z : EuclideanSpace ℝ (Fin 3) |
      ‖Matrix.toEuclideanLin Q⁻¹ (WithLp.toLp 2 ![z 1, z 2] - c - z 0 • u)‖ ≤ K ∧
      (WithLp.toLp 2 ![(z 0 - t₀) / q,
        (inner ℝ e (WithLp.toLp 2 ![z 1, z 2]) - Z) / q] : EuclideanSpace ℝ (Fin 2)) ∈ U} ⊆
      (fun z : EuclideanSpace ℝ (Fin 3) => A.mulVec z.ofLp) ⁻¹' T := by
    intro z hz
    change (WithLp.toLp 2 ![(A.mulVec z.ofLp) 0 - r 0, (A.mulVec z.ofLp) 1 - r 1] :
      EuclideanSpace ℝ (Fin 2)) ∈ U ∧ |(A.mulVec z.ofLp) 2 - r 2| ≤ K
    rw [hbase, htrans]
    exact ⟨hz.2, (PiLp.norm_apply_le _ _).trans hz.1⟩
  calc
    _ ≤ volume ((fun z : EuclideanSpace ℝ (Fin 3) => A.mulVec z.ofLp) ⁻¹' T) := measure_mono hsub
    _ = ENNReal.ofReal |A.det⁻¹| * volume T :=
      Submission.Obl.k4_multilinear_kakeya.matrix_preimage_volume A hdet hT
    _ = ENNReal.ofReal |A.det⁻¹| * (ENNReal.ofReal (2 * K) * volume U) := by
      rw [volume_projectedCylinder U hU r K]
    _ ≤ ENNReal.ofReal (2 * K * q * |Q.det|) * (ENNReal.ofReal (2 * K) * volume U) := by
      gcongr
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * K * q * |Q.det|)]
      congr 2
      ring

end Submission.Obl.k4_uncapped_native_capping.UWE
