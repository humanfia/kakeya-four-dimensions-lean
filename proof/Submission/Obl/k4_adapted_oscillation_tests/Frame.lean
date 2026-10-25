import Mathlib

/-!
# A maximal-volume frame in the unit body of a seminorm

For a continuous seminorm `V ≥ ‖·‖` on `EuclideanSpace ℝ (Fin n)`, the unit body
`K = {v | V v ≤ 1}` is compact. A frame `b : Fin n → K` maximizing `|det|` has nonzero
determinant, and by Cramer's rule every `v ∈ K` has coordinates of absolute value at most `1`
in it. Hence `K` lies in the image of the cube `[-1,1]^n` under the frame map, and
`volume K ≤ 2^n |det|`.
-/

namespace Submission.Obl.k4_adapted_oscillation_tests

open MeasureTheory Metric Set

variable {n : ℕ}

/-- The matrix whose `i`-th row lists the coordinates of `b i`. -/
def rowMat (b : Fin n → EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => b i j

/-- The linear map sending the `i`-th standard basis vector to `b i`. -/
noncomputable def frameMap (b : Fin n → EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.constrL b

theorem frameMap_apply (b : Fin n → EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n)) :
    frameMap b x = ∑ i, x i • b i := by
  simp [frameMap, Module.Basis.constrL_apply]

theorem frameMap_single (b : Fin n → EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    frameMap b (EuclideanSpace.single i 1) = b i := by
  rw [frameMap_apply]
  simp [PiLp.single_apply]

theorem det_frameMap (b : Fin n → EuclideanSpace ℝ (Fin n)) :
    (frameMap b).det = (rowMat b).det := by
  rw [ContinuousLinearMap.det,
    ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis, ← Matrix.det_transpose]
  congr 1
  ext i j
  simp [LinearMap.toMatrix_apply, rowMat, frameMap_single]

theorem rowMat_update (b : Fin n → EuclideanSpace ℝ (Fin n)) (j : Fin n)
    (v : EuclideanSpace ℝ (Fin n)) :
    rowMat (Function.update b j v) = (rowMat b).updateRow j (fun k => v k) := by
  ext i k
  by_cases h : i = j
  · subst h
    simp [rowMat, Matrix.updateRow_apply]
  · simp [rowMat, Matrix.updateRow_apply, h]

/-- Cramer's rule: replacing `b j` by `∑ i, t i • b i` multiplies the determinant by `t j`. -/
theorem det_rowMat_update_sum (b : Fin n → EuclideanSpace ℝ (Fin n)) (j : Fin n)
    (t : Fin n → ℝ) :
    (rowMat (Function.update b j (∑ i, t i • b i))).det = t j * (rowMat b).det := by
  rw [rowMat_update]
  have h : (fun k => (∑ i, t i • b i) k) = ∑ i, t i • (rowMat b) i := by
    ext k
    simp [rowMat, Finset.sum_apply]
  rw [h, Matrix.det_updateRow_sum, smul_eq_mul]

/-- With an invertible frame, every vector is a combination of the frame. -/
theorem sum_coeff_eq (b : Fin n → EuclideanSpace ℝ (Fin n)) (hb : (rowMat b).det ≠ 0)
    (v : EuclideanSpace ℝ (Fin n)) :
    ∑ i, (Matrix.vecMul (WithLp.ofLp v) (rowMat b)⁻¹) i • b i = v := by
  have h1 : Matrix.vecMul (Matrix.vecMul (WithLp.ofLp v) (rowMat b)⁻¹) (rowMat b) =
      WithLp.ofLp v := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hb),
      Matrix.vecMul_one]
  ext k
  have h2 : ∑ i, (Matrix.vecMul (WithLp.ofLp v) (rowMat b)⁻¹) i * (b i) k = v k :=
    congrFun h1 k
  rw [← h2]
  simp [Finset.sum_apply]

/-- The unit body of a continuous seminorm dominating the norm is compact. -/
theorem isCompact_unitBody (V : Seminorm ℝ (EuclideanSpace ℝ (Fin n))) (hV : Continuous V)
    (hdom : ∀ v, ‖v‖ ≤ V v) : IsCompact {v : EuclideanSpace ℝ (Fin n) | V v ≤ 1} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_le hV continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin n))) (r := 1)).subset ?_
    intro v hv
    simpa using (hdom v).trans hv

/-- A maximal-determinant frame in the unit body: every `v` with `V v ≤ 1` has coordinates
of absolute value at most `1` in it. -/
theorem exists_frame (V : Seminorm ℝ (EuclideanSpace ℝ (Fin n))) (hV : Continuous V)
    (hdom : ∀ v, ‖v‖ ≤ V v) :
    ∃ b : Fin n → EuclideanSpace ℝ (Fin n), (∀ i, V (b i) ≤ 1) ∧ (rowMat b).det ≠ 0 ∧
      ∀ v, V v ≤ 1 → ∃ t : Fin n → ℝ, (∀ i, |t i| ≤ 1) ∧ v = ∑ i, t i • b i := by
  set K := {v : EuclideanSpace ℝ (Fin n) | V v ≤ 1} with hK
  have hPc : IsCompact (Set.univ.pi fun _ : Fin n => K) :=
    isCompact_univ_pi fun _ => isCompact_unitBody V hV hdom
  have hne : (Set.univ.pi fun _ : Fin n => K).Nonempty :=
    ⟨fun _ => 0, fun i _ => by simp [K]⟩
  have hcont : Continuous fun b : Fin n → EuclideanSpace ℝ (Fin n) => |(rowMat b).det| := by
    refine continuous_abs.comp (Continuous.matrix_det ?_)
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (PiLp.continuous_apply 2 _ j).comp (continuous_apply i)
  obtain ⟨b, hbK, hmax⟩ := hPc.exists_isMaxOn hne hcont.continuousOn
  rw [isMaxOn_iff] at hmax
  -- the scaled standard basis lies in `K` and has nonzero determinant
  set b0 : Fin n → EuclideanSpace ℝ (Fin n) :=
    fun i => (V (EuclideanSpace.single i 1))⁻¹ • EuclideanSpace.single i 1 with hb0
  have hVpos : ∀ i : Fin n, 0 < V (EuclideanSpace.single i (1 : ℝ)) := fun i =>
    lt_of_lt_of_le (by simp) (hdom _)
  have hb0K : b0 ∈ Set.univ.pi fun _ : Fin n => K := by
    intro i _
    simp only [K, mem_ofPred_eq, b0, map_smul_eq_mul, Real.norm_eq_abs]
    rw [abs_of_pos (inv_pos.mpr (hVpos i)), inv_mul_cancel₀ (hVpos i).ne']
  have hb0det : (rowMat b0).det ≠ 0 := by
    have : rowMat b0 = Matrix.diagonal fun i => (V (EuclideanSpace.single i 1))⁻¹ := by
      ext i k
      by_cases h : i = k
      · subst h
        simp [rowMat, b0, PiLp.single_apply]
      · simp [rowMat, b0, PiLp.single_apply, h, Ne.symm h]
    rw [this, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => inv_ne_zero (hVpos i).ne'
  have hbdet : (rowMat b).det ≠ 0 := by
    intro h
    have h0 := hmax b0 hb0K
    rw [h, abs_zero] at h0
    exact hb0det (abs_nonpos_iff.mp h0)
  refine ⟨b, fun i => hbK i trivial, hbdet, fun v hv => ?_⟩
  set t := Matrix.vecMul (WithLp.ofLp v) (rowMat b)⁻¹ with ht
  have hvt : v = ∑ i, t i • b i := (sum_coeff_eq b hbdet v).symm
  refine ⟨t, fun j => ?_, hvt⟩
  have hupd : Function.update b j v ∈ Set.univ.pi fun _ : Fin n => K := by
    intro i _
    by_cases h : i = j
    · subst h
      simpa [K] using hv
    · simpa [Function.update_of_ne h] using hbK i trivial
  have h1 := hmax _ hupd
  have key : (rowMat (Function.update b j v)).det = t j * (rowMat b).det := by
    have := det_rowMat_update_sum b j t
    rwa [← hvt] at this
  simp only [key, abs_mul] at h1
  have hpos : 0 < |(rowMat b).det| := abs_pos.mpr hbdet
  nlinarith

/-- The volume of a coordinate box of `EuclideanSpace ℝ (Fin n)`. -/
theorem volume_box (a b : Fin n → ℝ) :
    volume (WithLp.toLp 2 '' Set.Icc a b : Set (EuclideanSpace ℝ (Fin n))) =
      ∏ i, ENNReal.ofReal (b i - a i) := by
  have himg : (WithLp.toLp 2 '' Set.Icc a b : Set (EuclideanSpace ℝ (Fin n))) =
      WithLp.ofLp ⁻¹' Set.Icc a b := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨WithLp.ofLp x, hx, by simp⟩
  rw [himg, (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
    measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi]

/-- Volume of the image of a set under an affine map `x ↦ p + L x`. -/
theorem volume_affine_image (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (p : EuclideanSpace ℝ (Fin n)) (s : Set (EuclideanSpace ℝ (Fin n))) :
    volume ((fun x => p + L x) '' s) = ENNReal.ofReal |L.det| * volume s := by
  have : (fun x => p + L x) '' s = (fun y => p + y) '' (L '' s) := by
    rw [Set.image_image]
  rw [this, Set.image_add_left, measure_preimage_add]
  exact Measure.addHaar_image_linearMap volume (L : _ →ₗ[ℝ] _) s

/-- The unit body of `V` has finite positive volume. -/
theorem volume_unitBody_pos (V : Seminorm ℝ (EuclideanSpace ℝ (Fin n))) (hV : Continuous V) :
    0 < volume {v : EuclideanSpace ℝ (Fin n) | V v ≤ 1} := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (Seminorm.ball_mem_nhds hV one_pos)
  refine lt_of_lt_of_le (Metric.measure_ball_pos volume 0 hε) (measure_mono ?_)
  intro v hv
  have := hball hv
  rw [Seminorm.mem_ball, sub_zero] at this
  exact this.le

theorem volume_unitBody_lt_top (V : Seminorm ℝ (EuclideanSpace ℝ (Fin n)))
    (hdom : ∀ v, ‖v‖ ≤ V v) :
    volume {v : EuclideanSpace ℝ (Fin n) | V v ≤ 1} < ⊤ := by
  refine lt_of_le_of_lt (measure_mono ?_) (measure_closedBall_lt_top (x := 0) (r := 1))
  intro v hv
  simpa using (hdom v).trans hv

/-- The frame map of the maximal frame: it sends the standard basis into the unit body,
has nonzero determinant, and `volume K ≤ 2^n |det|`. -/
theorem exists_frameMap (V : Seminorm ℝ (EuclideanSpace ℝ (Fin n))) (hV : Continuous V)
    (hdom : ∀ v, ‖v‖ ≤ V v) :
    ∃ T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
      (∀ i, V (T (EuclideanSpace.single i 1)) ≤ 1) ∧ T.det ≠ 0 ∧
      volume {v : EuclideanSpace ℝ (Fin n) | V v ≤ 1} ≤ 2 ^ n * ENNReal.ofReal |T.det| := by
  obtain ⟨b, hbV, hbdet, hcoord⟩ := exists_frame V hV hdom
  refine ⟨frameMap b, fun i => by simpa [frameMap_single] using hbV i, ?_, ?_⟩
  · rwa [det_frameMap]
  · have hsub : {v : EuclideanSpace ℝ (Fin n) | V v ≤ 1} ⊆
        (fun x => 0 + frameMap b x) '' (WithLp.toLp 2 '' Set.Icc (-1 : Fin n → ℝ) 1) := by
      intro v hv
      obtain ⟨t, ht, rfl⟩ := hcoord v hv
      refine ⟨WithLp.toLp 2 t, ⟨t, ⟨fun i => (abs_le.mp (ht i)).1, fun i => (abs_le.mp (ht i)).2⟩,
        rfl⟩, ?_⟩
      simp [frameMap_apply]
    refine (measure_mono hsub).trans (le_of_eq ?_)
    rw [volume_affine_image, volume_box]
    simp only [Pi.one_apply, Pi.neg_apply, sub_neg_eq_add]
    norm_num
    ring

end Submission.Obl.k4_adapted_oscillation_tests
