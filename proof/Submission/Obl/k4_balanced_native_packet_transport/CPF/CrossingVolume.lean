/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/CrossingVolume.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
/- Shared from this LOT obligation o105, session x0548, commit 9d59cc18efc1,
   Submission/Obl/k4_critical_path_framework/CrossingVolume.lean. Earlier provenance is retained below. -/
import Submission.Obl.k4_balanced_native_packet_transport.CPF.ChartCrossing
import Submission.Obl.k4_quadratic_slope_volume.SpatialVolume
import Submission.Lib.K4Homogenization.NativeDensityBounds

/-! The crossing count uses observation volume, without the assigned prior.
This distinction is what permits Markov pruning for the original law.
-/

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF

open Set MeasureTheory

def chartBase (κ : ℝ) (T : ℕ) (j : ℝ) (c u : Spatial) (Q : Frame) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  {z | z 0 ∈ Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T) ∧
    ‖Matrix.toEuclideanLin Q⁻¹ (WithLp.toLp 2 ![z 1, z 2] - c - z 0 • u)‖ ≤ κ}

theorem measurableSet_chartBase (κ : ℝ) (T : ℕ) (j : ℝ)
    (c u : Spatial) (Q : Frame) : MeasurableSet (chartBase κ T j c u Q) := by
  have ht : Measurable (fun z : EuclideanSpace ℝ (Fin 3) => z 0) := by fun_prop
  have hc : Continuous (fun z : EuclideanSpace ℝ (Fin 3) =>
      WithLp.toLp 2 ![z 1, z 2] - c - z 0 • u) := by fun_prop
  have hlin : Continuous (Matrix.toEuclideanLin Q⁻¹) :=
    LinearMap.continuous_of_finiteDimensional _
  exact (measurableSet_Icc.preimage ht).inter
    (measurableSet_le (hlin.comp hc).norm.measurable measurable_const)

theorem continuous_hiddenPolynomial_eval (R : Test) (w : ℝ) :
    Continuous (fun z : EuclideanSpace ℝ (Fin 3) => (hiddenPolynomial R z).eval w) := by
  simp_rw [hiddenPolynomial_eval]
  apply R.continuous_eval.comp
  fun_prop

theorem measurableSet_quadraticCrosses (R : Test) (a B κ : ℝ) (m : ℕ) (n : ℤ) :
    MeasurableSet {z : EuclideanSpace ℝ (Fin 3) |
      QuadraticCrosses (hiddenPolynomial R z) a B κ m n} := by
  simp_rw [QuadraticCrosses, ofPred_exists]
  apply MeasurableSet.iUnion
  intro i
  simp_rw [hiddenPolynomial_derivative]
  exact (measurableSet_le (continuous_hiddenPolynomial_eval R _).abs.measurable
    measurable_const).inter (measurableSet_le measurable_const
      (continuous_hiddenPolynomial_eval (MvPolynomial.pderiv 3 R) _).abs.measurable)

theorem measurableSet_chartCrosses_base (κ : ℝ) (T : ℕ) (j a B : ℝ)
    (c u : Spatial) (Q : Frame) (R : Test) (m : ℕ) (n : ℤ) :
    MeasurableSet {z : EuclideanSpace ℝ (Fin 3) |
      ChartCrosses κ T j a B c u Q R m (z, n)} := by
  convert (measurableSet_chartBase κ T j c u Q).inter
    (measurableSet_quadraticCrosses R a B κ m n) using 1
  ext z
  simp [ChartCrosses, chartBase, and_assoc]

theorem measurableSet_chartCrosses (κ : ℝ) (T : ℕ) (j a B : ℝ)
    (c u : Spatial) (Q : Frame) (R : Test) (m : ℕ) :
    MeasurableSet {o : Observation | ChartCrosses κ T j a B c u Q R m o} := by
  have hs : {o : Observation | ChartCrosses κ T j a B c u Q R m o} =
      ⋃ n : ℤ, {z : EuclideanSpace ℝ (Fin 3) |
        ChartCrosses κ T j a B c u Q R m (z, n)} ×ˢ {n} := by
    ext o
    simp only [mem_ofPred_eq, mem_iUnion, mem_prod, mem_singleton_iff]
    constructor
    · intro ho
      exact ⟨o.2, ho, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact hn
  rw [hs]
  exact MeasurableSet.iUnion fun n =>
    (measurableSet_chartCrosses_base κ T j a B c u Q R m n).prod (measurableSet_singleton n)

/-- The base of a chart has volume `pi * kappa^2 * q * |det Q|`. -/
theorem volume_chartBase {κ j : ℝ} {T : ℕ} {c u : Spatial} {Q : Frame}
    (hκ : 0 ≤ κ) (hQ : Matrix.det Q ≠ 0) :
    volume (chartBase κ T j c u Q) =
      ENNReal.ofReal (Real.pi * κ ^ 2 * |Matrix.det Q| / (2 : ℝ) ^ T) := by
  let e := Submission.Lib.K4Homogenization.nativeBaseCoordinates
  have he := Submission.Lib.K4Homogenization.measurePreserving_nativeBaseCoordinates
  rw [← he.measure_preimage_emb e.measurableEmbedding]
  rw [Measure.prod_apply ((measurableSet_chartBase κ T j c u Q).preimage e.measurable)]
  have hfiber (t : ℝ) :
      volume (Prod.mk t ⁻¹' (e ⁻¹' chartBase κ T j c u Q)) =
        (Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T)).indicator
          (fun _ => ENNReal.ofReal (Real.pi * κ ^ 2 * |Matrix.det Q|)) t := by
    by_cases ht : t ∈ Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T)
    · rw [indicator_of_mem ht]
      have hs : Prod.mk t ⁻¹' (e ⁻¹' chartBase κ T j c u Q) =
          {z : Fin 2 → ℝ | ‖Matrix.toEuclideanLin Q⁻¹
            (WithLp.toLp 2 (fun i => z i - c i - t * u i))‖ ≤ κ} := by
        ext z
        have hv : WithLp.toLp 2 ![z 0, z 1] - c - t • u =
            WithLp.toLp 2 (fun i : Fin 2 => z i - c i - t * u i) := by
          ext i
          fin_cases i <;> simp
        change (t ∈ Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T) ∧
          ‖Matrix.toEuclideanLin Q⁻¹ (WithLp.toLp 2 ![z 0, z 1] - c - t • u)‖ ≤ κ) ↔ _
        rw [and_iff_right ht, hv]
        rfl
      rw [hs]
      exact Submission.Obl.k4_quadratic_slope_volume.volume_coordinate_ellipse Q hQ c u t κ hκ
    · rw [indicator_of_notMem ht]
      have hs : Prod.mk t ⁻¹' (e ⁻¹' chartBase κ T j c u Q) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro z hz
        exact ht hz.1
      rw [hs, measure_empty]
  simp_rw [hfiber]
  rw [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  <;> ring

/-- Crossing observation volume is polynomial in the slack times `q * |det Q|`. -/
theorem volume_chartCrosses {κ j a B : ℝ} {T m : ℕ} {c u : Spatial}
    {Q : Frame} {R : Test} (hR : R.totalDegree ≤ 2)
    (ha : 0 < a) (hB : 0 < B) (hκ : 0 < κ) (hQ : Matrix.det Q ≠ 0) :
    (volume.prod Measure.count) {o : Observation | ChartCrosses κ T j a B c u Q R m o} ≤
      ENNReal.ofReal (8 * (1 + 4 * κ ^ 2) * Real.pi * κ ^ 2 *
        |Matrix.det Q| / (2 : ℝ) ^ T) := by
  rw [Measure.prod_apply (measurableSet_chartCrosses κ T j a B c u Q R m)]
  have hfiber (z : EuclideanSpace ℝ (Fin 3)) :
      Measure.count {n : ℤ | ChartCrosses κ T j a B c u Q R m (z, n)} ≤
        (chartBase κ T j c u Q).indicator
          (fun _ => ENNReal.ofReal (8 * (1 + 4 * κ ^ 2))) z := by
    by_cases hz : z ∈ chartBase κ T j c u Q
    · rw [indicator_of_mem hz]
      have h := ChartCrosses.finite_bins hR ha hB hκ z (T := T) (m := m) (j := j)
        (c := c) (u := u) (Q := Q)
      rw [Measure.count_apply_finite _ h.1]
      have hn := ENNReal.ofReal_le_ofReal h.2
      simpa only [Set.ncard_eq_toFinset_card _ h.1, ENNReal.ofReal_natCast] using hn
    · rw [indicator_of_notMem hz]
      have hs : {n : ℤ | ChartCrosses κ T j a B c u Q R m (z, n)} = ∅ := by
        ext n
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        intro hn
        exact hz ⟨hn.1, hn.2.1⟩
      rw [hs, measure_empty]
  calc
    _ ≤ ∫⁻ z, (chartBase κ T j c u Q).indicator
          (fun _ => ENNReal.ofReal (8 * (1 + 4 * κ ^ 2))) z ∂volume :=
      lintegral_mono hfiber
    _ = _ := by
      rw [lintegral_indicator_const (measurableSet_chartBase κ T j c u Q),
        volume_chartBase hκ.le hQ, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

end Submission.Obl.k4_balanced_native_packet_transport.CPF
