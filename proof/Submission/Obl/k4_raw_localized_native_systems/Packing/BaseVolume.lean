/- Adapted from this LOT tree, o197, session x0690, Packing/BaseVolume.lean,
   branch snapshot 9f1b6476; preserving original attributions below. -/
import Submission.Obl.k4_raw_localized_native_systems.NativeAxes
import Submission.Obl.k4_quadratic_slope_volume.SpatialVolume
import Submission.Lib.K4Homogenization.NativeDensityBounds

namespace Submission.Obl.k4_raw_localized_native_systems.Packing

open MeasureTheory Set
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

def basePlane (z : EuclideanSpace ℝ (Fin 3)) : Plane := WithLp.toLp 2 ![z 1, z 2]

def affineBaseTube (l r K : ℝ) (c u : Plane) (Q : Matrix (Fin 2) (Fin 2) ℝ) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  {z | z 0 ∈ Icc l r ∧ ‖Matrix.toEuclideanLin Q⁻¹ (basePlane z - c - z 0 • u)‖ ≤ K}

theorem measurableSet_affineBaseTube (l r K : ℝ) (c u : Plane)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) : MeasurableSet (affineBaseTube l r K c u Q) := by
  have ht : Measurable (fun z : EuclideanSpace ℝ (Fin 3) => z 0) := by fun_prop
  have hc : Continuous (fun z : EuclideanSpace ℝ (Fin 3) => basePlane z - c - z 0 • u) := by
    unfold basePlane
    fun_prop
  have hlin : Continuous (Matrix.toEuclideanLin Q⁻¹) := LinearMap.continuous_of_finiteDimensional _
  exact (measurableSet_Icc.preimage ht).inter
    (measurableSet_le (hlin.comp hc).norm.measurable measurable_const)

/-- The spatial ellipse area is integrated over the actual time interval.
This generalizes the dyadic chart-base computation in `Native.CrossingVolume`. -/
theorem volume_affineBaseTube {l r K : ℝ} {c u : Plane}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} (hK : 0 ≤ K) (hQ : Q.det ≠ 0) :
    volume (affineBaseTube l r K c u Q) =
      ENNReal.ofReal (Real.pi * K ^ 2 * |Q.det| * (r - l)) := by
  let e := Submission.Lib.K4Homogenization.nativeBaseCoordinates
  have he := Submission.Lib.K4Homogenization.measurePreserving_nativeBaseCoordinates
  rw [← he.measure_preimage_emb e.measurableEmbedding]
  rw [Measure.prod_apply ((measurableSet_affineBaseTube l r K c u Q).preimage e.measurable)]
  have hfiber (t : ℝ) : volume (Prod.mk t ⁻¹' (e ⁻¹' affineBaseTube l r K c u Q)) =
      (Icc l r).indicator (fun _ => ENNReal.ofReal (Real.pi * K ^ 2 * |Q.det|)) t := by
    by_cases ht : t ∈ Icc l r
    · rw [indicator_of_mem ht]
      have hs : Prod.mk t ⁻¹' (e ⁻¹' affineBaseTube l r K c u Q) =
          {z : Fin 2 → ℝ | ‖Matrix.toEuclideanLin Q⁻¹
            (WithLp.toLp 2 (fun i => z i - c i - t * u i))‖ ≤ K} := by
        ext z
        have hv : WithLp.toLp 2 ![z 0, z 1] - c - t • u =
            WithLp.toLp 2 (fun i : Fin 2 => z i - c i - t * u i) := by
          ext i
          fin_cases i <;> simp
        change (t ∈ Icc l r ∧
          ‖Matrix.toEuclideanLin Q⁻¹ (WithLp.toLp 2 ![z 0, z 1] - c - t • u)‖ ≤ K) ↔ _
        rw [and_iff_right ht, hv]
        rfl
      rw [hs]
      exact k4_quadratic_slope_volume.volume_coordinate_ellipse Q hQ c u t K hK
    · rw [indicator_of_notMem ht]
      have hs : Prod.mk t ⁻¹' (e ⁻¹' affineBaseTube l r K c u Q) = ∅ := by
        ext z
        simp only [mem_preimage, mem_empty_iff_false, iff_false]
        exact fun hz => ht hz.1
      rw [hs, measure_empty]
  simp_rw [hfiber]
  rw [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc,
    ← ENNReal.ofReal_mul (by positivity)]

def scalarWindowTube (n : Plane) (t y α β rt ry rn : ℝ) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  affineBaseTube (t - rt) (t + rt) 2 (y • tangentOfNormal n + α • n) (β • n)
    (Submission.Lib.K4FinitePlankAtlases.plankFrame ry rn (tangentOfNormal n) n)

theorem measurableSet_scalarWindowTube (n : Plane) (t y α β rt ry rn : ℝ) :
    MeasurableSet (scalarWindowTube n t y α β rt ry rn) :=
  measurableSet_affineBaseTube _ _ _ _ _ _

theorem volume_scalarWindowTube {n : Plane} (hn : ‖n‖ = 1)
    {t y α β rt ry rn : ℝ} (hry : 0 < ry) (hrn : 0 < rn) :
    volume (scalarWindowTube n t y α β rt ry rn) =
      ENNReal.ofReal (8 * Real.pi * rt * ry * rn) := by
  have he : ‖tangentOfNormal n‖ = 1 := (tangentOfNormal_norm n).trans hn
  have hdet := Submission.Lib.K4FinitePlankAtlases.plankFrame_abs_det hry hrn
    he hn (tangentOfNormal_orthogonal n)
  have hQ : (Submission.Lib.K4FinitePlankAtlases.plankFrame ry rn
      (tangentOfNormal n) n).det ≠ 0 := by
    apply abs_pos.mp
    rw [hdet]
    positivity
  rw [scalarWindowTube, volume_affineBaseTube (by norm_num) hQ, hdet]
  congr 1
  ring

theorem mem_scalarWindowTube {n : Plane} (hn : ‖n‖ = 1)
    {t y α β rt ry rn : ℝ} (hry : 0 < ry) (hrn : 0 < rn)
    {z : EuclideanSpace ℝ (Fin 3)} (ht : |z 0 - t| ≤ rt)
    (hy : |inner ℝ (basePlane z) (tangentOfNormal n) - y| ≤ ry)
    (hnormal : |inner ℝ (basePlane z - α • n - z 0 • (β • n)) n| ≤ rn) :
    z ∈ scalarWindowTube n t y α β rt ry rn := by
  have he : ‖tangentOfNormal n‖ = 1 := (tangentOfNormal_norm n).trans hn
  have hen := tangentOfNormal_orthogonal n
  have hne : inner ℝ n (tangentOfNormal n) = 0 := by rwa [real_inner_comm]
  have hee : inner ℝ (tangentOfNormal n) (tangentOfNormal n) = 1 := by
    rw [real_inner_self_eq_norm_sq, he]; norm_num
  refine ⟨?_, Submission.Lib.K4FinitePlankAtlases.plankFrame_fit hry hrn he hn hen ?_ ?_⟩
  · exact ⟨by linarith [(abs_le.mp ht).1], by linarith [(abs_le.mp ht).2]⟩
  · simpa only [inner_sub_left, inner_add_left, real_inner_smul_left, hee, hne,
      mul_one, mul_zero, sub_zero, add_zero] using hy
  · simpa only [inner_sub_left, inner_add_left, real_inner_smul_left, hen,
      mul_zero, zero_add] using hnormal

end
end Submission.Obl.k4_raw_localized_native_systems.Packing
