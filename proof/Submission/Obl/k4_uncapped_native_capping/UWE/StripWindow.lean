/-
Adapted from this LOT tree o198, session x0693, commit b5c1b640df5e526ffc014739d6614359923ec044,
Submission/Obl/k4_balanced_native_packet_transport/UWE/StripWindow.lean. Existing source attributions below are retained.
-/
/-
Adapted from this LOT tree, o120, session x0649, commit 99e461c8faeab846d12253887b2a587a38b5aa0e,
Submission/Obl/k4_unbounded_width_exclusion/StripWindow.lean (namespace Submission.Obl.k4_unbounded_width_exclusion renamed to
Submission.Obl.k4_uncapped_native_capping.UWE).
-/
import Submission.Obl.k4_uncapped_native_capping.UWE.Interface
import Submission.Obl.k4_scalar_angular_pair_agreement.CapIntegration
import Submission.Lib.K4Homogenization.NativeDensityBounds
import Submission.Lib.K4ContinuousPlanks.VelocityCap
import Submission.Obl.k4_plank_tube_realization.ConvexVolume

noncomputable section

namespace Submission.Obl.k4_uncapped_native_capping.UWE

open MeasureTheory Set

/-- The exact base window occupied by a bounded trajectory in an extrapolated
affine normal strip throughout the unit interval. -/
def originalStripWindow (n : EuclideanSpace ℝ (Fin 2)) (b c K g : ℝ) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  {z | z 0 ∈ Icc (0 : ℝ) 1 ∧
    ‖(WithLp.toLp 2 ![z 1, z 2] : EuclideanSpace ℝ (Fin 2))‖ ≤ K ∧
    |inner ℝ n (WithLp.toLp 2 ![z 1, z 2]) - b - z 0 * c| ≤ K * g}

theorem measurableSet_originalStripWindow
    (n : EuclideanSpace ℝ (Fin 2)) (b c K g : ℝ) :
    MeasurableSet (originalStripWindow n b c K g) := by
  unfold originalStripWindow
  measurability

/-- Extrapolating the narrow strip costs its actual width, with no inverse
minor-axis factor and no dependence on its affine center parameters. -/
theorem volume_originalStripWindow
    (n : EuclideanSpace ℝ (Fin 2)) (hn : ‖n‖ = 1)
    (b c : ℝ) {K g : ℝ} (hK : 0 ≤ K) (hg : 0 ≤ g) :
    volume (originalStripWindow n b c K g) ≤ ENNReal.ofReal (4 * K ^ 2 * g) := by
  let e := Submission.Obl.k4_plank_tube_realization.ConvexGeometry.rotate n
  have he : ‖e‖ = 1 := by
    exact (Submission.Obl.k4_plank_tube_realization.ConvexGeometry.rotate_norm n).trans hn
  have hen : inner ℝ e n = 0 :=
    Submission.Obl.k4_plank_tube_realization.ConvexGeometry.rotate_orthogonal n
  have hne : inner ℝ n e = 0 := by rw [real_inner_comm]; exact hen
  let U : Set (ℝ × (Fin 2 → ℝ)) :=
    Submission.Lib.K4Homogenization.nativeBaseCoordinates ⁻¹' originalStripWindow n b c K g
  have hU : MeasurableSet U := (measurableSet_originalStripWindow n b c K g).preimage
    Submission.Lib.K4Homogenization.nativeBaseCoordinates.measurable
  have hvol : (volume.prod (volume : Measure (Fin 2 → ℝ))) U =
      volume (originalStripWindow n b c K g) := by
    exact Submission.Lib.K4Homogenization.measurePreserving_nativeBaseCoordinates.measure_preimage
      (measurableSet_originalStripWindow n b c K g).nullMeasurableSet
  rw [← hvol]
  have hbound : (volume.prod (volume : Measure (Fin 2 → ℝ))) U ≤
      ENNReal.ofReal (4 * K ^ 2 * g) * volume (Icc (0 : ℝ) 1) := by
    apply Submission.Obl.k4_scalar_angular_pair_agreement.prod_mass_le_fiber_bound
      volume volume (Icc (0 : ℝ) 1) U (ENNReal.ofReal (4 * K ^ 2 * g)) hU
    · intro p hp
      exact hp.1
    · intro t ht
      let R : Set (EuclideanSpace ℝ (Fin 2)) :=
        {z | |inner ℝ (z - (b + t * c) • n) e| ≤ K ∧
          |inner ℝ (z - (b + t * c) • n) n| ≤ K * g}
      have hR : MeasurableSet R := by unfold R; measurability
      calc
        volume {z : Fin 2 → ℝ | (t, z) ∈ U} ≤
            volume ((WithLp.toLp 2) ⁻¹' R) := by
          apply measure_mono
          intro z hz
          have hzvec : (![z 0, z 1] : Fin 2 → ℝ) = z := by ext i; fin_cases i <;> rfl
          have hz' : t ∈ Icc (0 : ℝ) 1 ∧
              ‖(WithLp.toLp 2 z : EuclideanSpace ℝ (Fin 2))‖ ≤ K ∧
              |inner ℝ n (WithLp.toLp 2 z) - b - t * c| ≤ K * g := by
            simpa [U, originalStripWindow,
              Submission.Lib.K4Homogenization.nativeBaseCoordinates_apply, hzvec] using hz
          change |inner ℝ (WithLp.toLp 2 z - (b + t * c) • n) e| ≤ K ∧
            |inner ℝ (WithLp.toLp 2 z - (b + t * c) • n) n| ≤ K * g
          constructor
          · rw [inner_sub_left, inner_smul_left, hne, mul_zero, sub_zero]
            calc
              _ ≤ ‖(WithLp.toLp 2 z : EuclideanSpace ℝ (Fin 2))‖ * ‖e‖ := abs_real_inner_le_norm _ _
              _ ≤ K := by rw [he, mul_one]; exact hz'.2.1
          · simpa [inner_sub_left, inner_smul_left, hn, real_inner_comm,
              sub_add_eq_sub_sub] using hz'.2.2
        _ = volume R :=
          (PiLp.volume_preserving_toLp (Fin 2)).measure_preimage hR.nullMeasurableSet
        _ = ENNReal.ofReal (4 * K ^ 2 * g) := by
          rw [Submission.Lib.K4ContinuousPlanks.volume_planar_rectangle
            ((b + t * c) • n) e n he hn hen hK (mul_nonneg hK hg)]
          congr 1
          ring
  simpa using hbound

end Submission.Obl.k4_uncapped_native_capping.UWE
