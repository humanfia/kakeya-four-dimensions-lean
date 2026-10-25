/- Adapted from this LOT tree o222, session x0774, commit 1823dd94,
   Submission/Obl/k4_projected_parent_contact_reduction/ParentNativePartition.lean. -/
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.ParentZoom
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.RootMeshTransport

/-! Native signal partitions in an affine parent chart. -/

namespace Submission.Obl.k4_general_parent_projected_layers

open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Lib.K4AffineMeshCaps

open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_stable_native_signal_oscillation

noncomputable section

theorem RootMeshCap.mono {μ : Measure NativePoint} {C H delta : ℝ}
    (hcap : RootMeshCap μ C delta) (hCH : C ≤ H) (hd : 0 ≤ delta) :
    RootMeshCap μ H delta := by
  intro q
  exact (hcap q).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hCH (pow_nonneg hd 3)))

/-- The loss and Lipschitz term depend on parent filling; the Taylor error
retains the original native constant. No polynomial coefficient bound is used. -/
theorem finite_mesh_parent_signal_partition (A : ℕ) :
    ∃ J C : ℕ, 1 ≤ C ∧ ∀ K H a delta sigma C₀ : ℝ,
      2 ≤ K → K ^ 16 ≤ H → 0 < a → a ≤ 1 →
      0 < delta → 0 < sigma → sigma ≤ (H ^ J)⁻¹ → 0 ≤ C₀ →
      ∀ Z : Zoom, Z.Ok → Z.a = 1 →
        (∀ i, (∑ j, |Z.baseMatrix i j| * delta) ≤ sigma) →
        27 * C₀ * |Z.baseMatrix.det|⁻¹ ≤ H →
      ∀ P S : MvPolynomial (Fin 4) ℝ, P.totalDegree ≤ 2 → S.totalDegree ≤ 2 →
      ∀ μ : Measure NativePoint, IsProbabilityMeasure μ →
        (∀ᵐ p ∂μ, rootBaseCoordinates (Z.nativePoint p) ∈
          Icc (fun _ => (1 : ℝ) / 8) (fun _ => (1 : ℝ) / 4)) →
        RootMeshCap μ C₀ delta → (∀ᵐ p ∂μ, p ∈ goodSet K a P S) →
        ∃ E : Fin 2 → Set NativePoint,
          (∀ i, MeasurableSet (E i)) ∧ (∀ i j, i ≠ j → Disjoint (E i) (E j)) ∧
          μ (⋃ i, E i)ᶜ ≤ ENNReal.ofReal ((H ^ A)⁻¹) ∧
          ∀ i p, p ∈ E i → ∀ q, q ∈ E i →
            |value S p - value S q| ≤ 2 * K ^ 14 * a +
              H ^ C * ‖nativeBase (Z.nativePoint p) - nativeBase (Z.nativePoint q)‖ := by
  classical
  obtain ⟨J, C, hC, hpartition⟩ := finite_mesh_native_signal_partition A
  refine ⟨J, C, hC, ?_⟩
  intro K H a delta sigma C₀ hK hKH ha ha1 hd hs hsJ hC₀ Z hZ haZ hresolve
    hfill P S hP hS μ hprob hsmall hcap hgood
  have : IsProbabilityMeasure μ := hprob
  let ν := Measure.map Z.nativePoint μ
  have hνprob : IsProbabilityMeasure ν := inferInstance
  have hνsmall : RootBaseSmall ν := by
    exact (ae_map_iff Z.measurable_nativePoint.aemeasurable
      (measurableSet_Icc.preimage measurable_rootBaseCoordinates)).mpr hsmall
  have hνcap : RootMeshCap ν H sigma :=
    RootMeshCap.mono (Z.rootMeshCap_nativePoint hZ hd hs hC₀ hresolve hcap) hfill hs.le
  have hνgood : ∀ᵐ p ∂ν, p ∈ goodSet K a (Z.push P) (Z.push S) := by
    apply (ae_map_iff Z.measurable_nativePoint.aemeasurable
      (measurableSet_goodSet K a (Z.push P) (Z.push S))).mpr
    filter_upwards [hgood, hsmall] with p hp hpsmall
    exact Z.goodSet_nativePoint hZ haZ P S hP hS hp
      ((norm_nativeBase_le_one_of_small hpsmall).trans (by linarith))
  obtain ⟨F, hFm, hFd, hFloss, hFosc⟩ := hpartition K H a sigma hK hKH ha ha1
    hs hsJ (Z.push P) (Z.push S) ((Z.push_degree P).trans hP)
    ((Z.push_degree S).trans hS) ν hνprob hνsmall hνcap hνgood
  let E : Fin 2 → Set NativePoint := fun i => Z.nativePoint ⁻¹' F i
  refine ⟨E, fun i => (hFm i).preimage Z.measurable_nativePoint, ?_, ?_, ?_⟩
  · intro i j hij
    exact (hFd i j hij).preimage Z.nativePoint
  · have hmeas : MeasurableSet (⋃ i, F i)ᶜ := (MeasurableSet.iUnion hFm).compl
    have hmass : μ (⋃ i, E i)ᶜ = ν (⋃ i, F i)ᶜ := by
      rw [Measure.map_apply Z.measurable_nativePoint hmeas]
      simp only [E, preimage_compl, preimage_iUnion]
    rw [hmass]
    exact hFloss
  · intro i p hp q hq
    have h := hFosc i (Z.nativePoint p) hp (Z.nativePoint q) hq
    simpa only [Zoom.value_push_nativePoint Z hZ, haZ, inv_one, one_mul] using h

end

end Submission.Obl.k4_general_parent_projected_layers
