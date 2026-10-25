/- Adapted from this LOT tree o222, session x0774, commit 109e510d,
   Submission/Obl/k4_projected_parent_contact_reduction/NativeSignalMesh.lean.
   Existing source attributions are retained below. Accepted mesh-saturation
   results are imported from Submission.Lib.K4AffineMeshCaps.Saturation. -/
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.RootMeshTransport
import Submission.Obl.k4_stable_native_signal_oscillation.Closure

/-!
Finite-mesh native signal oscillation with separate Taylor and base-filling constants.
The root-lift good-law calculation is adapted from this LOT tree o176,
Submission/Obl/k4_stable_native_signal_oscillation/Closure.lean (accepted).
Pointwise root, derivative, error and pullback lemmas are imported.
-/

namespace Submission.Obl.k4_general_parent_projected_layers.NativeMesh

open Submission.Lib.K4AffineMeshCaps

open MvPolynomial MeasureTheory Set
open Submission.Obl.k4_stable_native_signal_oscillation
open Submission.Obl.k4_quadratic_atlas_normalization

set_option maxHeartbeats 2000000

noncomputable section

/-- Only the Lipschitz constant may depend on the larger base-filling bound H.
The additive native error keeps the original K. -/
theorem finite_mesh_native_signal_partition (A : ℕ) :
    ∃ J C : ℕ, 1 ≤ C ∧ ∀ K H a delta : ℝ,
      2 ≤ K → K ^ 16 ≤ H → 0 < a → a ≤ 1 →
      0 < delta → delta ≤ (H ^ J)⁻¹ →
      ∀ P S : MvPolynomial (Fin 4) ℝ, P.totalDegree ≤ 2 → S.totalDegree ≤ 2 →
      ∀ μ : Measure NativePoint, IsProbabilityMeasure μ →
        RootBaseSmall μ → RootMeshCap μ H delta →
        (∀ᵐ p ∂μ, p ∈ goodSet K a P S) →
        ∃ E : Fin 2 → Set NativePoint,
          (∀ i, MeasurableSet (E i)) ∧ (∀ i j, i ≠ j → Disjoint (E i) (E j)) ∧
          μ (⋃ i, E i)ᶜ ≤ ENNReal.ofReal ((H ^ A)⁻¹) ∧
          ∀ i p, p ∈ E i → ∀ q, q ∈ E i →
            |value S p - value S q| ≤ 2 * K ^ 14 * a + H ^ C * ‖nativeBase p - nativeBase q‖ := by
  classical
  obtain ⟨Jp, N, hJp, hN, hcontrol⟩ := root_polynomial_control_from_mesh
  obtain ⟨Jr, Cr, hCr, hroot⟩ := finite_mesh_exact_root_partition A
  let C := max (N + 1) Cr
  refine ⟨max Jp Jr, C, hCr.trans (le_max_right _ _), ?_⟩
  intro K H a delta hK hKH16 ha ha1 hd hdJ P S hP hS μ hprob hbase hcap hgood
  haveI : IsProbabilityMeasure μ := hprob
  have hK0 : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hKL : K ≤ K ^ 16 := by
    simpa using pow_le_pow_right₀ hK1 (by decide : 1 ≤ 16)
  have hKH : K ≤ H := hKL.trans hKH16
  have hH : 2 ≤ H := hK.trans hKH
  have hH0 : 0 < H := by linarith
  have hH1 : 1 ≤ H := by linarith
  have hK15H : K ^ 15 ≤ H := (pow_le_pow_right₀ hK1 (by decide : 15 ≤ 16)).trans hKH16
  have hdp : delta ≤ (H ^ Jp)⁻¹ := hdJ.trans
    (inv_anti₀ (pow_pos hH0 _) (pow_le_pow_right₀ hH1 (le_max_left _ _)))
  have hdr : delta ≤ (H ^ Jr)⁻¹ := hdJ.trans
    (inv_anti₀ (pow_pos hH0 _) (pow_le_pow_right₀ hH1 (le_max_right _ _)))
  let G := goodSet K a P S
  have hGm : MeasurableSet G := measurableSet_goodSet K a P S
  change ∀ᵐ p ∂μ, p ∈ G at hgood
  by_cases hc : (K ^ 5 * a)⁻¹ ≤ |curvature P 3|
  · let F := centerSignal P S
    have hF2 : F.totalDegree ≤ 2 := (centerSignal_degree P S hP).trans hS
    have hctl := hcontrol H delta hH hd hdp μ hprob hbase hcap
    have hFcontrol := hctl G hgood (fun p hp => hp.1.trans hKH) F
      (hF2.trans (by norm_num)) (K ^ 15) (by positivity) (fun p hp =>
        signal_bound_from_error hK ha1
          (center_signal_error P S hP hS hK ha ha1 hc hp) hp.2.2.2.2.2.1)
    let E : Fin 2 → Set NativePoint := fun i => if i = 0 then G else ∅
    refine ⟨E, ?_, ?_, ?_, ?_⟩
    · intro i
      by_cases hi : i = 0
      · simpa only [E, if_pos hi] using hGm
      · simp only [E, if_neg hi]
        exact MeasurableSet.empty
    · intro i j hij
      by_cases hi : i = 0
      · have hj : j ≠ 0 := fun hj => hij (hi.trans hj.symm)
        simp [E, hi, hj]
      · simp [E, hi]
    · have hUnion : (⋃ i, E i) = G := by
        ext p
        constructor
        · intro hp
          obtain ⟨i, hi⟩ := mem_iUnion.mp hp
          by_cases hzero : i = 0
          · simpa only [E, if_pos hzero] using hi
          · simp only [E, if_neg hzero] at hi
            exact hi.elim
        · intro hp
          exact mem_iUnion.mpr ⟨0, by simpa [E] using hp⟩
      have hzero : μ Gᶜ = 0 := ae_iff.mp hgood
      rw [hUnion, hzero]
      exact bot_le
    · intro i p hp q hq
      by_cases hi : i = 0
      · have hpG : p ∈ G := by simpa only [E, if_pos hi] using hp
        have hqG : q ∈ G := by simpa only [E, if_pos hi] using hq
        have hep := center_signal_error P S hP hS hK ha ha1 hc hpG
        have heq := center_signal_error P S hP hS hK ha ha1 hc hqG
        rw [abs_sub_comm] at hep heq
        have hosc := signal_oscillation_of_graph nativeBase (value S) (baseValue F)
          hep heq (hFcontrol.2 (nativeBase p) (nativeBase q)
            (by linarith [hpG.1]) (by linarith [hqG.1]))
        have hfactor : H ^ N * K ^ 15 ≤ H ^ C := by
          calc
            _ ≤ H ^ N * H := mul_le_mul_of_nonneg_left hK15H (by positivity)
            _ = H ^ (N + 1) := (pow_succ H N).symm
            _ ≤ H ^ C := pow_le_pow_right₀ hH1 (le_max_left _ _)
        exact hosc.trans (add_le_add le_rfl
          (mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)))
      · have hpempty : p ∈ (∅ : Set NativePoint) := by simpa only [E, if_neg hi] using hp
        exact hpempty.elim
  · have hcsmall : |curvature P 3| ≤ (K ^ 5 * a)⁻¹ := le_of_lt (lt_of_not_ge hc)
    let ν := Measure.map (rootLift P) μ
    have hν : IsProbabilityMeasure ν := inferInstance
    have hb : ∀ p, erBase (rootLift P p) = erBase p := nativeBase_rootLift P
    have hνbase : RootBaseSmall ν := hbase.map (rootLift P) (measurable_rootLift P) hb
    have hνcap : RootMeshCap ν H delta := hcap.map (rootLift P) (measurable_rootLift P) hb
    have hνgood : ∀ᵐ p ∂ν, ‖nativeBase p‖ ≤ K ^ 16 ∧ value P p = 0 ∧
        (K ^ 16)⁻¹ ≤ |value (pderiv 3 P) p| ∧ |value (pderiv 3 P) p| ≤ K ^ 16 ∧ |value S p| ≤ K ^ 16 := by
      apply (ae_map_iff (measurable_rootLift P).aemeasurable ?_).mpr
      · filter_upwards [hgood] with p hp
        obtain ⟨hr, hsimple, he⟩ := rootLift_spec P S hP hS hK ha ha1 hcsmall p
          hp.2.1 hp.2.2.1 hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2
        obtain ⟨hdlo, hdhi⟩ := rootLift_derivative_bounds P hP hK ha hcsmall
          hp.2.2.2.2.1 p hp.2.1 hp.2.2.1 hp.2.2.2.1 hr
        have hlower : (K ^ 16)⁻¹ ≤ K⁻¹ / 2 := by
          have h2K : 2 * K ≤ K ^ 16 := by
            calc
              _ ≤ K * K := mul_le_mul_of_nonneg_right hK hK0.le
              _ = K ^ 2 := by ring
              _ ≤ K ^ 16 := pow_le_pow_right₀ hK1 (by decide : 2 ≤ 16)
          calc
            _ ≤ (2 * K)⁻¹ := inv_anti₀ (by positivity) h2K
            _ = K⁻¹ / 2 := by field_simp
        refine ⟨?_, hr, hlower.trans hdlo, hdhi.trans
          (pow_le_pow_right₀ hK1 (by decide : 2 ≤ 16)), ?_⟩
        · rw [nativeBase_rootLift]
          exact hp.1.trans hKL
        · exact (signal_bound_from_error hK ha1 he hp.2.2.2.2.2.1).trans
            (pow_le_pow_right₀ hK1 (by decide : 15 ≤ 16))
      · exact (measurableSet_le measurable_nativeBase.norm measurable_const).inter
          ((measurableSet_eq_fun (continuous_value P).measurable measurable_const).inter
          ((measurableSet_le measurable_const (continuous_value (pderiv 3 P)).abs.measurable).inter
          ((measurableSet_le (continuous_value (pderiv 3 P)).abs.measurable measurable_const).inter
            (measurableSet_le (continuous_value S).abs.measurable measurable_const))))
    have hνgoodH : ∀ᵐ p ∂ν, ‖erBase p‖ ≤ H ∧ eval (fun i => p i) P = 0 ∧
        H⁻¹ ≤ |eval (fun i => p i) (pderiv 3 P)| ∧
        |eval (fun i => p i) (pderiv 3 P)| ≤ H ∧ |eval (fun i => p i) S| ≤ H := by
      filter_upwards [hνgood] with p hp
      exact ⟨hp.1.trans hKH16, hp.2.1,
        (inv_anti₀ (pow_pos hK0 16) hKH16).trans hp.2.2.1,
        hp.2.2.2.1.trans hKH16, hp.2.2.2.2.trans hKH16⟩
    obtain ⟨F, hFm, hFd, hmass, hFl⟩ :=
      hroot H delta hH hd hdr ν hν hνbase hνcap P S hP hS hνgoodH
    obtain ⟨E, hEm, hEd, hEloss, hEosc⟩ := pullback_signal_partition μ (rootLift P)
      (measurable_rootLift P) (nativeBase_rootLift P) S G hGm hgood
      (fun p hp => (rootLift_spec P S hP hS hK ha ha1 hcsmall p
        hp.2.1 hp.2.2.1 hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2).2.2)
      F hFm hFd hFl
    refine ⟨E, hEm, hEd, hEloss.trans hmass, ?_⟩
    intro i p hp q hq
    exact (hEosc i p hp q hq).trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hH1 (le_max_right _ _)) (norm_nonneg _)))

end

end Submission.Obl.k4_general_parent_projected_layers.NativeMesh
