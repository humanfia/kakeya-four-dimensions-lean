/-
Adapted from this LOT tree o198, session x0693, commit b5c1b640df5e526ffc014739d6614359923ec044,
Submission/Obl/k4_balanced_native_packet_transport/UWE/ProjectedAngularCap.lean. Existing source attributions below are retained.
-/
/-
Adapted from this LOT tree, o120, session x0649, commit 99e461c8faeab846d12253887b2a587a38b5aa0e,
Submission/Obl/k4_unbounded_width_exclusion/ProjectedAngularCap.lean (namespace Submission.Obl.k4_unbounded_width_exclusion renamed to
Submission.Obl.k4_uncapped_native_capping.UWE).
-/
import Submission.Obl.k4_uncapped_native_capping.UWE.NativeSignalCap
import Submission.Obl.k4_uncapped_native_capping.UWE.NonparallelMass
import Submission.Obl.k4_uncapped_native_capping.UWE.ProjectedAngularBins
import Submission.Obl.k4_uncapped_native_capping.UWE.ProjectedVolume

noncomputable section

namespace Submission.Obl.k4_uncapped_native_capping.UWE

open MeasureTheory Set

/-- The projected angular cap in original packet units. Its gain is the
original terminal joint/pure density ratio; its denominator is integrated at
the native signal depth. No terminal hidden-label count appears. -/
theorem native_signal_band_projected_angular_cap
    (μ ρ : Measure Incidence) (hρ : ρ ≤ μ)
    {N L r B w κ : ℝ} (hN : 1 ≤ N) (hrL : r ≤ L)
    (hB : 0 < B) (hκ : 1 ≤ κ) (data : NativeAngularSample μ N L B w)
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2) (b : ℝ)
    (g : Observation → ENNReal) (hg : Measurable g)
    (hlaw : μ.map (obs B (δ N r)) = (volume.prod Measure.count).withDensity g) (M gain : ENNReal)
    (hnative : ∀ᵐ p ∂ρ, p.2 ∈ Icc (0 : ℝ) 1 ∧ ‖y p.1 p.2‖ ≤ κ ∧
      |MvPolynomial.eval (x p.1 p.2) P - b| ≤ κ * δ N r ∧
      |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) P)| ≤ κ * B ∧
      |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4)
        (MvPolynomial.pderiv (3 : Fin 4) P))| ≤ κ * B ^ 2 / δ N r ∧
      B / κ ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) P)| ∧
      g (obs B (δ N r) p) ≤ M)
    (hangular : ∀ᵐ p ∂ρ, data.jointDensity (obs B (δ N L) p, nativeAngularBin w p) ≤
      gain * data.terminalDensity (obs B (δ N L) p))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.det ≠ 0)
    (e c u : EuclideanSpace ℝ (Fin 2)) (t₀ Z : ℝ)
    {K q : ℝ} (hK : 0 < K) (hq : 0 < q)
    (hfull : q / K ≤ ‖Matrix.toEuclideanLin Q.transpose e‖)
    (U : Set (EuclideanSpace ℝ (Fin 2))) (hU : MeasurableSet U)
    (hframe : ∀ᵐ p ∂ρ, ‖Matrix.toEuclideanLin Q⁻¹ (y p.1 p.2 - c - p.2 • u)‖ ≤ K)
    (hproject : ∀ᵐ p ∂ρ,
      (WithLp.toLp 2 ![(p.2 - t₀) / q, (inner ℝ e (y p.1 p.2) - Z) / q] :
        EuclideanSpace ℝ (Fin 2)) ∈ U)
    (n : EuclideanSpace ℝ (Fin 2)) (he : ‖e‖ = 1) (hn : ‖n‖ = 1) (hen : inner ℝ e n = 0)
    (β : ℝ) {K₀ g₀ a : ℝ} (hK₀ : 1 ≤ K₀) (hg₀ : 0 ≤ g₀) (hg₀a : g₀ ≤ a)
    (ha : 0 < a) (haw : a ≤ w) (j : ℤ)
    (hvelocity : ∀ᵐ p ∂ρ, |inner ℝ n (v p.1) - β| ≤ K₀ * g₀ ∧ ⌊inner ℝ e (v p.1) / a⌋ = j) :
    ρ univ ≤ gain * ENNReal.ofReal ((8 * K₀ + 2) ^ 2) * M * ENNReal.ofReal (64 * κ ^ 2) *
      ENNReal.ofReal (4 * K ^ 2 * q * |Q.det|) * volume U := by
  classical
  obtain ⟨V, hV, hVmem⟩ := tangent_velocity_bins e n he hn hen β hK₀ hg₀ hg₀a ha haw j
  have hVcard : (V.card : ENNReal) ≤ ENNReal.ofReal ((8 * K₀ + 2) ^ 2) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hV
  let π : Observation → Observation := Submission.Lib.K4Homogenization.coarsenObservation N r L
  have hπ : Measurable π := Submission.Lib.K4Homogenization.measurable_coarsenObservation N r L
  have hfac (p : Incidence) : π (obs B (δ N L) p) = obs B (δ N r) p := by
    apply Prod.ext
    · rfl
    · have h := Submission.Lib.K4Homogenization.observation_bin_coarsen hN hrL (B * x p.1 p.2 3)
      simpa [π, obs, δ, Submission.Lib.K4Homogenization.coarsenObservation,
        Submission.Lib.K4Homogenization.observationWidth,
        Submission.Lib.K4Homogenization.observationDepth] using h.symm
  have hcoarse : μ.map (π ∘ obs B (δ N L)) = (volume.prod Measure.count).withDensity g := by
    rw [show π ∘ obs B (δ N L) = obs B (δ N r) from funext hfac]
    exact hlaw
  let S : Set (EuclideanSpace ℝ (Fin 3)) := {z |
    ‖Matrix.toEuclideanLin Q⁻¹ (WithLp.toLp 2 ![z 1, z 2] - c - z 0 • u)‖ ≤ K ∧
    (WithLp.toLp 2 ![(z 0 - t₀) / q,
      (inner ℝ e (WithLp.toLp 2 ![z 1, z 2]) - Z) / q] : EuclideanSpace ℝ (Fin 2)) ∈ U}
  have hS : MeasurableSet S := by
    have hf : Measurable (fun z : EuclideanSpace ℝ (Fin 3) =>
      ‖Matrix.toEuclideanLin Q⁻¹ (WithLp.toLp 2 ![z 1, z 2] - c - z 0 • u)‖) := by fun_prop
    have hpr : Measurable (fun z : EuclideanSpace ℝ (Fin 3) =>
      (WithLp.toLp 2 ![(z 0 - t₀) / q,
        (inner ℝ e (WithLp.toLp 2 ![z 1, z 2]) - Z) / q] : EuclideanSpace ℝ (Fin 2))) := by fun_prop
    exact (measurableSet_le hf measurable_const).inter (hU.preimage hpr)
  have ha' : 0 < δ N r := by unfold δ; positivity
  have hmass : ρ univ ≤ gain * ENNReal.ofReal ((8 * K₀ + 2) ^ 2) * M *
      ENNReal.ofReal (64 * κ ^ 2) * volume S := by
    apply angular_list_coarse_window_mass_le μ ρ hρ (volume.prod Measure.count)
      (obs B (δ N L)) (by unfold obs x; fun_prop) (nativeAngularBin w) (measurable_nativeAngularBin w)
      data.terminalDensity data.measurable_terminal data.jointDensity data.measurable_joint
      data.terminal_law data.joint_law volume π hπ g hg hcoarse
      (nativeSignalCrossing κ B (δ N r) P b) (measurableSet_nativeSignalCrossing _ _ _ _ _)
      S hS gain (ENNReal.ofReal ((8 * K₀ + 2) ^ 2)) M (ENNReal.ofReal (64 * κ ^ 2))
      (nativeSignalCrossing_count hκ hB ha' P hP b) (fun _ => V)
      (fun v => by by_cases hv : v ∈ V <;> simp [hv]) (fun _ => hVcard)
    filter_upwards [hnative, hangular, hframe, hproject, hvelocity] with p hp hpa hpf hpr hpv
    obtain ⟨ht, hy, hv, hd, hdd, hfl, hgm⟩ := hp
    rw [hfac]
    refine ⟨?_, obs_mem_nativeSignalCrossing hκ hB ha' P hP b p ht hy hv hd hdd hfl,
      hgm, hVmem (v p.1) hpv.1 hpv.2, hpa⟩
    change ‖Matrix.toEuclideanLin Q⁻¹ (y p.1 p.2 - c - p.2 • u)‖ ≤ K ∧
      (WithLp.toLp 2 ![(p.2 - t₀) / q, (inner ℝ e (y p.1 p.2) - Z) / q] :
        EuclideanSpace ℝ (Fin 2)) ∈ U
    exact ⟨hpf, hpr⟩
  calc
    _ ≤ gain * ENNReal.ofReal ((8 * K₀ + 2) ^ 2) * M * ENNReal.ofReal (64 * κ ^ 2) * volume S := hmass
    _ ≤ gain * ENNReal.ofReal ((8 * K₀ + 2) ^ 2) * M * ENNReal.ofReal (64 * κ ^ 2) *
        (ENNReal.ofReal (4 * K ^ 2 * q * |Q.det|) * volume U) := by
      gcongr
      exact volume_packet_projected_base Q hQ e c u t₀ Z hK hq hfull U hU
    _ = _ := by ring

end Submission.Obl.k4_uncapped_native_capping.UWE
