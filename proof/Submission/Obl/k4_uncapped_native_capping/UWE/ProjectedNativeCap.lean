/-
Adapted from this LOT tree o198, session x0693, commit b5c1b640df5e526ffc014739d6614359923ec044,
Submission/Obl/k4_balanced_native_packet_transport/UWE/ProjectedNativeCap.lean. Existing source attributions below are retained.
-/
/-
Adapted from this LOT tree, o120, session x0649, commit 99e461c8faeab846d12253887b2a587a38b5aa0e,
Submission/Obl/k4_unbounded_width_exclusion/ProjectedNativeCap.lean (namespace Submission.Obl.k4_unbounded_width_exclusion renamed to
Submission.Obl.k4_uncapped_native_capping.UWE).
-/
import Submission.Obl.k4_uncapped_native_capping.UWE.NativeSignalCap
import Submission.Obl.k4_uncapped_native_capping.UWE.ProjectedVolume

noncomputable section

namespace Submission.Obl.k4_uncapped_native_capping.UWE

open MeasureTheory Set

/-- The continuous projected cap of a native signal band inside one packet,
measured in original incidence units. Dividing later by the fixed packet budget
`q * ν(A)` leaves precisely the balanced density ratio `|det Q| / ν(A)`. -/
theorem native_signal_band_projected_cap
    (μ ρ : Measure Incidence) (hρ : ρ ≤ μ)
    {κ B a : ℝ} (hκ : 1 ≤ κ) (hB : 0 < B) (ha : 0 < a)
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2) (b : ℝ)
    (g : Observation → ENNReal) (hg : Measurable g)
    (hlaw : μ.map (obs B a) = (volume.prod Measure.count).withDensity g) (M : ENNReal)
    (hnative : ∀ᵐ p ∂ρ, p.2 ∈ Icc (0 : ℝ) 1 ∧ ‖y p.1 p.2‖ ≤ κ ∧
      |MvPolynomial.eval (x p.1 p.2) P - b| ≤ κ * a ∧
      |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) P)| ≤ κ * B ∧
      |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4)
        (MvPolynomial.pderiv (3 : Fin 4) P))| ≤ κ * B ^ 2 / a ∧
      B / κ ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) P)| ∧
      g (obs B a p) ≤ M)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.det ≠ 0)
    (e c u : EuclideanSpace ℝ (Fin 2)) (t₀ Z : ℝ)
    {K q : ℝ} (hK : 0 < K) (hq : 0 < q)
    (hfull : q / K ≤ ‖Matrix.toEuclideanLin Q.transpose e‖)
    (U : Set (EuclideanSpace ℝ (Fin 2))) (hU : MeasurableSet U)
    (hframe : ∀ᵐ p ∂ρ, ‖Matrix.toEuclideanLin Q⁻¹ (y p.1 p.2 - c - p.2 • u)‖ ≤ K)
    (hproject : ∀ᵐ p ∂ρ,
      (WithLp.toLp 2 ![(p.2 - t₀) / q, (inner ℝ e (y p.1 p.2) - Z) / q] :
        EuclideanSpace ℝ (Fin 2)) ∈ U) :
    ρ univ ≤ (M * ENNReal.ofReal (64 * κ ^ 2)) *
      ENNReal.ofReal (4 * K ^ 2 * q * |Q.det|) * volume U := by
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
  have hmass : (ρ.map (fun p => (obs B a p).1)) S = ρ univ := by
    rw [Measure.map_apply (show Measurable (fun p => (obs B a p).1) by unfold obs x; fun_prop) hS]
    apply measure_congr
    filter_upwards [hframe, hproject] with p hp hpr
    apply propext
    change (‖Matrix.toEuclideanLin Q⁻¹ (y p.1 p.2 - c - p.2 • u)‖ ≤ K ∧
      (WithLp.toLp 2 ![(p.2 - t₀) / q, (inner ℝ e (y p.1 p.2) - Z) / q] :
        EuclideanSpace ℝ (Fin 2)) ∈ U) ↔ True
    exact iff_true_intro ⟨hp, hpr⟩
  have hcap := native_signal_band_base_cap μ ρ hρ hκ hB ha P hP b g hg hlaw M hnative
  calc
    _ = (ρ.map (fun p => (obs B a p).1)) S := hmass.symm
    _ ≤ ((M * ENNReal.ofReal (64 * κ ^ 2)) • volume) S := hcap S
    _ = (M * ENNReal.ofReal (64 * κ ^ 2)) * volume S := by rw [Measure.smul_apply, smul_eq_mul]
    _ ≤ (M * ENNReal.ofReal (64 * κ ^ 2)) *
        (ENNReal.ofReal (4 * K ^ 2 * q * |Q.det|) * volume U) := by
      gcongr
      exact volume_packet_projected_base Q hQ e c u t₀ Z hK hq hfull U hU
    _ = _ := by ring

end Submission.Obl.k4_uncapped_native_capping.UWE
