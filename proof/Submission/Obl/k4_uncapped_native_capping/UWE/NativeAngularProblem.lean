/-
Adapted from this LOT tree o198, session x0693, commit b5c1b640df5e526ffc014739d6614359923ec044,
Submission/Obl/k4_balanced_native_packet_transport/UWE/NativeAngularProblem.lean. Existing source attributions below are retained.
-/
/-
Adapted from this LOT tree, o120, session x0649, commit 99e461c8faeab846d12253887b2a587a38b5aa0e,
Submission/Obl/k4_unbounded_width_exclusion/NativeAngularProblem.lean (namespace Submission.Obl.k4_unbounded_width_exclusion renamed to
Submission.Obl.k4_uncapped_native_capping.UWE).
-/
import Submission.Obl.k4_uncapped_native_capping.UWE.NonparallelMass

noncomputable section

namespace Submission.Obl.k4_uncapped_native_capping.UWE

open MeasureTheory Set

/-- Extract the three original observation laws directly from a valid frozen
problem, using the actual terminal and zero-depth density versions. -/
def Problem.Valid.nativeAngularSample {p : Problem} {S η : ℝ} (hp : p.Valid S η)
    (k : ℕ) (γ : Fin (p.W k)) {u : ℝ} (hu : 0 < u) (huη : u ≤ η * p.L) :
    NativeAngularSample (((p.ν k γ).prod volume).restrict (p.E k γ))
      (p.N k) p.L (p.B k γ) (δ (p.N k) u) := by
  rcases hp with ⟨hN, hNt, hK, hL, hd, hd1, hS, hη, hdata, hg, hG, hmono, htyp, hcap, hang⟩
  refine ⟨p.g k γ p.L, p.g k γ 0, p.G k γ u,
    (hg k γ p.L hL.le le_rfl).1, (hg k γ 0 le_rfl hL.le).1,
    (hG k γ u hu huη).1, (hg k γ p.L hL.le le_rfl).2, ?_, (hG k γ u hu huη).2⟩
  simpa [δ] using (hg k γ 0 le_rfl hL.le).2

/-- The native crossing support required by the pairing estimate holds almost
everywhere for each original problem world. -/
theorem Problem.Valid.ae_native_zero_crossing {p : Problem} {S η : ℝ} (hp : p.Valid S η)
    (k : ℕ) (γ : Fin (p.W k)) :
    ∀ᵐ z ∂(((p.ν k γ).prod volume).restrict (p.E k γ)),
      obs (p.B k γ) 1 z ∈ Submission.Obl.k4_coarsened_outer_horizon_composition.crossing
        (p.K k) 0 1 (1 / p.B k γ) (p.B k γ) 0 0 (1 : Matrix (Fin 2) (Fin 2) ℝ) (p.P k γ) := by
  rcases hp with ⟨hN, hNt, hK, hL, hd, hd1, hS, hη, hdata, hg, hG, hmono, htyp, hcap, hang⟩
  obtain ⟨M, D, hreg⟩ := hdata
  rcases (hreg k).2.2.2.1 γ with
    ⟨hν, hB, hBu, hBi, hP, hPc, hνfmt, hE, hEI, hEb, hEf, hprior, hfloor⟩
  have hprior' := ae_restrict_of_ae (s := p.E k γ)
    ((Measure.quasiMeasurePreserving_fst (μ := p.ν k γ) (ν := (volume : Measure ℝ))).ae hprior)
  filter_upwards [ae_restrict_mem hE, hprior', hfloor] with z hz hpr hfl
  have ht := (hEI hz).2
  obtain ⟨hy, hv, hdv, hddv⟩ := hpr z.2 ht
  have hnorm : ‖y z.1 z.2‖ ≤ p.K k := by linarith [norm_nonneg (v z.1)]
  apply Submission.Obl.k4_coarsened_outer_horizon_composition.obs_mem_crossing
    (by linarith only [hK.1 k] : 0 < p.K k) (by norm_num : (0 : ℝ) < 1) hB
    0 0 (1 : Matrix (Fin 2) (Fin 2) ℝ) (p.P k γ) hP z ht
  · simpa [Submission.Obl.k4_coarsened_outer_horizon_composition.y,
      Submission.Obl.k4_coarsened_outer_horizon_composition.x, y, x] using hnorm
  · simpa only [Submission.Obl.k4_coarsened_outer_horizon_composition.x, x, mul_one] using hv
  · exact hdv
  · simpa only [Submission.Obl.k4_coarsened_outer_horizon_composition.x, x, div_one] using hddv
  · exact hfl

end Submission.Obl.k4_uncapped_native_capping.UWE
