import Submission.Obl.k4_remainder_pure_profile_normalization.RatioCharts
import Submission.Obl.k4_remainder_pure_profile_normalization.FiniteTails
import Submission.Obl.k4_remainder_pure_profile_normalization.NativeDensities
import Submission.Obl.k4_remainder_pure_profile_normalization.NormalizedGeometry

namespace Submission.Obl.k4_remainder_pure_profile_normalization
open MeasureTheory Filter Set
open scoped ENNReal

/-- Choose and retain one set of actual original terminal lists per sample. -/
noncomputable def KnownSequence.knownSystem {p : Data} {M D : ℕ} {r h : ℝ}
    (s : KnownSequence p M D r h) (k : ℕ) : KnownSystem p (s.index k) :=
  ⟨s.atlas k, Classical.choose (s.valid k)⟩

theorem KnownSequence.knownSystem_valid {p : Data} {M D : ℕ} {r h : ℝ}
    (s : KnownSequence p M D r h) (k : ℕ) : (s.knownSystem k).Valid M D r :=
  Classical.choose_spec (s.valid k)

theorem NormalizedSamples.prior_pos {p : Data} (hp : p.Valid) {r h : ℝ}
    (t : NormalizedSamples p r h) (k : ℕ) (b : Fin (t.sequence.atlas k).C) :
    0 < (t.sequence.atlas k).priorMass b := by
  exact (inv_pos.mpr (pow_pos (by linarith [hp.1 (t.sequence.index k)]) _)).trans_le
    (t.prior_lower k b)

noncomputable def NormalizedSamples.jointDensity {p : Data} (hp : p.Valid) {r h : ℝ}
    (t : NormalizedSamples p r h) (k : ℕ) (b : Fin (t.sequence.atlas k).C) (u : ℝ) :
    JointObservation → ENNReal :=
  Classical.choose ((t.sample k).joint_density (hp.1 _) b
    ((t.sequence.atlas k).system.normEventOf b)
    (δ (p.N (t.sequence.index k)) (p.L - r)) (δ (p.N (t.sequence.index k)) u))

/-- The actual normalized chart family before incidence-only homogenization. -/
noncomputable def NormalizedSamples.rawData {p : Data} (hp : p.Valid) {r h : ℝ}
    (t : NormalizedSamples p r h) (cap : ℝ) : Data :=
  t.sequence.remainingData cap (fun k => 3 * (t.sequence.atlas k).κ)
    (fun k => (t.sequence.atlas k).system.normEventOf) (fun _ => 0)
    (fun k b σ => (t.sequence.atlas k).normalizedDensity
      (fun b => ((t.sequence.knownSystem_valid k).chart b).1)
      (composedDepth (p.N (t.sequence.index k)) r σ) b)
    (t.jointDensity hp)

theorem NormalizedSamples.rawData_samples {p : Data} (hp : p.Valid) {r h : ℝ}
    (t : NormalizedSamples p r h) (cap : ℝ) (k : ℕ) :
    Normalization.SampleProblem ((t.rawData hp cap).N k) ((t.rawData hp cap).K k)
      t.formatM t.formatD ((t.rawData hp cap).W k)
      ((t.rawData hp cap).ω k) ((t.rawData hp cap).ν k) ((t.rawData hp cap).E k)
      ((t.rawData hp cap).P k) ((t.rawData hp cap).B k) := t.sample k

theorem NormalizedSamples.rawData_subpower {p : Data} (hp : p.Valid) {r h : ℝ}
    (t : NormalizedSamples p r h) (cap : ℝ) :
    (∀ k, 1 ≤ (t.rawData hp cap).K k) ∧ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ k in atTop, (t.rawData hp cap).K k ≤ (t.rawData hp cap).N k ^ ε :=
  t.subpower hp

theorem NormalizedSamples.rawData_pure_law {p : Data} (hp : p.Valid) {r h : ℝ}
    (t : NormalizedSamples p r h) (cap : ℝ) (hr : 0 ≤ r)
    (k : ℕ) (b : Fin ((t.rawData hp cap).W k)) (σ : ℝ)
    (hσ : 0 ≤ σ) (hσL : σ ≤ (t.rawData hp cap).L) :
    Measurable ((t.rawData hp cap).g k b σ) ∧
      ((((t.rawData hp cap).ν k b).prod volume).restrict ((t.rawData hp cap).E k b)).map
        (obs ((t.rawData hp cap).B k b) (δ ((t.rawData hp cap).N k) σ)) =
          (volume.prod Measure.count).withDensity ((t.rawData hp cap).g k b σ) := by
  constructor
  · exact (t.sequence.atlas k).measurable_normalizedDensity
      (fun b => ((t.sequence.knownSystem_valid k).chart b).1)
      (composedDepth (p.N (t.sequence.index k)) r σ) b
  · exact (t.sequence.knownSystem_valid k).normalizedDensity_law hp hr hσ
      (by change r + σ ≤ p.L; change σ ≤ p.L - r at hσL; linarith)
      (fun b => t.prior_pos hp k b) b

theorem NormalizedSamples.rawData_joint_law {p : Data} (hp : p.Valid) {r h : ℝ}
    (t : NormalizedSamples p r h) (cap : ℝ) (k : ℕ)
    (b : Fin ((t.rawData hp cap).W k)) (u : ℝ) :
    Measurable ((t.rawData hp cap).G k b u) ∧
      ((((t.rawData hp cap).ν k b).prod volume).restrict ((t.rawData hp cap).E k b)).map
        (fun z => (obs ((t.rawData hp cap).B k b) (δ ((t.rawData hp cap).N k) (t.rawData hp cap).L) z,
          fun j : Fin 2 => ⌊v z.1 j / δ ((t.rawData hp cap).N k) u⌋)) =
          ((volume.prod Measure.count).prod Measure.count).withDensity
            ((t.rawData hp cap).G k b u) := by
  have h := Classical.choose_spec ((t.sample k).joint_density (hp.1 _) b
    ((t.sequence.atlas k).system.normEventOf b)
    (δ (p.N (t.sequence.index k)) (p.L - r)) (δ (p.N (t.sequence.index k)) u))
  exact ⟨h.1, h.2.1⟩

end Submission.Obl.k4_remainder_pure_profile_normalization
