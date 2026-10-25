import Submission.Obl.k4_remainder_pure_profile_normalization.WeightedTransport
import Submission.Obl.k4_remainder_pure_profile_normalization.LabelDensities
import Submission.Obl.k4_remainder_pure_profile_normalization.Normalizer
import Submission.Obl.k4_remainder_pure_profile_normalization.ComposedDepth

namespace Submission.Obl.k4_remainder_pure_profile_normalization
open MeasureTheory Set
open scoped ENNReal

noncomputable def Atlas.priorMass {p : Data} {k : ℕ} (a : Atlas p k) (b : Fin a.C) : ℝ :=
  (p.ν k (a.γ b) (a.A b)).toReal

noncomputable def Atlas.densityRatio {p : Data} {k : ℕ} (a : Atlas p k) (b : Fin a.C) : ℝ :=
  |(a.Q b).det| / a.priorMass b

noncomputable def Atlas.normalizedMeasure {p : Data} {k : ℕ} (a : Atlas p k)
    (b : Fin a.C) : Measure Incidence :=
  ((a.system.normPrior (p.ν k) b).prod volume).restrict (a.system.normEventOf b)

noncomputable def Atlas.normalizedObservation {p : Data} {k : ℕ} (a : Atlas p k)
    (r σ : ℝ) (b : Fin a.C) : Incidence → Observation :=
  obs (p.B k (a.γ b) / δ (p.N k) r) (δ (p.N k) σ)

noncomputable def Atlas.normalizedDensity {p : Data} {k : ℕ} (a : Atlas p k)
    (hD : ∀ b, (a.Q b).det ≠ 0) (t : ℝ) (b : Fin a.C) : Observation → ENNReal :=
  (a.system.frameOf b).transportedDensity (a.system.frameOf_q_pos b).ne'
    (isUnit_iff_ne_zero.mpr (hD b)) (a.priorMass b) (a.labelDensity t b)

theorem Atlas.measurable_normalizedDensity {p : Data} {k : ℕ} (a : Atlas p k)
    (hD : ∀ b, (a.Q b).det ≠ 0) (t : ℝ) (b : Fin a.C) :
    Measurable (a.normalizedDensity hD t b) :=
  (a.system.frameOf b).measurable_transportedDensity _ _ _ (a.measurable_labelDensity t b)

theorem KnownSystem.Valid.frame_support {p : Data} {k M D : ℕ} {r : ℝ}
    {s : KnownSystem p k} (hs : s.Valid M D r) (b : Fin s.atlas.C) :
    ∀ z ∈ s.atlas.F b, z.1 ∈ s.atlas.A b ∧ z.2 ∈
      Icc (s.atlas.system.frameOf b).t₀
        ((s.atlas.system.frameOf b).t₀ + (s.atlas.system.frameOf b).q) := by
  intro z hz
  have hh := (hs.chart b).2.2.2.2.2.2.2.2.2.2.1 z hz
  refine ⟨hh.2.1, hh.2.2.1.1, ?_⟩
  change z.2 ≤ (s.atlas.j b : ℝ) / (2 : ℝ) ^ s.atlas.T + 1 / (2 : ℝ) ^ s.atlas.T
  convert hh.2.2.1.2 using 1 <;> ring

/-- Canonical original label densities give actual normalized density laws at
every admissible remaining depth. -/
theorem KnownSystem.Valid.normalizedDensity_law {p : Data} (hp : p.Valid)
    {k M D : ℕ} {r σ : ℝ} {s : KnownSystem p k} (hs : s.Valid M D r)
    (hr : 0 ≤ r) (hσ : 0 ≤ σ) (hL : r + σ ≤ p.L)
    (hprior : ∀ b, 0 < s.atlas.priorMass b) (b : Fin s.atlas.C) :
    (s.atlas.normalizedMeasure b).map (s.atlas.normalizedObservation r σ b) =
      (volume.prod Measure.count).withDensity
        (s.atlas.normalizedDensity (fun b => (hs.chart b).1) (composedDepth (p.N k) r σ) b) := by
  obtain ⟨_, _, hsample⟩ := hp.sampleProblem
  letI : IsProbabilityMeasure (p.ν k (s.atlas.γ b)) := (hsample k).prob _
  let F := s.atlas.system.frameOf b
  have hN : 1 < p.N k := by linarith [hp.1 k]
  have ht : 0 ≤ composedDepth (p.N k) r σ := composedDepth_nonneg hN hr hσ
  have htL : composedDepth (p.N k) r σ ≤ p.L := (composedDepth_bounds hN r σ).2.trans hL
  have hlaw := hs.labelDensity_law hp ht htL b
  rw [delta_composedDepth hN] at hlaw
  exact F.normalized_obs_density_ratio (s.atlas.system.frameOf_q_pos b)
    (isUnit_iff_ne_zero.mpr (hs.chart b).1) (p.ν k (s.atlas.γ b))
    (hs.chart b).2.2.2.2.2.2.1 (hs.chart b).2.2.2.2.2.2.2.1
    (hs.frame_support b) (hprior b) (p.B k (s.atlas.γ b)) (δ (p.N k) r) (δ (p.N k) σ)
    (by unfold δ; positivity) (s.atlas.labelDensity (composedDepth (p.N k) r σ) b)
    (s.atlas.measurable_labelDensity _ b) hlaw

/-- The sampled normalized canonical density is the actual original chart
label density times the exact spatial-Jacobian/prior ratio. -/
theorem Atlas.normalizedDensity_observed {p : Data} {k : ℕ} (a : Atlas p k)
    (hD : ∀ b, (a.Q b).det ≠ 0) {r σ : ℝ} (hN : 1 < p.N k)
    (b : Fin a.C) (z : Incidence) :
    a.normalizedDensity hD (composedDepth (p.N k) r σ) b
      (a.normalizedObservation r σ b ((a.system.frameOf b).normInc z)) =
      ENNReal.ofReal (a.densityRatio b) * a.labelDensity (composedDepth (p.N k) r σ) b
        (obs (p.B k (a.γ b)) (δ (p.N k) (composedDepth (p.N k) r σ)) z) := by
  have h := (a.system.frameOf b).transportedDensity_observed
    (a.system.frameOf_q_pos b).ne' (isUnit_iff_ne_zero.mpr (hD b)) (a.priorMass b)
    (p.B k (a.γ b)) (δ (p.N k) r) (δ (p.N k) σ) (by unfold δ; positivity)
    (a.labelDensity (composedDepth (p.N k) r σ) b) z
  rw [← delta_composedDepth hN r σ] at h
  exact h

/-- Exact cancellation of a normalized world's weight and conditioned incidence
law, for every measurable exceptional event. -/
theorem KnownSystem.Valid.normalized_weighted_event {p : Data} (hp : p.Valid)
    {k M D : ℕ} {r : ℝ} {s : KnownSystem p k} (hs : s.Valid M D r)
    (hprior : ∀ b, 0 < s.atlas.priorMass b) (hκ : 0 < s.atlas.κ)
    (b : Fin s.atlas.C) (S : Set Incidence) (hS : MeasurableSet S) :
    ENNReal.ofReal (s.atlas.system.normWeight (p.ω k) (p.ν k) b) *
        s.atlas.normalizedMeasure b S =
      ENNReal.ofReal (s.atlas.system.normZ (p.ω k) (p.ν k))⁻¹ *
        ENNReal.ofReal (p.ω k (s.atlas.γ b)) *
        s.atlas.selectedMeasure b ((s.atlas.system.frameOf b).normInc ⁻¹' S) := by
  obtain ⟨_, _, hsample⟩ := hp.sampleProblem
  letI : IsProbabilityMeasure (p.ν k (s.atlas.γ b)) := (hsample k).prob _
  have hknown : s.atlas.KnownAt M D r := ⟨s.lists, hs⟩
  have hZ : 0 < s.atlas.system.normZ (p.ω k) (p.ν k) :=
    (inv_pos.mpr hκ).trans_le (hknown.normalizer_lower (hsample k).prob
      (hsample k).weight_nonneg hκ)
  have hh := (s.atlas.system.frameOf b).normalized_weighted_mass
    (s.atlas.system.frameOf_q_pos b) (isUnit_iff_ne_zero.mpr (hs.chart b).1)
    (p.ν k (s.atlas.γ b)) (hs.chart b).2.2.2.2.2.2.1 (hs.chart b).2.2.2.2.2.2.2.1
    (hs.frame_support b) (hprior b) ((hsample k).weight_nonneg (s.atlas.γ b)) hZ S hS
  simpa only [Atlas.normalizedMeasure, Atlas.selectedMeasure, Normalization.ChartSystem.normWeight,
    Normalization.ChartSystem.normPrior, Normalization.ChartSystem.normEventOf,
    Atlas.system, Normalization.ChartSystem.frameOf, div_eq_mul_inv, one_div, mul_one, one_mul] using hh

end Submission.Obl.k4_remainder_pure_profile_normalization
