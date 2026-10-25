/-
Adapted from this LOT tree, obligation o093, session x0535, commit 21cac614,
Submission/Obl/k4_scalar_critical_path_terminal/DensityCaps.lean. Original attribution is retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.DensityMasks

/-! Original density-window masks give observation caps for every later
dominated incidence law. Pure and joint reference measures stay unchanged. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

theorem map_cap_of_density_exception_null {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] {μ σ : Measure X} (hσ : σ ≤ μ) (ref : Measure Y)
    {obs : X → Y} (hobs : Measurable obs) {d : Y → ℝ≥0∞} (hd : Measurable d)
    (hlaw : μ.map obs = ref.withDensity d) (C : ℝ≥0∞)
    (hnull : σ {x | C < d (obs x)} = 0) : σ.map obs ≤ C • ref := by
  apply Measure.le_iff.mpr
  intro B hB
  rw [Measure.map_apply hobs hB, Measure.smul_apply]
  calc
    σ (obs ⁻¹' B) = σ (obs ⁻¹' B \ {x | C < d (obs x)}) :=
      (measure_sdiff_null hnull).symm
    _ ≤ μ (obs ⁻¹' B \ {x | C < d (obs x)}) := hσ _
    _ ≤ C * ref B :=
      Submission.Obl.k4_scalar_terminal_chart_packet_extraction.mass_le_of_density_le
        hobs hd hlaw hB C Subset.rfl

theorem pure_observation_cap {p : Code} (hp : Exact p) (k : ℕ) (i : Fin (W p k))
    {r : ℝ} (hr : 0 ≤ r) (hrL : r ≤ L p) (τ : ℝ) {σ : Measure State}
    (hσ : σ ≤ mu p k i) (hnull : σ (pureException p k i r τ) = 0) :
    σ.map (Submission.Obl.k4_scalar_terminal_chart_packet_extraction.obsL (N p k ^ (-r))) ≤
      ENNReal.ofReal (N p k ^ (-f p r + τ)) • (volume.prod (Measure.count : Measure ℤ)) := by
  apply map_cap_of_density_exception_null hσ _
    (Submission.Obl.k4_scalar_terminal_chart_packet_extraction.measurable_obsL _)
      (hp.2.2.1 k i r hr hrL).1 (hp.2.2.1 k i r hr hrL).2 _
  apply measure_mono_null (t := pureException p k i r τ) ?_ hnull
  intro z hz
  exact Or.inr hz

theorem angular_observation_cap {p : Code} (hp : Exact p) (k : ℕ) (i : Fin (W p k))
    {a : ℝ} (ha : 0 < a) (haU : a ≤ U p) (τ : ℝ) {σ : Measure State}
    (hσ : σ ≤ mu p k i) (hnull : σ (angularException p k i a τ) = 0) :
    σ.map (Submission.Obl.k4_scalar_terminal_chart_packet_extraction.obsG
      (N p k ^ (-L p)) (N p k ^ (-a))) ≤
      ENNReal.ofReal (N p k ^ (-f p (L p) - S p * a + τ)) •
        ((volume.prod (Measure.count : Measure ℤ)).prod (Measure.count : Measure ℤ)) := by
  exact map_cap_of_density_exception_null hσ _
    (Submission.Obl.k4_scalar_terminal_chart_packet_extraction.measurable_obsG _ _)
      (hp.2.2.2.1 k i a ha haU).1 (hp.2.2.2.1 k i a ha haU).2 _ hnull

/-- The cap is an original base-volume cap, with a single hidden bin. It
persists under every later sparse restriction through the same hypotheses. -/
theorem pure_base_bin_cap {p : Code} (hp : Exact p) (k : ℕ) (i : Fin (W p k))
    {r : ℝ} (hr : 0 ≤ r) (hrL : r ≤ L p) (τ : ℝ) {σ : Measure State}
    (hσ : σ ≤ mu p k i) (hnull : σ (pureException p k i r τ) = 0)
    {B : Set (Fin 2 → ℝ)} (hB : MeasurableSet B) (c : ℤ) :
    σ ((Submission.Obl.k4_scalar_terminal_chart_packet_extraction.obsL (N p k ^ (-r))) ⁻¹'
      (B ×ˢ {c})) ≤ ENNReal.ofReal (N p k ^ (-f p r + τ)) * volume B := by
  have h := pure_observation_cap hp k i hr hrL τ hσ hnull (B ×ˢ {c})
  rw [Measure.map_apply
    (Submission.Obl.k4_scalar_terminal_chart_packet_extraction.measurable_obsL _)
      (hB.prod (measurableSet_singleton c)), Measure.smul_apply, smul_eq_mul,
    Measure.prod_prod] at h
  simpa using h

theorem angular_base_bins_cap {p : Code} (hp : Exact p) (k : ℕ) (i : Fin (W p k))
    {a : ℝ} (ha : 0 < a) (haU : a ≤ U p) (τ : ℝ) {σ : Measure State}
    (hσ : σ ≤ mu p k i) (hnull : σ (angularException p k i a τ) = 0)
    {B : Set (Fin 2 → ℝ)} (hB : MeasurableSet B) (c e : ℤ) :
    σ ((Submission.Obl.k4_scalar_terminal_chart_packet_extraction.obsG
      (N p k ^ (-L p)) (N p k ^ (-a))) ⁻¹' ((B ×ˢ {c}) ×ˢ {e})) ≤
        ENNReal.ofReal (N p k ^ (-f p (L p) - S p * a + τ)) * volume B := by
  have h := angular_observation_cap hp k i ha haU τ hσ hnull ((B ×ˢ {c}) ×ˢ {e})
  rw [Measure.map_apply
    (Submission.Obl.k4_scalar_terminal_chart_packet_extraction.measurable_obsG _ _)
      ((hB.prod (measurableSet_singleton c)).prod (measurableSet_singleton e)),
    Measure.smul_apply, smul_eq_mul, Measure.prod_prod, Measure.prod_prod] at h
  simpa using h

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures
