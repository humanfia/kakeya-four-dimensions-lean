import Submission.Obl.k4_scalar_pure_multiworld_homogenization.Table
import Submission.Obl.k4_native_base_flattening.Charge

noncomputable section

namespace Submission.Obl.k4_scalar_pure_multiworld_homogenization

open MeasureTheory Set
open scoped ENNReal
open Submission.Lib.K4ModelReduction

/-- The table error consists of source averaging error, a low-density cutoff,
and the fine cells that cross a coarse hidden-bin boundary. -/
theorem single_sample_table_exception
    (μ : Measure Incidence) (f h : (Fin 6 → ℝ) → ℝ)
    (hf : Measurable f) (hh : Measurable h)
    (hf₀ : ∀ z, 0 ≤ f z) (hh₀ : ∀ z, 0 ≤ h z)
    {R M σ a : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M) (hσ : 0 < σ) (ha : 0 < a)
    (hsf : supportedInCube f R) (hsh : supportedInCube h R)
    (hbf : ∀ z, f z ≤ M) (hbh : ∀ z, h z ≤ M)
    (hsource : μ.map chartPoint = volume.withDensity (fun z => ENNReal.ofReal (f z)))
    (hcell : ∀ z z', (∀ i ∉ ([0, 1] : List (Fin 6)), z i = z' i) →
      (∀ i ∈ ([0, 1] : List (Fin 6)), ⌊z i / σ⌋ = ⌊z' i / σ⌋) → h z = h z')
    (G : Observation → ENNReal) (hG : Measurable G)
    (hlaw : μ.map (chartObservation a ∘ chartPoint) = reference.withDensity G)
    (ε : ENNReal) :
    μ {z | G (chartObservation a (chartPoint z)) <
          2⁻¹ * ENNReal.ofReal (chartTable σ a h (chartLabel σ (chartPoint z))) ∨
        2 * ENNReal.ofReal (chartTable σ a h (chartLabel σ (chartPoint z))) <
          G (chartObservation a (chartPoint z)) ∨
        ENNReal.ofReal (chartTable σ a h (chartLabel σ (chartPoint z))) < ε} ≤
      ENNReal.ofReal M * ENNReal.ofReal ((2 * R / a + 5) * (2 * σ * (2 * R) ^ 5)) +
        2 * densityL1Distance volume h f +
        ε * ENNReal.ofReal ((2 * R) ^ 2 * (2 * R / a + 5)) := by
  classical
  let O : Incidence → Observation := chartObservation a ∘ chartPoint
  have hO : Measurable O := (measurable_chartObservation a).comp measurable_chartPoint
  let A := marginal a h
  have hA : Measurable A := measurable_marginal a hh
  have htrue : μ.map O = reference.withDensity (marginal a f) := by
    change μ.map (chartObservation a ∘ chartPoint) = _
    rw [← Measure.map_map (measurable_chartObservation a) measurable_chartPoint, hsource]
    exact map_chartObservation_withDensity a hf
  let : SigmaFinite reference := by infer_instance
  have hae : G =ᵐ[reference] marginal a f :=
    (withDensity_eq_iff_of_sigmaFinite hG.aemeasurable (measurable_marginal a hf).aemeasurable).mp
      (hlaw.symm.trans htrue)
  have hdf : ∀ z, |f z| ≤ M := fun z => by simpa only [abs_of_nonneg (hf₀ z)] using hbf z
  have hdh : ∀ z, |h z| ≤ M := fun z => by simpa only [abs_of_nonneg (hh₀ z)] using hbh z
  have herror : (∫⁻ z, Submission.Obl.k4_native_base_flattening.ediff (G z) (A z)
      ∂reference) ≤ densityL1Distance volume h f := by
    calc
      _ = ∫⁻ z, Submission.Obl.k4_native_base_flattening.ediff (A z) (marginal a f z)
          ∂reference := by
        apply lintegral_congr_ae
        filter_upwards [hae] with z hz
        rw [hz, Submission.Obl.k4_native_base_flattening.ediff_comm]
      _ ≤ _ := marginal_discrepancy_le a hh hf hh₀ hf₀ hsh hsf hdh hdf
  let Bad : Set Observation := {z | G z < 2⁻¹ * A z ∨ 2 * A z < G z ∨ A z < ε}
  have hBad : MeasurableSet Bad :=
    (measurableSet_lt hG (measurable_const.mul hA)).union
      ((measurableSet_lt (measurable_const.mul hA) hG).union
        (measurableSet_lt hA measurable_const))
  have hfactor (z : Incidence) (hz : x z.1 z.2 ∉ straddles σ a) :
      ENNReal.ofReal (chartTable σ a h (chartLabel σ (chartPoint z))) = A (O z) := by
    rw [← chartTable_factor hσ a h hcell (chartPoint z) hz]
    exact ofReal_realMarginal a hh hh₀ hsh hdh _
  have hcover : {z | G (chartObservation a (chartPoint z)) <
          2⁻¹ * ENNReal.ofReal (chartTable σ a h (chartLabel σ (chartPoint z))) ∨
        2 * ENNReal.ofReal (chartTable σ a h (chartLabel σ (chartPoint z))) <
          G (chartObservation a (chartPoint z)) ∨
        ENNReal.ofReal (chartTable σ a h (chartLabel σ (chartPoint z))) < ε} ⊆
      {z | x z.1 z.2 ∈ straddles σ a} ∪ O ⁻¹' Bad := by
    intro z hz
    by_cases hs : x z.1 z.2 ∈ straddles σ a
    · exact Or.inl hs
    · right
      change G (O z) < 2⁻¹ * A (O z) ∨ 2 * A (O z) < G (O z) ∨ A (O z) < ε
      simp only [mem_ofPred_eq] at hz
      simpa only [hfactor z hs, O, Function.comp_apply] using hz
  have hcharge : μ (O ⁻¹' Bad) ≤ 2 * densityL1Distance volume h f +
      ε * ENNReal.ofReal ((2 * R) ^ 2 * (2 * R / a + 5)) := by
    rw [← Measure.map_apply hO hBad, hlaw, withDensity_apply _ hBad]
    exact (Submission.Obl.k4_native_base_flattening.bad_lintegral_le reference hG hA ε).trans
      (add_le_add (mul_le_mul' le_rfl herror)
        (mul_le_mul' le_rfl (reference_marginal_support_bound ha hR hsh)))
  calc
    _ ≤ μ {z | x z.1 z.2 ∈ straddles σ a} + μ (O ⁻¹' Bad) :=
      (measure_mono hcover).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal M * ENNReal.ofReal ((2 * R / a + 5) * (2 * σ * (2 * R) ^ 5)) +
        (2 * densityL1Distance volume h f + ε * ENNReal.ofReal ((2 * R) ^ 2 * (2 * R / a + 5))) :=
      add_le_add (source_straddling_bound hsource hR hσ ha hsf hbf) hcharge
    _ = _ := by rw [add_assoc]

end Submission.Obl.k4_scalar_pure_multiworld_homogenization
