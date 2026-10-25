/- Adapted from this LOT tree, obligation o100, session x0340, commit fb1668b,
   Submission/Obl/k4_scalar_marked_profile_selection/AtomDensity.lean. -/
import Submission.Obl.k4_marked_scalar_grid_selection.Scalar.NoiseCoordinates
import Submission.Obl.k4_profile_density_bounds.Mass
import Submission.Obl.k4_dyadic_crop_affine_laws.Framework.CountedDensity

noncomputable section

namespace Submission.Obl.k4_marked_scalar_grid_selection.Scalar

open MeasureTheory Set
open scoped ENNReal

abbrev packBase {B : Type*} (p : ℝ × (ℝ × B)) : Base × B :=
  (![p.1, p.2.1], p.2.2)

theorem packBase_law {B : Type*} [MeasurableSpace B] [Countable B]
    [MeasurableSingletonClass B] :
    ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (Measure.count : Measure B))).map
      packBase = (volume : Measure Base).prod Measure.count := by
  have hp := (volume_preserving_finTwoArrow ℝ).symm
    (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ)
  have hpair : MeasurePreserving (fun p : ℝ × ℝ => (![p.1, p.2] : Base)) volume volume := by
    convert hp using 1
    funext p
    funext i
    fin_cases i <;> rfl
  have hprod := hpair.prod (MeasurePreserving.id (Measure.count : Measure B))
  have hassoc := (measurePreserving_prodAssoc (volume : Measure ℝ) (volume : Measure ℝ)
    (Measure.count : Measure B)).symm (MeasurableEquiv.prodAssoc :
      ((ℝ × ℝ) × B) ≃ᵐ (ℝ × (ℝ × B)))
  exact (hprod.comp hassoc).map_eq

/-- The unweighted observation of one whole tag/time atom has the intercept
noise ceiling. The hidden bin may be any measurable function of time and of the
other four coefficient noises. -/
theorem atom_label_density_bound {H J : ℕ} {σ : ℝ} (hσ : 0 < σ)
    (b : Fin H → Fin 5 → ℝ) (j : Fin H) (z : Fin J)
    {B : Type*} [MeasurableSpace B] [Countable B] [MeasurableSingletonClass B]
    (f : ℝ × (Fin 4 → ℝ) → B) (hf : Measurable f) (D : ℝ≥0∞)
    (hlabel : ∀ t, (otherNoise σ).map (fun v => f (t, v)) ≤ D • Measure.count) :
    (((noise σ).prod (volume.restrict (cell J z))).map
      (fun p => ((![p.2, y ((j : ℕ), b j + p.1) p.2] : Base),
        f (p.2, dropY p.1)))) ≤
      (ENNReal.ofReal σ⁻¹ * D) • (volume : Measure Base).prod Measure.count := by
  letI := noise_probability hσ
  letI := intervalNoise_probability hσ
  letI := otherNoise_probability hσ
  let τ := volume.restrict (cell J z)
  let shift : ℝ × (Fin 4 → ℝ) → ℝ := fun p =>
    b j 0 + p.1 * (b j 1 + p.2 0)
  have hshift : Measurable shift := by fun_prop
  have hβ : intervalNoise σ ≤ ENNReal.ofReal σ⁻¹ • volume :=
    smul_le_smul_left _ Measure.restrict_le_self
  have hb := labelled_noise_bound τ (otherNoise σ) (intervalNoise σ)
    (ENNReal.ofReal σ⁻¹) D hβ f hf hlabel shift hshift
  have hpack : Measurable (packBase : ℝ × (ℝ × B) → Base × B) := by fun_prop
  have h := Measure.map_mono hb hpack
  rw [Measure.map_smul _ hpack.aemeasurable] at h
  have hright : (τ.prod ((volume : Measure ℝ).prod (Measure.count : Measure B))).map packBase ≤
      (volume : Measure Base).prod Measure.count := by
    rw [← packBase_law]
    exact Measure.map_mono (Measure.prod_mono (μ' := (volume : Measure ℝ))
      Measure.restrict_le_self le_rfl) hpack
  have h' := h.trans (smul_le_smul_left _ hright)
  rw [Measure.map_map hpack (by fun_prop), ← noiseReorder_law hσ τ,
    Measure.map_map (by fun_prop) (by fun_prop)] at h'
  convert h' using 1
  congr 1
  funext p
  apply Prod.ext
  · funext i
    fin_cases i
    · rfl
    · dsimp [packBase, shift, noiseReorder, dropY, y]
      ring
  · rfl

abbrev pureWidthObservation (a : ℝ) (p : Incidence) : ObsSpace :=
  (![p.2, y p.1 p.2], ⌊x p.1 p.2 / a⌋)

theorem atom_pure_density_bound {H J : ℕ} {σ : ℝ} (hσ : 0 < σ)
    (a : ℝ) (b : Fin H → Fin 5 → ℝ) (j : Fin H) (z : Fin J) :
    (atom σ J b j z).map (pureWidthObservation a) ≤ ENNReal.ofReal σ⁻¹ • reference := by
  letI := otherNoise_probability hσ
  let f : ℝ × (Fin 4 → ℝ) → ℤ := fun p =>
    ⌊((b j 2 + p.2 1) + p.1 * (b j 3 + p.2 2) + p.1 ^ 2 * (b j 4 + p.2 3)) / a⌋
  have hf : Measurable f := by fun_prop
  have hlabel (t : ℝ) : (otherNoise σ).map (fun v => f (t, v)) ≤
      (1 : ℝ≥0∞) • Measure.count := by
    apply le_count_of_singletons
    intro n
    have hft : Measurable (fun v => f (t, v)) := by fun_prop
    rw [Measure.map_apply hft (measurableSet_singleton n)]
    exact (measure_mono (subset_univ _)).trans_eq (measure_univ)
  have h := atom_label_density_bound hσ b j z f hf 1 hlabel
  rw [atom, Measure.map_map (by fun_prop : Measurable (pureWidthObservation a)) (by fun_prop)]
  simpa [f, pureWidthObservation, atomMap, x, dropY, Function.comp_def, reference] using h



theorem atom_obs_density_bound {H J : ℕ} {σ : ℝ} (hσ : 0 < σ)
    (N r : ℝ) (b : Fin H → Fin 5 → ℝ) (j : Fin H) (z : Fin J) :
    (atom σ J b j z).map (obs N r) ≤ ENNReal.ofReal σ⁻¹ • reference :=
  atom_pure_density_bound hσ (N ^ (-r)) b j z


abbrev widthObservation (a ρ : ℝ) (p : Incidence) : Base × (ℤ × ℤ) :=
  (![p.2, y p.1 p.2], (⌊x p.1 p.2 / a⌋, ⌊p.1.2 1 / ρ⌋))

theorem measurable_widthObservation (a ρ : ℝ) : Measurable (widthObservation a ρ) := by
  fun_prop

/-- A whole atom's joint density gains the bin-width/noise-width factor in its
scalar velocity label. -/
theorem atom_joint_density_bound {H J : ℕ} {σ ρ : ℝ} (hσ : 0 < σ) (hρ : 0 < ρ)
    (a : ℝ) (b : Fin H → Fin 5 → ℝ) (j : Fin H) (z : Fin J) :
    (atom σ J b j z).map (widthObservation a ρ) ≤
      ENNReal.ofReal (σ⁻¹ * min 1 (ρ / σ)) •
        (volume : Measure Base).prod (Measure.count : Measure (ℤ × ℤ)) := by
  letI := otherNoise_probability hσ
  let f : ℝ × (Fin 4 → ℝ) → ℤ × ℤ := fun p =>
    (⌊((b j 2 + p.2 1) + p.1 * (b j 3 + p.2 2) + p.1 ^ 2 * (b j 4 + p.2 3)) / a⌋,
      ⌊(b j 1 + p.2 0) / ρ⌋)
  have hf : Measurable f := by fun_prop
  have hlabel (t : ℝ) : (otherNoise σ).map (fun v => f (t, v)) ≤
      ENNReal.ofReal (min 1 (ρ / σ)) • Measure.count :=
    otherNoise_joint_bin hσ hρ (b j 1) _ (by fun_prop)
  have h := atom_label_density_bound hσ b j z f hf _ hlabel
  rw [atom, Measure.map_map (measurable_widthObservation _ _) (by fun_prop)]
  simpa [f, widthObservation, atomMap, x, y, dropY, Function.comp_def,
    ENNReal.ofReal_mul (inv_nonneg.mpr hσ.le)] using h

/-- A measure domination and a geometric support yield a density representative
satisfying the same ceiling and support pointwise. -/
theorem bounded_supported_density {Y : Type*} [MeasurableSpace Y]
    (μ ρ : Measure Y) [IsFiniteMeasure μ] [SigmaFinite ρ]
    (c : ℝ≥0∞) (hdom : μ ≤ c • ρ) (S : Set Y) (hS : MeasurableSet S)
    (hsupp : ∀ᵐ y ∂μ, y ∈ S) :
    ∃ f : Y → ℝ≥0∞, Measurable f ∧ μ = ρ.withDensity f ∧
      ∀ y, f y ≤ S.indicator (fun _ => c) y := by
  have hac : μ ≪ ρ := (Measure.absolutelyContinuous_of_le hdom).trans
    ((Measure.absolutelyContinuous_refl ρ).smul_left c)
  obtain ⟨f, hf, hμ, hfs⟩ :=
    Submission.Obl.k4_dyadic_crop_affine_laws.Framework.exists_density_with_support
      μ ρ hac S hS hsupp
  have hcap : ∀ᵐ y ∂ρ, f y ≤ c := by
    apply Submission.Obl.k4_profile_density_bounds.ae_density_le_of_measure_bound ρ hf c
    intro A hA
    rw [← hμ]
    exact hdom A
  refine ⟨(fun y => min (f y) c), hf.min measurable_const, ?_, ?_⟩
  · rw [hμ]
    apply withDensity_congr_ae
    filter_upwards [hcap] with y hy
    exact (min_eq_left hy).symm
  · intro y
    by_cases hy : y ∈ S
    · rw [indicator_of_mem hy]
      exact min_le_right _ _
    · simp only [indicator_of_notMem hy]
      change min (f y) c ≤ 0
      rw [hfs y hy, min_eq_left zero_le]

end Submission.Obl.k4_marked_scalar_grid_selection.Scalar
