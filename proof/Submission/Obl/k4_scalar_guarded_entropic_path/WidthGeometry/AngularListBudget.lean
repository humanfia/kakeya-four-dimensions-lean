/-
Adapted from this LOT tree, obligation o134, session x0438, commit 2e990309978b,
Submission/Obl/k4_scalar_guarded_tangent_obstruction/AngularListBudget.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.WidthGeometry.CountedLists

namespace Submission.Obl.k4_scalar_guarded_entropic_path.WidthGeometry

open MeasureTheory Set

variable {Ω X β : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [MeasurableSpace β] [Countable β] [MeasurableSingletonClass β]

omit [MeasurableSingletonClass β] in
/-- A joint density cap on an observation mask is domination against the
pure marginal of the unchanged original law. -/
theorem restricted_joint_map_le (μ : Measure Ω) (ref : Measure X)
    (observe : Ω → X) (bin : Ω → β) (hobserve : Measurable observe) (hbin : Measurable bin)
    (f : X → ENNReal) (F : X × β → ENNReal) (hf : Measurable f)
    (hpure : μ.map observe = ref.withDensity f)
    (hjoint : μ.map (fun ω => (observe ω, bin ω)) = (ref.prod Measure.count).withDensity F)
    (G : Set (X × β)) (hG : MeasurableSet G) (c : ENNReal)
    (hcap : ∀ z ∈ G, F z ≤ c * f z.1) :
    (μ.restrict ((fun ω => (observe ω, bin ω)) ⁻¹' G)).map
        (fun ω => (observe ω, bin ω)) ≤
      c • ((μ.map observe).prod Measure.count) := by
  have hmap : Measurable (fun ω => (observe ω, bin ω)) := hobserve.prodMk hbin
  rw [← Measure.restrict_map hmap hG, hjoint, restrict_withDensity hG F,
    ← withDensity_indicator hG F, hpure, prod_withDensity_left hf,
    ← withDensity_smul c (f := fun z : X × β => f z.1) (hf.comp measurable_fst)]
  apply withDensity_mono
  apply Filter.Eventually.of_forall
  intro z
  by_cases hz : z ∈ G
  · simpa only [indicator_of_mem hz, Pi.smul_apply, smul_eq_mul] using hcap z hz
  · simp only [indicator_of_notMem hz, Pi.smul_apply, smul_eq_mul, zero_le]

/-- Apply the original angular ceiling to a finite list of labels after
all named masks. Neither the pure denominator nor its normalization moves. -/
theorem restricted_mass_le_angular_list_budget
    (μ : Measure Ω) [IsFiniteMeasure μ] (ref : Measure X)
    (observe : Ω → X) (bin : Ω → β) (hobserve : Measurable observe) (hbin : Measurable bin)
    (f : X → ENNReal) (F : X × β → ENNReal) (hf : Measurable f)
    (hpure : μ.map observe = ref.withDensity f)
    (hjoint : μ.map (fun ω => (observe ω, bin ω)) = (ref.prod Measure.count).withDensity F)
    (G : Set (X × β)) (hG : MeasurableSet G) (c D : ENNReal)
    (hcap : ∀ z ∈ G, F z ≤ c * f z.1)
    (L : X → Finset β) (hL : ∀ b, MeasurableSet {x | b ∈ L x})
    (hcard : ∀ x, (L x).card ≤ D)
    (hcover : ∀ᵐ ω ∂μ.restrict ((fun ω => (observe ω, bin ω)) ⁻¹' G),
      bin ω ∈ L (observe ω)) :
    μ.restrict ((fun ω => (observe ω, bin ω)) ⁻¹' G) Set.univ ≤
      (c * D) * μ Set.univ := by
  apply original_mass_le_list_budget μ _ observe bin hobserve hbin L hL c D hcard ?_ hcover
  exact restricted_joint_map_le μ ref observe bin hobserve hbin f F hf hpure hjoint G hG c hcap

/-- An arbitrary incidence restriction pays only the original exceptional
mask mass, in addition to its finite-list budget on the good mask. -/
theorem original_mass_le_angular_list_budget_with_bad
    (μ : Measure Ω) [IsFiniteMeasure μ] (ρ : Measure Ω) (hρ : ρ ≤ μ)
    (ref : Measure X) (observe : Ω → X) (bin : Ω → β)
    (hobserve : Measurable observe) (hbin : Measurable bin)
    (f : X → ENNReal) (F : X × β → ENNReal) (hf : Measurable f)
    (hpure : μ.map observe = ref.withDensity f)
    (hjoint : μ.map (fun ω => (observe ω, bin ω)) = (ref.prod Measure.count).withDensity F)
    (G : Set (X × β)) (hG : MeasurableSet G) (c D : ENNReal)
    (hcap : ∀ z ∈ G, F z ≤ c * f z.1)
    (L : X → Finset β) (hL : ∀ b, MeasurableSet {x | b ∈ L x})
    (hcard : ∀ x, (L x).card ≤ D)
    (hcover : ∀ᵐ ω ∂ρ, bin ω ∈ L (observe ω)) :
    ρ Set.univ ≤ (c * D) * μ Set.univ +
      μ ((fun ω => (observe ω, bin ω)) ⁻¹' G)ᶜ := by
  let event := (fun ω => (observe ω, bin ω)) ⁻¹' G
  have hmap : Measurable (fun ω => (observe ω, bin ω)) := hobserve.prodMk hbin
  have hevent : MeasurableSet event := hG.preimage hmap
  have hdom : (ρ.restrict event).map (fun ω => (observe ω, bin ω)) ≤
      c • ((μ.map observe).prod Measure.count) :=
    (Measure.map_mono (Measure.restrict_mono_measure hρ event) hmap).trans
      (restricted_joint_map_le μ ref observe bin hobserve hbin f F hf hpure hjoint G hG c hcap)
  have hbound := original_mass_le_list_budget μ (ρ.restrict event) observe bin hobserve hbin
    L hL c D hcard hdom (ae_restrict_of_ae hcover)
  have hgood : ρ event ≤ (c * D) * μ Set.univ := by
    simpa only [Measure.restrict_apply_univ] using hbound
  calc
    ρ Set.univ = ρ event + ρ eventᶜ := (measure_add_measure_compl hevent).symm
    _ ≤ (c * D) * μ Set.univ + μ eventᶜ := add_le_add hgood (hρ _)

end Submission.Obl.k4_scalar_guarded_entropic_path.WidthGeometry
