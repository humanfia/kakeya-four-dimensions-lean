/- Adapted from this LOT tree, obligation o218, session x0764, commit e1e41f8e737fdc1974cfdf32d18bbf69838b3ce8,
   Submission/Obl/k4_horizontal_endpoint_wide_return/ComparisonLabels.lean.
   Original source attributions are retained below. -/
import Submission.Obl.k4_subcritical_endpoint_native_pairing.FinitePairLabels

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing

open Set MeasureTheory

noncomputable def comparisonDomainEntries {ι Γ : Type*} (S : Finset ι)
    (domain : ι → Γ) (g : Γ) : Finset ι := by
  classical
  exact S.filter (fun i => domain i = g)

theorem mem_comparisonDomainEntries {ι Γ : Type*} (S : Finset ι)
    (domain : ι → Γ) (g : Γ) (i : ι) :
    i ∈ comparisonDomainEntries S domain g ↔ i ∈ S ∧ domain i = g := by
  classical
  exact Finset.mem_filter

/-- Replacing each domain's list by its actual fiber does not increase the
original reference budget, including when domains with empty lists are dropped. -/
theorem comparison_domain_reference_budget {ι Γ : Type*} (S : Finset ι)
    (domain : ι → Γ) (G : Finset Γ) (T : Γ → ENNReal) :
    (∑ g ∈ G, ((comparisonDomainEntries S domain g).card : ENNReal) * T g) ≤
      ∑ i ∈ S, T (domain i) := by
  classical
  calc
    _ = ∑ g ∈ G, ∑ i ∈ S with domain i = g, T (domain i) := by
      apply Finset.sum_congr rfl
      intro g hg
      calc
        _ = ∑ _i ∈ S.filter (fun i => domain i = g), T g := by
          simp only [comparisonDomainEntries, Finset.sum_const, nsmul_eq_mul]
        _ = _ := Finset.sum_congr rfl fun i hi => by
          rw [(Finset.mem_filter.mp hi).2]
    _ = ∑ i ∈ S with domain i ∈ G, T (domain i) :=
      Finset.sum_fiberwise_eq_sum_filter S G domain (fun i => T (domain i))
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- Only domains containing entries in both surviving lists are needed.
The new finite reader has exactly the old domain fiber laws. -/
theorem exists_common_active_domain_reader {Ω ι₁ ι₂ Γ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
    (μ : Measure Ω) (hμ : μ ≠ 0) (S₁ : Finset ι₁) (S₂ : Finset ι₂)
    (domain₁ : ι₁ → Γ) (domain₂ : ι₂ → Γ) (reader : Ω → Γ)
    (hreader : Measurable reader)
    (hcover : ∀ᵐ p ∂μ, ∃ i ∈ S₁, ∃ j ∈ S₂,
      domain₁ i = reader p ∧ domain₂ j = reader p) :
    ∃ (G : Finset Γ) (r : Ω → G), Measurable r ∧
      (∀ᵐ p ∂μ, (r p : Γ) = reader p) ∧
      (∀ g : G, (comparisonDomainEntries S₁ domain₁ g).Nonempty ∧
        (comparisonDomainEntries S₂ domain₂ g).Nonempty) ∧
      ∀ g : G, μ.restrict {p | r p = g} = μ.restrict {p | reader p = (g : Γ)} := by
  classical
  let G := (S₁.image domain₁) ∩ (S₂.image domain₂)
  have hGcover : ∀ᵐ p ∂μ, reader p ∈ G := by
    filter_upwards [hcover] with p hp
    obtain ⟨i, hi, j, hj, hdi, hdj⟩ := hp
    exact Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨i, hi, hdi⟩,
      Finset.mem_image.mpr ⟨j, hj, hdj⟩⟩
  have : (ae μ).NeBot := ae_neBot.mpr hμ
  obtain ⟨p, hp⟩ := hGcover.exists
  have : Nonempty G := ⟨⟨reader p, hp⟩⟩
  let E : G → Set Ω := fun g => {p | reader p = (g : Γ)}
  have hE : ∀ g, MeasurableSet (E g) := fun g => hreader (measurableSet_singleton _)
  have huniq : ∀ᵐ p ∂μ, ∀ g g', p ∈ E g → p ∈ E g' → g = g' := by
    filter_upwards [] with p g g' hg hg'
    exact Subtype.ext (hg.symm.trans hg')
  have hc : ∀ᵐ p ∂μ, ∃ g, p ∈ E g := by
    filter_upwards [hGcover] with p hp
    exact ⟨⟨reader p, hp⟩, rfl⟩
  obtain ⟨r, hr, hae, hfib⟩ := exists_measurable_pair_labels μ E hE huniq hc
  refine ⟨G, r, hr, ?_, ?_, hfib⟩
  · filter_upwards [hae] with p hp
    exact ((hp (r p)).mp rfl).symm
  · intro g
    obtain ⟨h₁, h₂⟩ := Finset.mem_inter.mp g.property
    obtain ⟨i, hi, hdi⟩ := Finset.mem_image.mp h₁
    obtain ⟨j, hj, hdj⟩ := Finset.mem_image.mp h₂
    exact ⟨⟨i, (mem_comparisonDomainEntries _ _ _ _).mpr ⟨hi, hdi⟩⟩,
      ⟨j, (mem_comparisonDomainEntries _ _ _ _).mpr ⟨hj, hdj⟩⟩⟩

/-- Reindex one original surviving list inside a domain. The selector is
measurable and its marginal masses are the entire original entry masses. -/
theorem exists_measurable_domain_entry_labels {Ω ι Γ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace ι] [MeasurableSpace Γ]
    [MeasurableSingletonClass Γ]
    (μ : Measure Ω) (S : Finset ι) (domain : ι → Γ) (reader : Ω → Γ)
    (hreader : Measurable reader) (E : ι → Set Ω)
    (hE : ∀ i, MeasurableSet (E i))
    (hsub : ∀ i ∈ S, E i ⊆ {p | reader p = domain i})
    (hunique : ∀ᵐ p ∂μ, ∀ i ∈ S, ∀ j ∈ S, p ∈ E i → p ∈ E j → i = j)
    (hcover : ∀ᵐ p ∂μ, ∃ i ∈ S, p ∈ E i)
    (g : Γ) (hg : (comparisonDomainEntries S domain g).Nonempty) :
    ∃ f : Ω → comparisonDomainEntries S domain g, Measurable f ∧
      (∀ᵐ p ∂μ.restrict {p | reader p = g}, p ∈ E (f p)) ∧
      ∀ i : comparisonDomainEntries S domain g,
        (μ.restrict {p | reader p = g}) {p | f p = i} = μ (E i) := by
  classical
  obtain ⟨i₀, hi₀⟩ := hg
  have : Nonempty (comparisonDomainEntries S domain g) := ⟨⟨i₀, hi₀⟩⟩
  let μg := μ.restrict {p | reader p = g}
  let Eg : comparisonDomainEntries S domain g → Set Ω := fun i => E i
  have hgmeas : MeasurableSet {p | reader p = g} := hreader (measurableSet_singleton g)
  have huniq : ∀ᵐ p ∂μg, ∀ i j, p ∈ Eg i → p ∈ Eg j → i = j := by
    filter_upwards [hunique.filter_mono (ae_mono Measure.restrict_le_self)] with p hp i j hi hj
    apply Subtype.ext
    exact hp i ((mem_comparisonDomainEntries _ _ _ _).mp i.property).1
      j ((mem_comparisonDomainEntries _ _ _ _).mp j.property).1 hi hj
  have hc : ∀ᵐ p ∂μg, ∃ i, p ∈ Eg i := by
    filter_upwards [hcover.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem hgmeas] with p hp hpg
    obtain ⟨i, hi, hpi⟩ := hp
    have hdi : domain i = g := (hsub i hi hpi).symm.trans hpg
    exact ⟨⟨i, (mem_comparisonDomainEntries _ _ _ _).mpr ⟨hi, hdi⟩⟩, hpi⟩
  obtain ⟨f, hf, hae, hfib⟩ := exists_measurable_pair_labels μg Eg (fun i => hE i) huniq hc
  refine ⟨f, hf, ?_, ?_⟩
  · filter_upwards [hae] with p hp
    exact (hp (f p)).mp rfl
  · intro i
    have heq := congrArg (fun m : Measure Ω => m univ) (hfib i)
    simp only [Measure.restrict_apply_univ] at heq
    change μg {p | f p = i} = μ (E i)
    rw [heq, Measure.restrict_apply (hE i)]
    congr 1
    apply inter_eq_left.mpr
    intro p hp
    obtain ⟨hi, hdi⟩ := (mem_comparisonDomainEntries _ _ _ _).mp i.property
    exact (hsub i hi hp).trans hdi

end Submission.Obl.k4_subcritical_endpoint_native_pairing
