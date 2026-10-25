import Mathlib
import Submission.Lib.K4ScalarActualSwitching.PaletteConditioning

/-!
# Simultaneous final-law floors and common-time restoration

Finite overlapping labels can be pruned against earlier reference weights with
all floors measured under one final restriction. A selected trajectory can also
provide a common set of times on which all incidence trajectories are restored.
Earlier-history reference weights also descend to native states through finite state lists.

Adapted from: here:o218 (session x0760),
`Submission/Obl/k4_horizontal_endpoint_wide_return/SimultaneousFloors.lean` and
`Submission/Obl/k4_horizontal_endpoint_wide_return/TimeRestoration.lean` and
`Submission/Obl/k4_horizontal_endpoint_wide_return/HistoryPalette.lean` and
`Submission/Obl/k4_horizontal_endpoint_wide_return/FinalPalette.lean` and
`Submission/Obl/k4_horizontal_endpoint_wide_return/JointPruning.lean`.
The palette normalization calculation extends the accepted
`Submission/Lib/K4ReferencePruning.lean` argument to an arbitrary final submeasure.
-/

namespace Submission.Lib.K4FinalLawSelection

open MeasureTheory Set
open scoped ENNReal

/-- Prune all light entries against fixed reference weights at once. The floors
are measured under the final restriction, including after other layers were pruned. -/
theorem simultaneous_reference_floors {Ω ι : Type*} [MeasurableSpace Ω]
    (s : Finset ι) (E : ι → Set Ω) (hE : ∀ i, MeasurableSet (E i))
    (w : ι → ENNReal) (μ : Measure Ω) :
    ∃ G : Set Ω, MeasurableSet G ∧ μ Gᶜ ≤ ∑ i ∈ s, w i ∧
      ∀ i ∈ s, (μ.restrict G) (E i) = 0 ∨ w i ≤ (μ.restrict G) (E i) := by
  classical
  revert μ
  refine Finset.strongInductionOn s ?_
  intro s ih μ
  by_cases hall : ∀ i ∈ s, w i ≤ μ (E i)
  · refine ⟨univ, MeasurableSet.univ, by simp, ?_⟩
    intro i hi
    exact Or.inr (by simpa using hall i hi)
  · push Not at hall
    obtain ⟨i, hi, hlight⟩ := hall
    obtain ⟨G, hG, hloss, hgood⟩ :=
      ih (s.erase i) (Finset.erase_ssubset hi) (μ.restrict (E i)ᶜ)
    refine ⟨G ∩ (E i)ᶜ, hG.inter (hE i).compl, ?_, ?_⟩
    · have hcover : (G ∩ (E i)ᶜ)ᶜ ⊆ E i ∪ (Gᶜ ∩ (E i)ᶜ) := by
        intro p hp
        by_cases hpi : p ∈ E i
        · exact Or.inl hpi
        · exact Or.inr ⟨fun hpG => hp ⟨hpG, hpi⟩, hpi⟩
      calc
        μ (G ∩ (E i)ᶜ)ᶜ ≤ μ (E i ∪ (Gᶜ ∩ (E i)ᶜ)) := measure_mono hcover
        _ ≤ μ (E i) + μ (Gᶜ ∩ (E i)ᶜ) := measure_union_le _ _
        _ = μ (E i) + (μ.restrict (E i)ᶜ) Gᶜ := by
          rw [Measure.restrict_apply hG.compl]
        _ ≤ w i + ∑ j ∈ s.erase i, w j := add_le_add hlight.le hloss
        _ = ∑ j ∈ s, w j := Finset.add_sum_erase _ _ hi
    · intro j hj
      by_cases hji : j = i
      · subst j
        left
        rw [Measure.restrict_apply (hE i)]
        have hempty : E i ∩ (G ∩ (E i)ᶜ) = ∅ := by
          ext p; simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false]; tauto
        rw [hempty, measure_empty]
      · have hgoodj := hgood j (Finset.mem_erase.mpr ⟨hji, hj⟩)
        rw [Measure.restrict_restrict hG] at hgoodj
        exact hgoodj

/-- The simultaneous pruning is a restriction of the original law and charges
its entire deletion to the sum of the old reference weights. -/
theorem exists_simultaneous_floor_measure {Ω ι : Type*} [MeasurableSpace Ω]
    (s : Finset ι) (E : ι → Set Ω) (hE : ∀ i, MeasurableSet (E i))
    (w : ι → ENNReal) (μ : Measure Ω) :
    ∃ ρ : Measure Ω, ρ ≤ μ ∧ μ univ ≤ ρ univ + ∑ i ∈ s, w i ∧
      ∀ i ∈ s, ρ (E i) = 0 ∨ w i ≤ ρ (E i) := by
  obtain ⟨G, hG, hloss, hgood⟩ := simultaneous_reference_floors s E hE w μ
  refine ⟨μ.restrict G, Measure.restrict_le_self, ?_, hgood⟩
  rw [Measure.restrict_apply_univ]
  calc
    μ univ = μ G + μ Gᶜ := (measure_add_measure_compl hG).symm
    _ ≤ μ G + ∑ i ∈ s, w i := add_le_add le_rfl hloss

/-- If an original finite layer covers the law, the surviving heavy entries
still cover the final law. This works with several layers by using disjoint index types. -/
theorem simultaneous_floor_support {Ω ι : Type*} [MeasurableSpace Ω]
    (s : Finset ι) (E : ι → Set Ω) (hE : ∀ i, MeasurableSet (E i))
    (w : ι → ENNReal) (μ : Measure Ω)
    (hcover : ∀ᵐ p ∂μ, ∃ i ∈ s, p ∈ E i) :
    ∃ (ρ : Measure Ω) (S : Finset ι),
      ρ ≤ μ ∧ μ univ ≤ ρ univ + ∑ i ∈ s, w i ∧ S ⊆ s ∧
      (∀ i ∈ S, w i ≤ ρ (E i)) ∧ (∀ᵐ p ∂ρ, ∃ i ∈ S, p ∈ E i) := by
  classical
  obtain ⟨ρ, hρ, hloss, hgood⟩ := exists_simultaneous_floor_measure s E hE w μ
  let S := s.filter (fun i => w i ≤ ρ (E i))
  refine ⟨ρ, S, hρ, hloss, Finset.filter_subset _ _, ?_, ?_⟩
  · intro i hi
    exact (Finset.mem_filter.mp hi).2
  · have htrace : ∀ᵐ p ∂ρ, ∀ i : s, p ∈ E i → w i ≤ ρ (E i) := by
      apply ae_all_iff.mpr
      intro i
      rcases hgood i i.property with hz | hh
      · have hnot : ∀ᵐ p ∂ρ, p ∉ E i := by
          rw [ae_iff]
          simpa only [not_not, Set.ofPred_mem_eq] using hz
        filter_upwards [hnot] with p hp
        exact fun hmem => (hp hmem).elim
      · exact Filter.Eventually.of_forall (fun p _ => hh)
    filter_upwards [hcover.filter_mono (ae_mono hρ), htrace] with p hp htrace
    obtain ⟨i, hi, hpi⟩ := hp
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, htrace ⟨i, hi⟩ hpi⟩, hpi⟩


/-- One trajectory supplies a set of times on which restoring every paired
trajectory retains dense mass. The law remains the original unnormalized law. -/
theorem exists_restored_fiber {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure α) (τ : Measure β) [IsProbabilityMeasure ν] [IsProbabilityMeasure τ]
    (μ : Measure (α × β)) {K m : ℝ} (hK : 0 < K) (hm : 0 < m)
    (hdom : μ ≤ ENNReal.ofReal K • (ν.prod τ))
    (hmass : ENNReal.ofReal m ≤ μ univ)
    (E : Set (α × β)) (hE : MeasurableSet E) (hfull : μ Eᶜ = 0) :
    ∃ a : α, MeasurableSet (Prod.mk a ⁻¹' E) ∧
      ENNReal.ofReal (m ^ 2 / (4 * K)) ≤ μ (Prod.snd ⁻¹' (Prod.mk a ⁻¹' E)) := by
  let δ : ℝ := m / (2 * K)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let f : β → ENNReal := fun t => ν {a | (a, t) ∈ E}
  have hf : Measurable f := measurable_measure_prodMk_right hE
  let H : Set β := {t | ENNReal.ofReal δ ≤ f t}
  have hH : MeasurableSet H := measurableSet_le measurable_const hf
  have hpreH : MeasurableSet (Prod.snd ⁻¹' H : Set (α × β)) := hH.preimage measurable_snd
  have hpreHc : MeasurableSet (Prod.snd ⁻¹' Hᶜ : Set (α × β)) := hH.compl.preimage measurable_snd
  have hμfin : μ univ < ∞ := by
    calc
      μ univ ≤ (ENNReal.ofReal K • (ν.prod τ)) univ := hdom _
      _ = ENNReal.ofReal K := by simp
      _ < ∞ := ENNReal.ofReal_lt_top
  have : IsFiniteMeasure μ := ⟨hμfin⟩
  have hprodlight : (ν.prod τ) (E ∩ (Prod.snd ⁻¹' Hᶜ)) ≤ ENNReal.ofReal δ := by
    rw [Measure.prod_apply_symm (hE.inter hpreHc)]
    calc
      _ ≤ ∫⁻ _t : β, ENNReal.ofReal δ ∂τ := by
        apply lintegral_mono
        intro t
        change ν ((fun a : α => (a, t)) ⁻¹' (E ∩ (Prod.snd ⁻¹' Hᶜ))) ≤ ENNReal.ofReal δ
        by_cases ht : t ∈ H
        · have hempty : (fun a : α => (a, t)) ⁻¹' (E ∩ (Prod.snd ⁻¹' Hᶜ)) = ∅ := by
            ext a; simp [ht]
          rw [hempty, measure_empty]
          exact zero_le
        · have heq : (fun a : α => (a, t)) ⁻¹' (E ∩ (Prod.snd ⁻¹' Hᶜ)) = {a | (a, t) ∈ E} := by
            ext a; simp [ht]
          rw [heq]
          exact (lt_of_not_ge ht).le
      _ = ENNReal.ofReal δ := by simp
  have hlight : μ (Prod.snd ⁻¹' Hᶜ) ≤ ENNReal.ofReal (m / 2) := by
    have heq : μ (Prod.snd ⁻¹' Hᶜ) = μ (E ∩ (Prod.snd ⁻¹' Hᶜ)) := by
      apply measure_congr
      have hEa : ∀ᵐ p ∂μ, p ∈ E := by
        rw [ae_iff]
        exact hfull
      filter_upwards [hEa] with p hp
      simp only [mem_inter_iff, hp, true_and]
    rw [heq]
    calc
      _ ≤ ENNReal.ofReal K * (ν.prod τ) (E ∩ (Prod.snd ⁻¹' Hᶜ)) := hdom _
      _ ≤ ENNReal.ofReal K * ENNReal.ofReal δ := mul_le_mul' le_rfl hprodlight
      _ = ENNReal.ofReal (m / 2) := by
        rw [← ENNReal.ofReal_mul hK.le]
        congr 1
        dsimp [δ]
        field_simp
  have hheavy : ENNReal.ofReal (m / 2) ≤ μ (Prod.snd ⁻¹' H) := by
    have hsplit : ENNReal.ofReal m = ENNReal.ofReal (m / 2) + ENNReal.ofReal (m / 2) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    have hcover : μ univ ≤ μ (Prod.snd ⁻¹' H) + ENNReal.ofReal (m / 2) := by
      calc
        μ univ = μ (Prod.snd ⁻¹' H) + μ (Prod.snd ⁻¹' H)ᶜ :=
          (measure_add_measure_compl hpreH).symm
        _ ≤ μ (Prod.snd ⁻¹' H) + ENNReal.ofReal (m / 2) := add_le_add le_rfl hlight
    have hh := hmass.trans hcover
    rw [hsplit] at hh
    exact ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top hh
  let σ : Measure β := μ.map Prod.snd
  have hσH : σ H = μ (Prod.snd ⁻¹' H) := Measure.map_apply measurable_snd hH
  have hσuniv : σ univ = μ univ := by
    change (μ.map Prod.snd) univ = μ univ
    rw [Measure.map_apply measurable_snd MeasurableSet.univ]
    rfl
  have : IsFiniteMeasure σ := ⟨by rw [hσuniv]; exact hμfin⟩
  have hpair : ENNReal.ofReal (m ^ 2 / (4 * K)) ≤ (ν.prod σ) E := by
    rw [Measure.prod_apply_symm hE]
    calc
      ENNReal.ofReal (m ^ 2 / (4 * K)) = ENNReal.ofReal δ * ENNReal.ofReal (m / 2) := by
        rw [← ENNReal.ofReal_mul hδ.le]
        congr 1
        dsimp [δ]
        field_simp
        ring
      _ ≤ ENNReal.ofReal δ * σ H := mul_le_mul' le_rfl (by rwa [hσH])
      _ = ∫⁻ t, H.indicator (fun _ => ENNReal.ofReal δ) t ∂σ := by
        rw [lintegral_indicator hH]
        simp
      _ ≤ ∫⁻ t, f t ∂σ := by
        apply lintegral_mono
        intro t
        by_cases ht : t ∈ H
        · rw [Set.indicator_of_mem ht]
          exact ht
        · simp only [Set.indicator_of_notMem ht]
          exact zero_le
  have havgfin : (∫⁻ a, σ (Prod.mk a ⁻¹' E) ∂ν) ≠ ∞ := by
    apply ne_of_lt
    calc
      _ ≤ ∫⁻ _a : α, σ univ ∂ν := lintegral_mono (fun _ => measure_mono (subset_univ _))
      _ = σ univ := by simp
      _ < ∞ := measure_lt_top _ _
  obtain ⟨a, -, ha⟩ := exists_notMem_null_lintegral_le havgfin (measure_empty : ν (∅ : Set α) = 0)
  refine ⟨a, hE.preimage (measurable_const.prodMk measurable_id), ?_⟩
  have hbound : ENNReal.ofReal (m ^ 2 / (4 * K)) ≤ σ (Prod.mk a ⁻¹' E) := by
    rw [Measure.prod_apply hE] at hpair
    exact hpair.trans ha
  have hEa : MeasurableSet (Prod.mk a ⁻¹' E) :=
    hE.preimage (measurable_const.prodMk measurable_id)
  change ENNReal.ofReal (m ^ 2 / (4 * K)) ≤ (μ.map Prod.snd) (Prod.mk a ⁻¹' E) at hbound
  rwa [Measure.map_apply measurable_snd hEa] at hbound

/-- The same common time set has a positive mass under the reference time law. -/
theorem exists_restored_fiber_with_prior {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure α) (τ : Measure β) [IsProbabilityMeasure ν] [IsProbabilityMeasure τ]
    (μ : Measure (α × β)) {K m : ℝ} (hK : 0 < K) (hm : 0 < m)
    (hdom : μ ≤ ENNReal.ofReal K • (ν.prod τ))
    (hmass : ENNReal.ofReal m ≤ μ univ)
    (E : Set (α × β)) (hE : MeasurableSet E) (hfull : μ Eᶜ = 0) :
    ∃ a : α, MeasurableSet (Prod.mk a ⁻¹' E) ∧
      ENNReal.ofReal (m ^ 2 / (4 * K ^ 2)) ≤ τ (Prod.mk a ⁻¹' E) ∧
      ENNReal.ofReal (m ^ 2 / (4 * K)) ≤ μ (Prod.snd ⁻¹' (Prod.mk a ⁻¹' E)) := by
  obtain ⟨a, hEa, hrestore⟩ := exists_restored_fiber ν τ μ hK hm hdom hmass E hE hfull
  refine ⟨a, hEa, ?_, hrestore⟩
  have hcap : μ (Prod.snd ⁻¹' (Prod.mk a ⁻¹' E)) ≤
      ENNReal.ofReal K * τ (Prod.mk a ⁻¹' E) := by
    have heq : (Prod.snd ⁻¹' (Prod.mk a ⁻¹' E) : Set (α × β)) =
        univ ×ˢ (Prod.mk a ⁻¹' E) := by ext p; simp
    calc
      _ ≤ (ENNReal.ofReal K • (ν.prod τ)) (Prod.snd ⁻¹' (Prod.mk a ⁻¹' E)) := hdom _
      _ = ENNReal.ofReal K * τ (Prod.mk a ⁻¹' E) := by
        rw [Measure.smul_apply, heq, Measure.prod_prod, measure_univ, one_mul]
        rfl
  have heq : m ^ 2 / (4 * K ^ 2) = (m ^ 2 / (4 * K)) / K := by
    field_simp
  rw [heq, ENNReal.ofReal_div_of_pos hK,
    ENNReal.div_le_iff (ne_of_gt (ENNReal.ofReal_pos.mpr hK)) ENNReal.ofReal_ne_top]
  simpa only [mul_comm] using hrestore.trans hcap


/-- Product domination and time support pass to the restricted reference time law.
This supplies a probability time prior on the unit interval without changing μ. -/
theorem dominated_restrict_time {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure α) (τ : Measure β) [SFinite ν] [SFinite τ]
    (μ : Measure (α × β)) (c : ENNReal) (S : Set β)
    (hdom : μ ≤ c • (ν.prod τ)) (hfull : μ (univ ×ˢ S)ᶜ = 0) :
    μ ≤ c • (ν.prod (τ.restrict S)) := by
  have hs : ∀ᵐ p ∂μ, p ∈ univ ×ˢ S := by
    rw [ae_iff]
    exact hfull
  calc
    μ = μ.restrict (univ ×ˢ S) := (Measure.restrict_eq_self_of_ae_mem hs).symm
    _ ≤ (c • (ν.prod τ)).restrict (univ ×ˢ S) := Measure.restrict_mono_measure hdom _
    _ = c • (ν.prod (τ.restrict S)) := by
      rw [Measure.restrict_smul, ← Measure.prod_restrict, Measure.restrict_univ]

/-- One common restriction preserves heavy-entry coverage separately in every
layer; events in different layers may intersect arbitrarily. -/
theorem simultaneous_floor_layers {Ω ι Q : Type*} [MeasurableSpace Ω]
    (s : Finset ι) (E : ι → Set Ω) (hE : ∀ i, MeasurableSet (E i))
    (w : ι → ENNReal) (μ : Measure Ω) (layer : Q → ι → Prop)
    (hcover : ∀ q, ∀ᵐ p ∂μ, ∃ i ∈ s, layer q i ∧ p ∈ E i) :
    ∃ (ρ : Measure Ω) (S : Finset ι),
      ρ ≤ μ ∧ μ univ ≤ ρ univ + ∑ i ∈ s, w i ∧ S ⊆ s ∧
      (∀ i ∈ S, w i ≤ ρ (E i)) ∧
      ∀ q, ∀ᵐ p ∂ρ, ∃ i ∈ S, layer q i ∧ p ∈ E i := by
  classical
  obtain ⟨ρ, hρ, hloss, hgood⟩ := exists_simultaneous_floor_measure s E hE w μ
  let S := s.filter (fun i => w i ≤ ρ (E i))
  refine ⟨ρ, S, hρ, hloss, Finset.filter_subset _ _, ?_, ?_⟩
  · exact fun i hi => (Finset.mem_filter.mp hi).2
  · have htrace : ∀ᵐ p ∂ρ, ∀ i : s, p ∈ E i → w i ≤ ρ (E i) := by
      apply ae_all_iff.mpr
      intro i
      rcases hgood i i.property with hz | hh
      · have hnot : ∀ᵐ p ∂ρ, p ∉ E i := by
          rw [ae_iff]
          simpa only [not_not, Set.ofPred_mem_eq] using hz
        filter_upwards [hnot] with p hp
        exact fun hmem => (hp hmem).elim
      · exact Filter.Eventually.of_forall (fun p _ => hh)
    intro q
    filter_upwards [(hcover q).filter_mono (ae_mono hρ), htrace] with p hp htrace
    obtain ⟨i, hi, hqi, hpi⟩ := hp
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, htrace ⟨i, hi⟩ hpi⟩, hqi, hpi⟩

/-- The earlier-history weights whose state lists contain a given native state. -/
noncomputable def historyStateWeight {ι Q : Type*} [Fintype ι]
    (options : ι → Finset Q) (w : ι → ENNReal) (q : Q) : ENNReal := by
  classical
  exact ∑ h, if q ∈ options h then w h else 0

/-- A bounded number of native states per earlier history preserves the total
reference budget, with no projected predictor label added to the state. -/
theorem historyStateWeight_budget {ι Q : Type*} [Fintype ι] [Fintype Q]
    (options : ι → Finset Q) (w : ι → ENNReal) (L : ℕ)
    (hL : ∀ h, (options h).card ≤ L) :
    (∑ q, historyStateWeight options w q) ≤ (L : ENNReal) * ∑ h, w h := by
  classical
  unfold historyStateWeight
  rw [Finset.sum_comm]
  calc
    _ = ∑ h, ((options h).card : ENNReal) * w h := by
      apply Finset.sum_congr rfl
      intro h _
      simp
    _ ≤ ∑ h, (L : ENNReal) * w h := by
      apply Finset.sum_le_sum
      intro h _
      exact mul_le_mul' (by exact_mod_cast hL h) le_rfl
    _ = (L : ENNReal) * ∑ h, w h := (Finset.mul_sum _ _ _).symm

/-- The persistent palette numerators descend from earlier histories to native
states. Conditioning on projected predictor labels is never required. -/
theorem native_state_palette_cap {Ω ι Q V : Type*}
    [MeasurableSpace Ω] [MeasurableSpace V] [Fintype ι]
    (μ : Measure Ω) (π : Measure V) (control : Ω → V) (state : Ω → Q)
    (H : ι → Set Ω) (options : ι → Finset Q) (w : ι → ENNReal) (C : ENNReal)
    (hcover : ∀ᵐ p ∂μ, ∃ h, p ∈ H h)
    (hoptions : ∀ h, ∀ᵐ p ∂μ, p ∈ H h → state p ∈ options h)
    (hcap : ∀ h (A : Set V), MeasurableSet A →
      μ {p | p ∈ H h ∧ control p ∈ A} ≤ C * w h * π A) :
    ∀ q (A : Set V), MeasurableSet A →
      μ {p | state p = q ∧ control p ∈ A} ≤ C * historyStateWeight options w q * π A := by
  classical
  intro q A hA
  let I := Finset.univ.filter (fun h => q ∈ options h)
  have htrace : ∀ᵐ p ∂μ, ∀ h, p ∈ H h → state p ∈ options h := ae_all_iff.mpr hoptions
  have hsub : {p | state p = q ∧ control p ∈ A} ≤ᵐ[μ]
      ⋃ h ∈ I, {p | p ∈ H h ∧ control p ∈ A} := by
    filter_upwards [hcover, htrace] with p hp htrace
    rintro ⟨hpq, hpA⟩
    obtain ⟨h, hph⟩ := hp
    have hq : q ∈ options h := by simpa only [hpq] using htrace h hph
    exact mem_biUnion (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩) ⟨hph, hpA⟩
  have hweights : (∑ h ∈ I, w h) = historyStateWeight options w q := by
    simp [I, historyStateWeight, Finset.sum_filter]
  calc
    _ ≤ μ (⋃ h ∈ I, {p | p ∈ H h ∧ control p ∈ A}) := measure_mono_ae hsub
    _ ≤ ∑ h ∈ I, μ {p | p ∈ H h ∧ control p ∈ A} := measure_biUnion_finset_le _ _
    _ ≤ ∑ h ∈ I, C * w h * π A := Finset.sum_le_sum (fun h _ => hcap h A hA)
    _ = C * (∑ h ∈ I, w h) * π A := by rw [Finset.mul_sum, Finset.sum_mul]
    _ = C * historyStateWeight options w q * π A := by rw [hweights]


/-- Normalize persistent palette numerators using floors under an arbitrary
final submeasure. This includes common pruning of several projected layers.
The normalization calculation follows K4ReferencePruning.reference_pruned_palette_cap;
here the final law need not be the one-pass referenceKeep restriction. -/
theorem palette_cap_of_final_floors {Ω Q V : Type*}
    [MeasurableSpace Ω] [MeasurableSpace V]
    (μ ρ : Measure Ω) (hρ : ρ ≤ μ) (state : Ω → Q) (control : Ω → V)
    (π : Measure V) (w : Q → ENNReal) (C δ : ENNReal)
    (hδ0 : δ ≠ 0) (hδtop : δ ≠ ⊤)
    (hfloors : ∀ q, ρ (state ⁻¹' {q}) = 0 ∨ δ * w q ≤ ρ (state ⁻¹' {q}))
    (hcap : ∀ q (A : Set V), MeasurableSet A →
      μ {p | state p = q ∧ control p ∈ A} ≤ C * w q * π A) :
    ∀ q (A : Set V), MeasurableSet A →
      ρ {p | state p = q ∧ control p ∈ A} ≤
        (C / δ) * ρ (state ⁻¹' {q}) * π A := by
  intro q A hA
  rcases hfloors q with hzero | hfloor
  · calc
      _ ≤ ρ (state ⁻¹' {q}) := measure_mono (fun p hp => hp.1)
      _ = 0 := hzero
      _ ≤ _ := zero_le
  · have href : w q ≤ δ⁻¹ * ρ (state ⁻¹' {q}) := by
      calc
        w q = δ⁻¹ * (δ * w q) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hδ0 hδtop, one_mul]
        _ ≤ δ⁻¹ * ρ (state ⁻¹' {q}) := mul_le_mul' le_rfl hfloor
    calc
      _ ≤ μ {p | state p = q ∧ control p ∈ A} := hρ _
      _ ≤ C * w q * π A := hcap q A hA
      _ ≤ C * (δ⁻¹ * ρ (state ⁻¹' {q})) * π A := by gcongr
      _ = _ := by rw [div_eq_mul_inv]; ac_rfl

/-- Final-law floors give an exact conditional palette bound. In the frozen
asymptotic problem, V is the chosen discrete velocity grid and π its pushed-forward
palette; no absolute-continuity assertion for the raw velocity is required. -/
theorem conditional_palette_of_final_floors {Ω Q V : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    [MeasurableSpace V] [StandardBorelSpace V] [Nonempty V]
    (μ ρ : Measure Ω) [IsFiniteMeasure ρ] (hρ : ρ ≤ μ)
    (state : Ω → Q) (hstate : Measurable state)
    (control : Ω → V) (hcontrol : Measurable control)
    (π : Measure V) (w : Q → ENNReal) (C δ : ENNReal)
    (hδ0 : δ ≠ 0) (hδtop : δ ≠ ⊤)
    (hfloors : ∀ q, ρ (state ⁻¹' {q}) = 0 ∨ δ * w q ≤ ρ (state ⁻¹' {q}))
    (hcap : ∀ q (A : Set V), MeasurableSet A →
      μ {p | state p = q ∧ control p ∈ A} ≤ C * w q * π A) :
    ∀ᵐ q ∂ρ.map state,
      ProbabilityTheory.condDistrib control state ρ q ≤ (C / δ) • π := by
  apply Submission.Lib.K4ScalarActualSwitching.condDistrib_palette_le
    ρ state hstate control hcontrol π (C / δ)
  exact palette_cap_of_final_floors μ ρ hρ state control π w C δ hδ0 hδtop hfloors hcap


/-- The budget also holds on arbitrary finite subsets of an infinite native state space. -/
theorem historyStateWeight_finset_budget {ι Q : Type*} [Fintype ι]
    (options : ι → Finset Q) (w : ι → ENNReal) (S : Finset Q) (L : ℕ)
    (hL : ∀ h, (options h).card ≤ L) :
    (∑ q ∈ S, historyStateWeight options w q) ≤ (L : ENNReal) * ∑ h, w h := by
  classical
  unfold historyStateWeight
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ h, ((options h).card : ENNReal) * w h := by
      apply Finset.sum_le_sum
      intro h _
      calc
        _ = ∑ _q ∈ S.filter (fun q => q ∈ options h), w h := by rw [Finset.sum_filter]
        _ ≤ ∑ _q ∈ options h, w h := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro q hq
            exact (Finset.mem_filter.mp hq).2
          · intros; exact zero_le
        _ = _ := by simp
    _ ≤ ∑ h, (L : ENNReal) * w h := by
      apply Finset.sum_le_sum
      intro h _
      exact mul_le_mul' (by exact_mod_cast hL h) le_rfl
    _ = (L : ENNReal) * ∑ h, w h := (Finset.mul_sum _ _ _).symm

/-- A finite earlier-history family gives a summable native-state reference budget,
including when native states are integer tuples rather than a finite type. -/
theorem historyStateWeight_tsum_budget {ι Q : Type*} [Fintype ι]
    (options : ι → Finset Q) (w : ι → ENNReal) (L : ℕ)
    (hL : ∀ h, (options h).card ≤ L) :
    (∑' q, historyStateWeight options w q) ≤ (L : ENNReal) * ∑ h, w h := by
  classical
  let S := Finset.univ.biUnion options
  have hout : ∀ q ∉ S, historyStateWeight options w q = 0 := by
    intro q hq
    unfold historyStateWeight
    apply Finset.sum_eq_zero
    intro h _
    apply if_neg
    intro hmem
    exact hq (Finset.mem_biUnion.mpr ⟨h, Finset.mem_univ _, hmem⟩)
  rw [tsum_eq_sum hout]
  exact historyStateWeight_finset_budget options w S L hL

/-- Common event floors and native-state palette normalization are obtained
under one final law. Native states may be integer tuples; only the active
state set must be finite. The palette retains its original reference weights. -/
theorem exists_joint_floors_and_palette {Ω ι Q V : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    [MeasurableSpace V] [StandardBorelSpace V] [Nonempty V]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (E : ι → Set Ω) (hE : ∀ i, MeasurableSet (E i)) (wE : ι → ENNReal)
    (state : Ω → Q) (hstate : Measurable state) (S : Finset Q)
    (hS : ∀ᵐ p ∂μ, state p ∈ S)
    (control : Ω → V) (hcontrol : Measurable control) (π : Measure V)
    (w : Q → ENNReal) (C δ : ENNReal) (hδ0 : δ ≠ 0) (hδtop : δ ≠ ⊤)
    (hcap : ∀ q (A : Set V), MeasurableSet A →
      μ {p | state p = q ∧ control p ∈ A} ≤ C * w q * π A) :
    ∃ (ρ : Measure Ω) (hρ : ρ ≤ μ),
      letI := isFiniteMeasure_of_le μ hρ
      μ univ ≤ ρ univ + ((∑ i, wE i) + δ * ∑ q ∈ S, w q) ∧
      (∀ i, ρ (E i) = 0 ∨ wE i ≤ ρ (E i)) ∧
      (∀ q, ρ (state ⁻¹' {q}) = 0 ∨ δ * w q ≤ ρ (state ⁻¹' {q})) ∧
      (∀ᵐ q ∂ρ.map state, ProbabilityTheory.condDistrib control state ρ q ≤ (C / δ) • π) := by
  classical
  let events : ι ⊕ Q → Set Ω := Sum.elim E (fun q => state ⁻¹' {q})
  let weights : ι ⊕ Q → ENNReal := Sum.elim wE (fun q => δ * w q)
  have hevents : ∀ j, MeasurableSet (events j) := by
    intro j
    cases j with
    | inl i => exact hE i
    | inr q => exact hstate (measurableSet_singleton q)
  obtain ⟨ρ, hρ, hloss, hfloor⟩ := exists_simultaneous_floor_measure
    (Finset.univ.disjSum S) events hevents weights μ
  have hstatefloor : ∀ q, ρ (state ⁻¹' {q}) = 0 ∨ δ * w q ≤ ρ (state ⁻¹' {q}) := by
    intro q
    by_cases hq : q ∈ S
    · exact hfloor (Sum.inr q) (by simp [hq])
    · left
      have hnot : ∀ᵐ p ∂ρ, p ∉ state ⁻¹' {q} := by
        filter_upwards [hS.filter_mono (ae_mono hρ)] with p hp
        intro hpq
        change state p = q at hpq
        rw [hpq] at hp
        exact hq hp
      rw [ae_iff] at hnot
      simpa only [not_not, Set.ofPred_mem_eq] using hnot
  haveI : IsFiniteMeasure ρ := isFiniteMeasure_of_le μ hρ
  refine ⟨ρ, hρ, ?_, ?_, hstatefloor, ?_⟩
  · simpa [weights, Finset.sum_disjSum, Finset.mul_sum] using hloss
  · intro i
    exact hfloor (Sum.inl i) (by simp)
  · exact conditional_palette_of_final_floors μ ρ hρ state hstate control hcontrol π w C δ
      hδ0 hδtop hstatefloor hcap

end Submission.Lib.K4FinalLawSelection
