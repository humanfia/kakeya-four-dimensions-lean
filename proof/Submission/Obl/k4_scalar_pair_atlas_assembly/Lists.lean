import Mathlib

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_pair_atlas_assembly

open MeasureTheory Set

noncomputable section

/-- A fixed finite compatibility table transports the old observation list. -/
def transportList {β γ X : Type*} [DecidableEq γ]
    (Λ : X → Finset β) (R : β → Finset γ) (z : X) : Finset γ :=
  (Λ z).biUnion R

lemma mem_transportList {β γ X : Type*} [DecidableEq γ]
    (Λ : X → Finset β) (R : β → Finset γ) (z : X) (o : γ) :
    o ∈ transportList Λ R z ↔ ∃ i ∈ Λ z, o ∈ R i := by
  simp [transportList]

/-- Compatibility tables do not multiply a subpower list by the total atlas size. -/
lemma card_transportList_le {β γ X : Type*} [DecidableEq γ]
    (Λ : X → Finset β) (R : β → Finset γ) (z : X)
    (D : ℝ) (hD : ∀ i, ((R i).card : ℝ) ≤ D) :
    ((transportList Λ R z).card : ℝ) ≤ ((Λ z).card : ℝ) * D := by
  classical
  calc
    ((transportList Λ R z).card : ℝ) ≤ (∑ i ∈ Λ z, (R i).card : ℕ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ = ∑ i ∈ Λ z, ((R i).card : ℝ) := by simp
    _ ≤ ∑ _i ∈ Λ z, D := Finset.sum_le_sum (fun i _ => hD i)
    _ = ((Λ z).card : ℝ) * D := by simp

lemma measurable_transportList {β γ X : Type*} [Fintype β] [DecidableEq γ]
    [MeasurableSpace X] (Λ : X → Finset β) (R : β → Finset γ)
    (hΛ : ∀ i, MeasurableSet {z | i ∈ Λ z}) (o : γ) :
    MeasurableSet {z | o ∈ transportList Λ R z} := by
  classical
  simp only [mem_transportList]
  have heq : {z | ∃ i ∈ Λ z, o ∈ R i} =
      ⋃ i : β, {z | i ∈ Λ z} ∩ {z | o ∈ R i} := by
    ext z
    simp
  rw [heq]
  exact MeasurableSet.iUnion fun i => (hΛ i).inter (by simp)

/-- Old almost-everywhere list knowledge recovers every selected compatible output label. -/
lemma transportList_recovers {α β γ X : Type*} [MeasurableSpace α]
    [Fintype β] [DecidableEq γ] (μ : Measure α)
    (Λ : X → Finset β) (R : β → Finset γ) (obs : α → X)
    (C : β → Set α)
    (hΛ : ∀ i, μ {q | q ∈ C i ∧ i ∉ Λ (obs q)} = 0)
    (o : γ) (S : Set α) (hS : S ⊆ {q | ∃ i, q ∈ C i ∧ o ∈ R i}) :
    μ {q | q ∈ S ∧ o ∉ transportList Λ R (obs q)} = 0 := by
  apply measure_mono_null _ (measure_iUnion_null hΛ)
  rintro q ⟨hq, ho⟩
  obtain ⟨i, hi, hio⟩ := hS hq
  refine mem_iUnion.mpr ⟨i, hi, ?_⟩
  intro hmem
  exact ho ((mem_transportList Λ R (obs q) o).mpr ⟨i, hmem, hio⟩)

/-- The compatibility table may also use the observed time and base point. -/
def transportAtList {β γ X : Type*} [DecidableEq γ]
    (Λ : X → Finset β) (R : X → β → Finset γ) (z : X) : Finset γ :=
  transportList Λ (R z) z

lemma mem_transportAtList {β γ X : Type*} [DecidableEq γ]
    (Λ : X → Finset β) (R : X → β → Finset γ) (z : X) (o : γ) :
    o ∈ transportAtList Λ R z ↔ ∃ i ∈ Λ z, o ∈ R z i := by
  exact mem_transportList Λ (R z) z o

lemma measurable_transportAtList {β γ X : Type*} [Fintype β] [DecidableEq γ]
    [MeasurableSpace X] (Λ : X → Finset β) (R : X → β → Finset γ)
    (hΛ : ∀ i, MeasurableSet {z | i ∈ Λ z})
    (hR : ∀ i o, MeasurableSet {z | o ∈ R z i}) (o : γ) :
    MeasurableSet {z | o ∈ transportAtList Λ R z} := by
  classical
  have heq : {z | o ∈ transportAtList Λ R z} =
      ⋃ i : β, {z | i ∈ Λ z} ∩ {z | o ∈ R z i} := by
    ext z
    simp [mem_transportAtList]
  rw [heq]
  exact MeasurableSet.iUnion fun i => (hΛ i).inter (hR i o)

lemma transportAtList_recovers {α β γ X : Type*} [MeasurableSpace α]
    [Fintype β] [DecidableEq γ] (μ : Measure α)
    (Λ : X → Finset β) (R : X → β → Finset γ) (obs : α → X)
    (C : β → Set α)
    (hΛ : ∀ i, μ {q | q ∈ C i ∧ i ∉ Λ (obs q)} = 0)
    (o : γ) (S : Set α) (hS : S ⊆ {q | ∃ i, q ∈ C i ∧ o ∈ R (obs q) i}) :
    μ {q | q ∈ S ∧ o ∉ transportAtList Λ R (obs q)} = 0 := by
  apply measure_mono_null _ (measure_iUnion_null hΛ)
  rintro q ⟨hq, ho⟩
  obtain ⟨i, hi, hio⟩ := hS hq
  refine mem_iUnion.mpr ⟨i, hi, ?_⟩
  intro hmem
  exact ho ((mem_transportAtList Λ R (obs q) o).mpr ⟨i, hmem, hio⟩)

/-- A compatibility entry identifies the original world of its witness. Thus recovery may be
applied using the original per-world null sets. -/
lemma world_transport_recovers {α β γ X ι : Type*} [MeasurableSpace α]
    [Fintype β] [DecidableEq γ] (μ : ι → Measure α)
    (world : β → ι) (newWorld : γ → ι)
    (Λ : ι → X → Finset β) (R : β → Finset γ) (obs : α → X)
    (C : β → Set α)
    (hΛ : ∀ i, μ (world i) {q | q ∈ C i ∧ i ∉ Λ (world i) (obs q)} = 0)
    (hR : ∀ i o, o ∈ R i → newWorld o = world i)
    (o : γ) (S : Set α) (hS : S ⊆ {q | ∃ i, o ∈ R i ∧ q ∈ C i}) :
    μ (newWorld o) {q | q ∈ S ∧ o ∉ transportList (Λ (newWorld o)) R (obs q)} = 0 := by
  classical
  have hn (i : β) : μ (newWorld o)
      {q | o ∈ R i ∧ q ∈ C i ∧ i ∉ Λ (newWorld o) (obs q)} = 0 := by
    by_cases hoi : o ∈ R i
    · have hw := (hR i o hoi).symm
      simpa only [hoi, true_and, hw] using hΛ i
    · simp [hoi]
  apply measure_mono_null _ (measure_iUnion_null hn)
  rintro q ⟨hq, ho⟩
  obtain ⟨i, hoi, hqi⟩ := hS hq
  refine mem_iUnion.mpr ⟨i, hoi, hqi, ?_⟩
  intro hi
  exact ho ((mem_transportList _ R (obs q) o).mpr ⟨i, hi, hoi⟩)

end

end Submission.Obl.k4_scalar_pair_atlas_assembly
