import Submission.Obl.k4_contact_shifted_quadratic_candidates.NestedLabels
import Submission.Obl.k4_contact_shifted_quadratic_candidates.AffinePalette

namespace Submission.Obl.k4_contact_shifted_quadratic_candidates

open Set MeasureTheory
open scoped ENNReal

noncomputable section

/-- All closed dyadic blocks have unique labels away from these countably
many time endpoints. Removing them costs zero original incidence mass. -/
def endpointGood {α : Type*} (n T : ℕ → ℕ)
    (j : (h : ℕ) → Fin (n h) → Fin (2 ^ T h)) : Set (α × ℝ) :=
  {p | ∀ h i, p.2 ≠ (((j h i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T h}

theorem measurableSet_endpointGood {α : Type*} [MeasurableSpace α]
    (n T : ℕ → ℕ) (j : (h : ℕ) → Fin (n h) → Fin (2 ^ T h)) :
    MeasurableSet (endpointGood (α := α) n T j) := by
  have heq : endpointGood (α := α) n T j =
      ⋂ h, ⋂ i, {p : α × ℝ | p.2 ≠ (((j h i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T h} := by
    ext p
    simp only [endpointGood, mem_ofPred_eq, mem_iInter]
  rw [heq]
  exact MeasurableSet.iInter fun h => MeasurableSet.iInter fun i =>
    (measurableSet_eq_fun measurable_snd measurable_const).compl

theorem ae_endpointGood {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (μ : Measure (α × ℝ)) (C : ℝ≥0∞)
    (hdom : μ ≤ C • ν.prod volume)
    (n T : ℕ → ℕ) (j : (h : ℕ) → Fin (n h) → Fin (2 ^ T h)) :
    ∀ᵐ p ∂μ, p ∈ endpointGood n T j :=
  ae_all_iff.mpr fun h => ae_all_iff.mpr fun i =>
    ae_time_ne_of_product_domination ν μ C hdom _

theorem original_labels_unique_on_endpointGood {α : Type*}
    (n T : ℕ → ℕ) (j : (h : ℕ) → Fin (n h) → Fin (2 ^ T h))
    (A : (h : ℕ) → Fin (n h) → Set α)
    (hdisj : ∀ h i i', i ≠ i' → j h i = j h i' → Disjoint (A h i) (A h i'))
    (p : α × ℝ) (hp : p ∈ endpointGood n T j) :
    ∀ h i i', p ∈ A h i ×ˢ closedTimeBlock (T h) (j h i) →
      p ∈ A h i' ×ˢ closedTimeBlock (T h) (j h i') → i = i' := by
  intro h i i' hi hi'
  by_contra hne
  have hd := Submission.Obl.k4_quadratic_finite_greedy_cover.halfOpen_packets_disjoint
    (A h) (fun i => (j h i : ℕ)) ((2 : ℝ) ^ T h) (by positivity)
    (fun i i' hne heq => hdisj h i i' hne (Fin.ext heq))
  have hdis := Set.disjoint_left.mp (hd hne)
  apply hdis (a := p)
  · exact ⟨hi.1, hi.2.1, lt_of_le_of_ne hi.2.2 (hp h i)⟩
  · exact ⟨hi'.1, hi'.2.1, lt_of_le_of_ne hi'.2.2 (hp h i')⟩

/-- Cleaning a measurable successful source by the contact condition and
all time endpoints leaves its original residual mass unchanged. -/
theorem clean_source_mass {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (μ ρ : Measure (α × ℝ)) (C : ℝ≥0∞)
    (hdom : μ ≤ C • ν.prod volume) (hρ : ρ ≤ μ)
    (b : α → Fin 6 → ℝ) (hb : Measurable b) (E : ℝ)
    (hcontact : ∀ᵐ p ∂μ, |b p.1 4 + b p.1 0| ≤ E)
    (n T : ℕ → ℕ) (j : (h : ℕ) → Fin (n h) → Fin (2 ^ T h))
    (G : Set (α × ℝ)) (hG : MeasurableSet G) :
    ∃ G' : Set (α × ℝ), MeasurableSet G' ∧ G' ⊆ G ∧ ρ G' = ρ G ∧
      (∀ p ∈ G', p ∈ endpointGood n T j) ∧
      ∀ p ∈ G', |b p.1 4 + b p.1 0| ≤ E := by
  let contact : Set (α × ℝ) := {p | |b p.1 4 + b p.1 0| ≤ E}
  have hc : MeasurableSet contact := measurableSet_le (by fun_prop) measurable_const
  let G' := G ∩ (endpointGood n T j ∩ contact)
  refine ⟨G', hG.inter ((measurableSet_endpointGood n T j).inter hc),
    inter_subset_left, ?_, (fun p hp => hp.2.1), (fun p hp => hp.2.2)⟩
  apply measure_congr
  filter_upwards [ae_mono hρ (ae_endpointGood ν μ C hdom n T j), ae_mono hρ hcontact]
    with p hp hc
  exact propext ⟨fun h => h.1, fun h => ⟨h, hp, hc⟩⟩

end

end Submission.Obl.k4_contact_shifted_quadratic_candidates
