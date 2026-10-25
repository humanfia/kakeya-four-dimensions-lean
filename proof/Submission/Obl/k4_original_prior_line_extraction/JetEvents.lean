import Submission.Obl.k4_original_prior_line_extraction.TranslatedWindows

namespace Submission.Obl.k4_original_prior_line_extraction

open MeasureTheory Set Filter
open scoped ENNReal

/-- Extend a local continuous directional jet by zero to obtain a measurable function. -/
noncomputable def cutoffJet (F : Base → ℝ) (v : Base) (m : ℕ) : Base → ℝ :=
  by
    classical
    exact (Metric.ball 0 1).piecewise
      (fun x => iteratedDeriv m (fun t : ℝ => F (x + t • v)) 0) (fun _ => 0)

lemma measurable_cutoffJet {F : Base → ℝ} (v : Base) (m : ℕ)
    (hf : ContinuousOn (fun x => iteratedDeriv m (fun t : ℝ => F (x + t • v)) 0)
      (Metric.ball 0 1)) : Measurable (cutoffJet F v m) := by
  classical
  unfold cutoffJet
  exact hf.measurable_piecewise continuousOn_const measurableSet_ball

lemma cutoffJet_eq (F : Base → ℝ) (v : Base) (m : ℕ) {x : Base} (hx : ‖x‖ < 1) :
    cutoffJet F v m x = iteratedDeriv m (fun t : ℝ => F (x + t • v)) 0 := by
  classical
  have hxball : x ∈ Metric.ball (0 : Base) 1 := by simpa using hx
  exact piecewise_eq_of_mem _ _ _ hxball

noncomputable def jetEvent {n₁ n₂ : ℕ}
    (F₁ : Fin n₁ → Base → ℝ) (F₂ : Fin n₂ → Base → ℝ)
    (v : Base) (K : ℕ) (u l : ℝ) : Set ((Fin n₁ × Fin n₂) × Base) :=
  {p | ‖p.2‖ ≤ (1 : ℝ) / 2 ∧
    |cutoffJet (F₁ p.1.1) v 0 p.2 - cutoffJet (F₂ p.1.2) v 0 p.2| ≤ u ∧
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ K ∧
      l ≤ |cutoffJet (F₁ p.1.1) v j p.2 - cutoffJet (F₂ p.1.2) v j p.2|}

lemma jetEvent_iff {n₁ n₂ : ℕ}
    (F₁ : Fin n₁ → Base → ℝ) (F₂ : Fin n₂ → Base → ℝ)
    (v : Base) (K : ℕ) (u l : ℝ) (p : (Fin n₁ × Fin n₂) × Base) :
    p ∈ jetEvent F₁ F₂ v K u l ↔
      ‖p.2‖ ≤ (1 : ℝ) / 2 ∧ |F₁ p.1.1 p.2 - F₂ p.1.2 p.2| ≤ u ∧
      ∃ j : ℕ, 1 ≤ j ∧ j ≤ K ∧ l ≤
        |iteratedDeriv j (fun t : ℝ => F₁ p.1.1 (p.2 + t • v)) 0 -
          iteratedDeriv j (fun t : ℝ => F₂ p.1.2 (p.2 + t • v)) 0| := by
  by_cases hp : ‖p.2‖ ≤ (1 : ℝ) / 2
  · have hp' : ‖p.2‖ < 1 := by linarith
    simp [jetEvent, cutoffJet_eq _ _ _ hp']
  · simp only [jetEvent, mem_setOf_eq, hp, false_and]

lemma measurableSet_jetEvent {n₁ n₂ : ℕ}
    (F₁ : Fin n₁ → Base → ℝ) (F₂ : Fin n₂ → Base → ℝ)
    (v : Base) (K : ℕ) (u l : ℝ)
    (h₁ : ∀ i m, m ≤ K → ContinuousOn
      (fun x => iteratedDeriv m (fun t : ℝ => F₁ i (x + t • v)) 0) (Metric.ball 0 1))
    (h₂ : ∀ i m, m ≤ K → ContinuousOn
      (fun x => iteratedDeriv m (fun t : ℝ => F₂ i (x + t • v)) 0) (Metric.ball 0 1)) :
    MeasurableSet (jetEvent F₁ F₂ v K u l) := by
  classical
  have hjet₁ (m : ℕ) (hm : m ≤ K) : Measurable
      (fun p : (Fin n₁ × Fin n₂) × Base => cutoffJet (F₁ p.1.1) v m p.2) :=
    measurable_from_prod_countable_right fun a => measurable_cutoffJet v m (h₁ a.1 m hm)
  have hjet₂ (m : ℕ) (hm : m ≤ K) : Measurable
      (fun p : (Fin n₁ × Fin n₂) × Base => cutoffJet (F₂ p.1.2) v m p.2) :=
    measurable_from_prod_countable_right fun a => measurable_cutoffJet v m (h₂ a.2 m hm)
  have heq : jetEvent F₁ F₂ v K u l =
      ⋃ j ∈ Finset.Icc 1 K, {p : (Fin n₁ × Fin n₂) × Base |
        ‖p.2‖ ≤ (1 : ℝ) / 2 ∧
        |cutoffJet (F₁ p.1.1) v 0 p.2 - cutoffJet (F₂ p.1.2) v 0 p.2| ≤ u ∧
        l ≤ |cutoffJet (F₁ p.1.1) v j p.2 - cutoffJet (F₂ p.1.2) v j p.2|} := by
    ext p
    simp only [jetEvent, mem_setOf_eq, mem_iUnion, Finset.mem_Icc]
    constructor
    · rintro ⟨hp, hval, j, hj₁, hjK, hgap⟩
      exact ⟨j, ⟨hj₁, hjK⟩, hp, hval, hgap⟩
    · rintro ⟨j, ⟨hj₁, hjK⟩, hp, hval, hgap⟩
      exact ⟨hp, hval, j, hj₁, hjK, hgap⟩
  rw [heq]
  apply Finset.measurableSet_biUnion
  intro j hj
  have hjK : j ≤ K := (Finset.mem_Icc.mp hj).2
  exact (measurableSet_le measurable_snd.norm measurable_const).inter
    ((measurableSet_le ((hjet₁ 0 (Nat.zero_le _)).sub (hjet₂ 0 (Nat.zero_le _))).abs
      measurable_const).inter
      (measurableSet_le measurable_const ((hjet₁ j hjK).sub (hjet₂ j hjK)).abs))

end Submission.Obl.k4_original_prior_line_extraction
