import Mathlib

/-!
Adapted from: here:o049

Original finite-atlas proofs developed by session x0147, through commit e50df50.
The weighted plank input is a parameter; no obligation module is imported.
-/

namespace Submission.Lib.K4FinitePlankAtlases

open MeasureTheory Set

variable {α β : Type*} [MeasurableSpace α]

/-- The original measure after all earlier trajectory fits have been removed. -/
noncomputable def residualMeasure (F : β → Set α) (μ : Measure α) : List β → Measure α
  | [] => μ
  | b :: l => residualMeasure F (μ.restrict (F b)ᶜ) l

/-- Every selected geometric candidate removes at least the fixed threshold,
measured before the remaining candidates are selected. -/
inductive GreedySequence (F : β → Set α) (η : ℝ) : Measure α → List β → Prop
  | nil (μ : Measure α) : GreedySequence F η μ []
  | cons {μ : Measure α} {b : β} {l : List β}
      (mass : η ≤ μ.real (F b))
      (tail : GreedySequence F η (μ.restrict (F b)ᶜ) l) :
      GreedySequence F η μ (b :: l)

/-- Each used list entry has its floor under the still unnormalized original law
with exactly the preceding candidates deleted. -/
theorem GreedySequence.mass_at {F : β → Set α} {η : ℝ} {μ : Measure α} {l : List β}
    (h : GreedySequence F η μ l) :
    ∀ i : Fin l.length,
      η ≤ (residualMeasure F μ (l.take i.val)).real (F (l.get i)) := by
  induction h with
  | nil μ => intro i; exact i.elim0
  | @cons μ b l hb ht ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [residualMeasure] using hb
    · simpa [residualMeasure] using ih j

/-- A finite measure cannot support arbitrarily many disjoint deletions of fixed
positive mass. Consequently the greedy selection stops with no heavy residual fit. -/
theorem greedy_exhaustion_of_budget (F : β → Set α)
    (hF : ∀ b, MeasurableSet (F b)) {η : ℝ} (_hη : 0 < η) (n : ℕ) :
    ∀ (μ : Measure α) [IsFiniteMeasure μ], μ.real univ < (n : ℝ) * η →
      ∃ l : List β, l.length < n ∧ GreedySequence F η μ l ∧
        ∀ b, (residualMeasure F μ l).real (F b) < η := by
  induction n with
  | zero =>
    intro μ hμ hmass
    have hnonneg : 0 ≤ μ.real univ := ENNReal.toReal_nonneg
    norm_num at hmass
    exact False.elim (not_lt_of_ge hnonneg hmass)
  | succ n ih =>
    intro μ hμ hmass
    classical
    by_cases hheavy : ∃ b, η ≤ μ.real (F b)
    · obtain ⟨b, hb⟩ := hheavy
      let μ' := μ.restrict (F b)ᶜ
      have hbudget : μ'.real univ < (n : ℝ) * η := by
        rw [show μ'.real univ = μ.real (F b)ᶜ from measureReal_restrict_apply_univ _,
          measureReal_compl (hF b)]
        push_cast at hmass
        linarith
      obtain ⟨l, hlen, hgreedy, hstop⟩ := ih μ' hbudget
      exact ⟨b :: l, by simp only [List.length_cons]; omega,
        GreedySequence.cons hb hgreedy, hstop⟩
    · refine ⟨[], by simp, GreedySequence.nil μ, ?_⟩
      intro b
      exact lt_of_not_ge (fun hb => hheavy ⟨b, hb⟩)

/-- The bounded-budget result applies to every finite measure and positive threshold. -/
theorem exists_greedy_exhaustion (F : β → Set α) (hF : ∀ b, MeasurableSet (F b))
    (μ : Measure α) [IsFiniteMeasure μ] {η : ℝ} (hη : 0 < η) :
    ∃ l : List β, GreedySequence F η μ l ∧
      ∀ b, (residualMeasure F μ l).real (F b) < η := by
  obtain ⟨n, hn⟩ := exists_nat_gt (μ.real univ / η)
  have hbudget : μ.real univ < (n : ℝ) * η := (div_lt_iff₀ hη).mp hn
  obtain ⟨l, hlen, hg, hs⟩ := greedy_exhaustion_of_budget F hF hη n μ hbudget
  exact ⟨l, hg, hs⟩

/-- Iterated deletion is restriction of the original law to the complement of
all selected candidate sets, with no renormalization. -/
theorem residualMeasure_eq (F : β → Set α) (hF : ∀ b, MeasurableSet (F b))
    (μ : Measure α) (l : List β) :
    residualMeasure F μ l = μ.restrict (⋃ b ∈ l, F b)ᶜ := by
  classical
  induction l generalizing μ with
  | nil => simp [residualMeasure]
  | cons b l ih =>
    have hU : (⋃ c ∈ b :: l, F c) = F b ∪ ⋃ c ∈ l, F c := by
      ext x
      simp only [List.mem_cons, mem_iUnion]
      aesop
    have hm : MeasurableSet (⋃ c ∈ l, F c) :=
      MeasurableSet.biUnion l.finite_toSet.countable (fun c _ => hF c)
    rw [residualMeasure, ih, hU, compl_union, Measure.restrict_restrict hm.compl]
    rw [inter_comm]

/-- Geometric packets may have different true floors (for example, proportional
to their spatial determinants). A common positive lower bound makes the same
finite greedy construction terminate. -/
inductive ThresholdGreedySequence (F : β → Set α) (threshold : β → ℝ) :
    Measure α → List β → Prop
  | nil (μ : Measure α) : ThresholdGreedySequence F threshold μ []
  | cons {μ : Measure α} {b : β} {l : List β}
      (mass : threshold b ≤ μ.real (F b))
      (tail : ThresholdGreedySequence F threshold (μ.restrict (F b)ᶜ) l) :
      ThresholdGreedySequence F threshold μ (b :: l)

theorem ThresholdGreedySequence.mass_at {F : β → Set α} {threshold : β → ℝ}
    {μ : Measure α} {l : List β} (h : ThresholdGreedySequence F threshold μ l) :
    ∀ i : Fin l.length,
      threshold (l.get i) ≤ (residualMeasure F μ (l.take i.val)).real (F (l.get i)) := by
  induction h with
  | nil μ => intro i; exact i.elim0
  | @cons μ b l hb ht ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [residualMeasure] using hb
    · simpa [residualMeasure] using ih j

/-- The geometric greedy stopping rule with a packet-dependent mass floor.
The sequence length is bounded before any candidate is chosen. -/
theorem threshold_greedy_exhaustion_of_budget (F : β → Set α)
    (hF : ∀ b, MeasurableSet (F b)) (threshold : β → ℝ) {η : ℝ}
    (hfloor : ∀ b, η ≤ threshold b) (n : ℕ) :
    ∀ (μ : Measure α) [IsFiniteMeasure μ], μ.real univ < (n : ℝ) * η →
      ∃ l : List β, l.length < n ∧ ThresholdGreedySequence F threshold μ l ∧
        ∀ b, (residualMeasure F μ l).real (F b) < threshold b := by
  induction n with
  | zero =>
    intro μ hμ hmass
    have hnonneg : 0 ≤ μ.real univ := ENNReal.toReal_nonneg
    norm_num at hmass
    exact False.elim (not_lt_of_ge hnonneg hmass)
  | succ n ih =>
    intro μ hμ hmass
    classical
    by_cases hheavy : ∃ b, threshold b ≤ μ.real (F b)
    · obtain ⟨b, hb⟩ := hheavy
      let μ' := μ.restrict (F b)ᶜ
      have hbudget : μ'.real univ < (n : ℝ) * η := by
        rw [show μ'.real univ = μ.real (F b)ᶜ from measureReal_restrict_apply_univ _,
          measureReal_compl (hF b)]
        push_cast at hmass
        linarith [hfloor b]
      obtain ⟨l, hlen, hgreedy, hstop⟩ := ih μ' hbudget
      exact ⟨b :: l, by simp only [List.length_cons]; omega,
        ThresholdGreedySequence.cons hb hgreedy, hstop⟩
    · refine ⟨[], by simp, ThresholdGreedySequence.nil μ, ?_⟩
      intro b
      exact lt_of_not_ge (fun hb => hheavy ⟨b, hb⟩)

theorem exists_threshold_greedy_exhaustion (F : β → Set α)
    (hF : ∀ b, MeasurableSet (F b)) (threshold : β → ℝ)
    (μ : Measure α) [IsFiniteMeasure μ] {η : ℝ} (hη : 0 < η)
    (hfloor : ∀ b, η ≤ threshold b) :
    ∃ l : List β, ThresholdGreedySequence F threshold μ l ∧
      ∀ b, (residualMeasure F μ l).real (F b) < threshold b := by
  obtain ⟨n, hn⟩ := exists_nat_gt (μ.real univ / η)
  obtain ⟨l, hlen, hg, hs⟩ := threshold_greedy_exhaustion_of_budget F hF threshold hfloor n μ
    ((div_lt_iff₀ hη).mp hn)
  exact ⟨l, hg, hs⟩

end Submission.Lib.K4FinitePlankAtlases
