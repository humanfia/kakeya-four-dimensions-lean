import Submission.Obl.k4_conditional_common_affine_field.LineMixedTerm

namespace Submission.Obl.k4_conditional_common_affine_field

open Set MeasureTheory
open scoped ENNReal

/-- Delete neighborhoods of two axes using their ceilings in the original law.
The fitted event retains at least half its absolute mass floor. -/
theorem retain_nonaxis_event {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : Set Ω) (hE : MeasurableSet E) (v : Ω → ℝ) (hv : Measurable v)
    (w₁ w₂ r m D : ℝ) (hm : 0 < m) (hD : 0 ≤ D) (hsmall : 4*D ≤ m)
    (hmass : ENNReal.ofReal m ≤ μ E)
    (hpencil₁ : μ {p | |v p-w₁| < r} ≤ ENNReal.ofReal D)
    (hpencil₂ : μ {p | |v p-w₂| < r} ≤ ENNReal.ofReal D) :
    ∃ T : Set Ω, MeasurableSet T ∧ T ⊆ E ∧ ENNReal.ofReal (m/2) ≤ μ T ∧
      ∀ p ∈ T, r ≤ |v p-w₁| ∧ r ≤ |v p-w₂| := by
  let A : Set Ω := {p | r ≤ |v p-w₁| ∧ r ≤ |v p-w₂|}
  have hA : MeasurableSet A :=
    (measurableSet_le measurable_const (hv.sub_const w₁).abs).inter
      (measurableSet_le measurable_const (hv.sub_const w₂).abs)
  let T := E ∩ A
  let B₁ : Set Ω := {p | |v p-w₁| < r}
  let B₂ : Set Ω := {p | |v p-w₂| < r}
  have hcover : E ⊆ (T ∪ B₁) ∪ B₂ := by
    intro p hp
    by_cases h₁ : r ≤ |v p-w₁|
    · by_cases h₂ : r ≤ |v p-w₂|
      · exact Or.inl (Or.inl ⟨hp,h₁,h₂⟩)
      · exact Or.inr (lt_of_not_ge h₂)
    · exact Or.inl (Or.inr (lt_of_not_ge h₁))
  have hbound : ENNReal.ofReal m ≤ μ T+ENNReal.ofReal (m/2) := by
    calc
      _ ≤ μ E := hmass
      _ ≤ μ ((T ∪ B₁) ∪ B₂) := measure_mono hcover
      _ ≤ μ T+μ B₁+μ B₂ := (measure_union_le _ _).trans
        (add_le_add (measure_union_le _ _) le_rfl)
      _ ≤ μ T+ENNReal.ofReal D+ENNReal.ofReal D :=
        add_le_add (add_le_add le_rfl hpencil₁) hpencil₂
      _ = μ T+ENNReal.ofReal (2*D) := by
        rw [add_assoc,← ENNReal.ofReal_add hD hD]
        congr 2
        ring
      _ ≤ μ T+ENNReal.ofReal (m/2) := add_le_add le_rfl
        (ENNReal.ofReal_le_ofReal (by linarith))
  have hsplit : ENNReal.ofReal m = ENNReal.ofReal (m/2)+ENNReal.ofReal (m/2) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  rw [hsplit] at hbound
  exact ⟨T,hE.inter hA,inter_subset_left,
    ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top hbound,fun p hp => hp.2⟩

/-- A third-direction line witness can be selected after all field fitting,
using only the earlier unconditional pencil ceilings. -/
theorem lineMixedTerm_from_pencils {α : Type} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (μ : Measure (α × ℝ))
    {ι : Type} (chart : α → ι) (L : ι → Finset (Fin 3 → ℝ))
    (b u : α → ℝ) (hu : Measurable u) (g : α × ℝ → ℝ)
    (E : Set (α × ℝ)) (β : Fin 4 → ℝ) (K n m r D E₁ E₂ w₁ w₂ : ℝ)
    (hK : 0 < K) (hn : 1 ≤ n) (hm : 0 < m) (hr : 0 < r)
    (hD : 0 ≤ D) (hsmall : 4*D ≤ m)
    (hdom : μ ≤ ENNReal.ofReal K • ν.prod volume)
    (hEm : MeasurableSet E) (hEtime : E ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (hmass : ENNReal.ofReal m ≤ μ E) (hL : ∀ i, ((L i).card : ℝ) ≤ n)
    (hbilin : ∀ p ∈ E, |g p-(β 0+β 1*(b p.1+p.2*(u p.1-w₁))+
      β 2*(b p.1+p.2*(u p.1-w₂))+
      β 3*(b p.1+p.2*(u p.1-w₁))*(b p.1+p.2*(u p.1-w₂)))| ≤ E₁)
    (hfit : ∀ p ∈ E, ∃ a ∈ L (chart p.1), |g p-a 0-a 1*p.2| ≤ E₂)
    (hpencil₁ : μ {p | |u p.1-w₁| < r} ≤ ENNReal.ofReal D)
    (hpencil₂ : μ {p | |u p.1-w₂| < r} ≤ ENNReal.ofReal D) :
    |β 3| * r^2 ≤ 8*(96*K*n/m)^2*(E₁+E₂) := by
  obtain ⟨T,hTm,hTE,hTmass,hTaway⟩ := retain_nonaxis_event μ E hEm
    (fun p => u p.1) (hu.comp measurable_fst) w₁ w₂ r m D hm hD hsmall hmass hpencil₁ hpencil₂
  have h := lineMixedTerm ν μ chart L b u g T β K n (m/2) r E₁ E₂ w₁ w₂
    inferInstance hK hn (by positivity) hr hdom hTm (hTE.trans hEtime) hTmass hL
    (fun p hp => hbilin p (hTE hp)) (fun p hp => hfit p (hTE hp)) hTaway
  simpa only [show 48*K*n/(m/2)=96*K*n/m by ring] using h

end Submission.Obl.k4_conditional_common_affine_field
