import Submission.Obl.k4_matching_gap_regularization.Restriction

set_option autoImplicit false

namespace Submission.Obl.k4_matching_gap_regularization

open MeasureTheory Set
open scoped ENNReal

def Base (J : ℕ) (d ε N : ℝ) {n₁ n₂ : ℕ}
    (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ)
    (π₁ : Fin n₁ → ℝ) (π₂ : Fin n₂ → ℝ)
    (μ : Measure ((Fin n₁ × Fin n₂) × ℝ)) : Prop :=
  (n₁ : ℝ) ≤ N ^ (d + ε) ∧ (n₂ : ℝ) ≤ N ^ (d + ε) ∧
  (∀ i, ContDiffOn ℝ (J + 1) (f₁ i) (Ioo (-1 : ℝ) 2)) ∧
  (∀ i, ContDiffOn ℝ (J + 1) (f₂ i) (Ioo (-1 : ℝ) 2)) ∧
  (∀ i j, j ≤ J + 1 → ∀ t ∈ Icc (0 : ℝ) 1, |iteratedDeriv j (f₁ i) t| ≤ N ^ ε) ∧
  (∀ i j, j ≤ J + 1 → ∀ t ∈ Icc (0 : ℝ) 1, |iteratedDeriv j (f₂ i) t| ≤ N ^ ε) ∧
  (∀ i, 0 ≤ π₁ i) ∧ (∀ i, 0 ≤ π₂ i) ∧
  (∑ i, π₁ i) = 1 ∧ (∑ i, π₂ i) = 1 ∧ IsProbabilityMeasure μ ∧
  (∀ i (E : Set ℝ), MeasurableSet E →
    μ {p | p.1.1 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ ε * π₁ i) * volume E) ∧
  (∀ i (E : Set ℝ), MeasurableSet E →
    μ {p | p.1.2 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ ε * π₂ i) * volume E)

def BadSet (D : ℕ) (η N : ℝ) {n₁ n₂ : ℕ}
    (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ) :
    Set ((Fin n₁ × Fin n₂) × ℝ) :=
  {p | p.2 ∈ Icc (0 : ℝ) 1 ∧ |f₁ p.1.1 p.2 - f₂ p.1.2 p.2| ≤ N ^ (-1 + η) ∧
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ D ∧
      N ^ (-η) ≤ |iteratedDeriv j (f₁ p.1.1) p.2 - iteratedDeriv j (f₂ p.1.2) p.2|}

def GapSet (J : ℕ) (β : ℕ → ℝ) (ε N : ℝ) {n₁ n₂ : ℕ}
    (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ) :
    Set ((Fin n₁ × Fin n₂) × ℝ) :=
  {p | p.2 ∈ Ico (0 : ℝ) 1 ∧ |f₁ p.1.1 p.2 - f₂ p.1.2 p.2| ≤ N ^ (-1 + ε) ∧
    ∀ j : ℕ, 1 ≤ j → j ≤ J →
      |iteratedDeriv j (f₁ p.1.1) p.2 - iteratedDeriv j (f₂ p.1.2) p.2| ≤ N ^ (-β j + ε) ∧
      (β j < 2 → N ^ (-β j - ε) ≤
        |iteratedDeriv j (f₁ p.1.1) p.2 - iteratedDeriv j (f₂ p.1.2) p.2|)}

def Bad (D J : ℕ) (d η N : ℝ) : Prop :=
  ∃ (n₁ n₂ : ℕ) (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ)
    (π₁ : Fin n₁ → ℝ) (π₂ : Fin n₂ → ℝ) (μ : Measure ((Fin n₁ × Fin n₂) × ℝ)),
    Base J d η N f₁ f₂ π₁ π₂ μ ∧ μ (BadSet D η N f₁ f₂)ᶜ = 0

def Gap (J : ℕ) (d : ℝ) (β : ℕ → ℝ) (ε N : ℝ) : Prop :=
  ∃ (n₁ n₂ : ℕ) (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ)
    (π₁ : Fin n₁ → ℝ) (π₂ : Fin n₂ → ℝ) (μ : Measure ((Fin n₁ × Fin n₂) × ℝ)),
    Base J d ε N f₁ f₂ π₁ π₂ μ ∧ μ (GapSet J β ε N f₁ f₂)ᶜ = 0

def Admissible (D J : ℕ) (β : ℕ → ℝ) : Prop :=
  (∀ j : ℕ, 1 ≤ j → j ≤ J → 0 ≤ β j ∧ β j ≤ 2) ∧
  ∃ j : ℕ, 1 ≤ j ∧ j ≤ D ∧ β j = 0

lemma base_enlarge {n₁ n₂ J : ℕ} {f₁ : Fin n₁ → ℝ → ℝ} {f₂ : Fin n₂ → ℝ → ℝ}
    {π₁ : Fin n₁ → ℝ} {π₂ : Fin n₂ → ℝ}
    {μ ν : Measure ((Fin n₁ × Fin n₂) × ℝ)} {d η a ε N : ℝ}
    (hN : 1 ≤ N) (hη : η ≤ ε) (ha : a + η ≤ ε)
    (hν : ∀ E : Set ((Fin n₁ × Fin n₂) × ℝ), ν E ≤ ENNReal.ofReal (N ^ a) * μ E)
    (hprob : IsProbabilityMeasure ν)
    (hbase : Base J d η N f₁ f₂ π₁ π₂ μ) :
    Base J d ε N f₁ f₂ π₁ π₂ ν := by
  rcases hbase with ⟨hn₁, hn₂, hf₁, hf₂, hb₁, hb₂, hp₁, hp₂, hs₁, hs₂, hμ, hm₁, hm₂⟩
  have hr : N ^ η ≤ N ^ ε := Real.rpow_le_rpow_of_exponent_le hN hη
  refine ⟨hn₁.trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith)),
    hn₂.trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith)), hf₁, hf₂,
    ?_, ?_, hp₁, hp₂, hs₁, hs₂, hprob, ?_, ?_⟩
  · exact fun i j hj t ht => (hb₁ i j hj t ht).trans hr
  · exact fun i j hj t ht => (hb₂ i j hj t ht).trans hr
  · exact fun i E hE => marginal_power_loss hN (hp₁ i) ha hν (hm₁ i E hE)
  · exact fun i E hE => marginal_power_loss hN (hp₂ i) ha hν (hm₂ i E hE)

/-- Nearby exponent vectors give the same data after increasing the error,
provided the lower-bound cutoff is retained. -/
lemma gap_transport {J : ℕ} {d η ε N : ℝ} {β γ : ℕ → ℝ}
    (hN : 1 ≤ N) (hη : η ≤ ε)
    (hclose : ∀ j, 1 ≤ j → j ≤ J → |β j - γ j| ≤ ε - η)
    (hcut : ∀ j, 1 ≤ j → j ≤ J → γ j < 2 → β j < 2)
    (hgap : Gap J d β η N) : Gap J d γ ε N := by
  rcases hgap with ⟨n₁, n₂, f₁, f₂, π₁, π₂, μ, hbase, hsupp⟩
  have hprob : IsProbabilityMeasure μ := hbase.2.2.2.2.2.2.2.2.2.2.1
  have hdom : ∀ E : Set ((Fin n₁ × Fin n₂) × ℝ), μ E ≤ ENNReal.ofReal (N ^ (0 : ℝ)) * μ E :=
    fun E => by simp
  refine ⟨n₁, n₂, f₁, f₂, π₁, π₂, μ,
    base_enlarge hN hη (by simpa using hη) hdom hprob hbase, (ae_iff).1 ?_⟩
  have hae : ∀ᵐ p ∂μ, p ∈ GapSet J β η N f₁ f₂ := (ae_iff).2 hsupp
  filter_upwards [hae] with p hp
  refine ⟨hp.1, hp.2.1.trans (Real.rpow_le_rpow_of_exponent_le hN (add_le_add le_rfl hη)), ?_⟩
  intro j hj₁ hjJ
  have hc := abs_le.1 (hclose j hj₁ hjJ)
  have hj := hp.2.2 j hj₁ hjJ
  refine ⟨hj.1.trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith only [hc.1])), ?_⟩
  intro hγ
  exact (Real.rpow_le_rpow_of_exponent_le hN (by linarith only [hc.2])).trans
    (hj.2 (hcut j hj₁ hjJ hγ))

end Submission.Obl.k4_matching_gap_regularization
