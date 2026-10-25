import Submission.Obl.k4_contact_time_rate_rigidity.Geometry
import Submission.Obl.k4_contact_time_rate_rigidity.Palette
import Submission.Obl.k4_contact_time_rate_rigidity.Budget

namespace Submission.Obl.k4_contact_time_rate_rigidity

open MeasureTheory Set
open scoped ENNReal

/-- Nested fine assignments force the entire incidence law into short coarse times. -/
theorem nested_time_bound {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (μ : Measure (α × ℝ))
    (b : α → Fin 6 → ℝ) {nc nf M : ℕ}
    (A₀ : Fin nc → Set α) (j₀ : Fin nc → Fin M) (c₀ : Fin nc → Fin 5 → ℝ)
    (A₁ B₁ : Fin nf → Set α) (I₁ : Fin nf → Set ℝ)
    (u : Fin nf → ℝ) (c₁ : Fin nf → Fin 5 → ℝ)
    {K q g e δ η : ℝ} (hK : 1 ≤ K) (hq : 0 < q) (hδ : 0 < δ) (hη : 0 ≤ η)
    (hdom : μ ≤ ENNReal.ofReal K • (ν.prod volume))
    (hA₀ : ∀ i, MeasurableSet (A₀ i))
    (hdisj : ∀ i i', i ≠ i' → j₀ i = j₀ i' → Disjoint (A₀ i) (A₀ i'))
    (hsub : ∀ i, B₁ i ⊆ A₁ i)
    (hancestor : ∀ i, ∃ h, A₁ i ⊆ A₀ h)
    (hrow₀ : ∀ i l, l ∈ A₀ i → |b l 4 - c₀ i 3 - c₀ i 4 * b l 3| ≤ K * g)
    (hrow₁ : ∀ i l, l ∈ A₁ i →
      |b l 0 + u i * b l 3 - c₁ i 0 - u i * c₁ i 1| ≤ K * q)
    (htime : ∀ i t, t ∈ I₁ i → |t - u i| ≤ q)
    (hcontact : ∀ᵐ p ∂μ, |b p.1 4 + b p.1 0| ≤ e)
    (hpos : ∀ i, ν (A₁ i) ≠ 0)
    (hmass : ∀ i, ENNReal.ofReal (q / K) * ν (A₁ i) ≤ μ (B₁ i ×ˢ I₁ i))
    (hcap : ∀ i (a : ℤ), μ {p | p.1 ∈ B₁ i ∧ p.2 ∈ I₁ i ∧ ⌊b p.1 3 / δ⌋ = a} ≤
      ENNReal.ofReal (K * q) * ν (A₁ i) * ENNReal.ofReal (K * η))
    (hsmall : 6 * K ^ 3 * η < 1)
    (hcover : ∀ᵐ p ∂μ, ∃ i, p.1 ∈ B₁ i ∧ p.2 ∈ I₁ i) :
    μ univ ≤ ENNReal.ofReal (2 * K *
      (q + (2 * K * q + 2 * K * g + 2 * e) / δ)) * (M : ℝ≥0∞) := by
  classical
  choose ancestor hancestor using hancestor
  let τ := q + (2 * K * q + 2 * K * g + 2 * e) / δ
  have hblock (i : Fin nf) (t : ℝ) (ht : t ∈ I₁ i) :
      |t - c₀ (ancestor i) 4| ≤ τ := by
    obtain ⟨p₀, p₁, hp₀, hp₁, hsep⟩ :=
      label_witnesses μ (B₁ i ×ˢ I₁ i) {p | |b p.1 4 + b p.1 0| ≤ e}
        (fun p => b p.1 3) hK hq hδ hη (ν (A₁ i)) (hpos i) (measure_ne_top _ _)
        (hmass i) (by simpa only [mem_prod, and_assoc] using hcap i) hsmall hcontact
    have ha₀ := hsub i hp₀.1.1
    have ha₁ := hsub i hp₁.1.1
    have hpivot : |u i - c₀ (ancestor i) 4| ≤
        (2 * K * q + 2 * K * g + 2 * e) / δ := by
      apply pivot_bound hδ hsep.le hp₀.2 hp₁.2
        (hrow₀ _ _ (hancestor i ha₀)) (hrow₀ _ _ (hancestor i ha₁))
        (z := c₁ i 0 + u i * c₁ i 1)
      · simpa only [sub_add_eq_sub_sub] using hrow₁ i _ ha₀
      · simpa only [sub_add_eq_sub_sub] using hrow₁ i _ ha₁
    calc
      _ ≤ |t - u i| + |u i - c₀ (ancestor i) 4| := abs_sub_le _ _ _
      _ ≤ τ := add_le_add (htime i t ht) hpivot
  have hcover' : ∀ᵐ p ∂μ, ∃ i, p.1 ∈ A₀ i ∧
      p.2 ∈ Icc (c₀ i 4 - τ) (c₀ i 4 + τ) := by
    filter_upwards [hcover] with p hp
    obtain ⟨i, hi, ht⟩ := hp
    refine ⟨ancestor i, hancestor i (hsub i hi), ?_⟩
    have hh := abs_le.mp (hblock i p.2 ht)
    constructor <;> linarith
  simpa only [Fintype.card_fin] using
    mass_bound_of_time_cover ν μ A₀ j₀ (fun i => c₀ i 4)
      (by linarith : 0 ≤ K) hdom hA₀ hdisj hcover'

end Submission.Obl.k4_contact_time_rate_rigidity
