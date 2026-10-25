import Mathlib

namespace Submission.Obl.k4_horizontal_supercritical_three_projections

open MeasureTheory Set Filter
open scoped ENNReal BigOperators

/-- One finite disjoint family of full-time physical predictions. -/
structure ProjectionLayer (α : Type) where
  n : ℕ
  C : Fin n → Set α
  q : Fin n → Fin 3 → ℤ
  G : Fin n → MvPolynomial (Fin 2) ℝ

namespace ProjectionLayer

variable {α : Type} [MeasurableSpace α]

/-- Its full trajectory coverage, as an incidence event. -/
def covered (L : ProjectionLayer α) : Set (α × ℝ) := {p | ∃ i, p.1 ∈ L.C i}

/-- All estimates are charged to the original measure `ρ`, before later restrictions. -/
def Good (L : ProjectionLayer α) (N d depth ε R χ D : ℝ)
    (b : α → Fin 6 → ℝ) (π : Measure ℝ) (ρ : Measure (α × ℝ)) : Prop :=
  (∀ i, MeasurableSet (L.C i)) ∧
  (∀ i i', i ≠ i' → Disjoint (L.C i) (L.C i')) ∧
  (∀ i,
    (∀ l ∈ L.C i, ⌊b l 3 / χ⌋ = L.q i 0 ∧ ⌊b l 0 / χ⌋ = L.q i 1 ∧
      ⌊b l 1 / D⌋ = L.q i 2 ∧ (∀ e, |b l e| ≤ N ^ ε)) ∧
    |(L.q i 0 : ℝ) * χ| + |(L.q i 1 : ℝ) * χ| + |(L.q i 2 : ℝ) * D| ≤ N ^ ε ∧
    (L.G i).totalDegree ≤ 2 ∧
    (∀ e, |(L.G i).coeff e| ≤ N ^ R) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1,
      |MvPolynomial.eval ![t, (L.q i 2 : ℝ) * D - t * ((L.q i 1 : ℝ) * χ) + D * w]
        (L.G i)| ≤ N ^ ε) ∧
    (∀ l ∈ L.C i, ∀ t ∈ Icc (0 : ℝ) 1,
      |(b l 1 + t * b l 4) - (L.q i 2 : ℝ) * D + t * ((L.q i 1 : ℝ) * χ)| ≤
        N ^ ε * D ∧
      |(b l 2 + t * b l 5) - MvPolynomial.eval ![t, b l 1 + t * b l 4] (L.G i)| ≤
        N ^ ε * N ^ (-depth)) ∧
    ENNReal.ofReal (χ * D * (N ^ (-depth)) ^ d / N ^ ε) *
      π (Ico ((L.q i 0 : ℝ) * χ) (((L.q i 0 : ℝ) + 1) * χ)) ≤
        ρ (L.C i ×ˢ Icc (0 : ℝ) 1)) ∧
  (∑ i, ENNReal.ofReal (χ * D * (N ^ (-depth)) ^ d) *
    π (Ico ((L.q i 0 : ℝ) * χ) (((L.q i 0 : ℝ) + 1) * χ))) ≤ ENNReal.ofReal (N ^ ε)

/-- A stronger loss or coefficient bound supplies every weaker requested one. -/
theorem Good.mono {L : ProjectionLayer α} {N d depth ε ε' R R' χ D : ℝ}
    {b : α → Fin 6 → ℝ} {π : Measure ℝ} {ρ : Measure (α × ℝ)}
    (h : L.Good N d depth ε R χ D b π ρ) (hN : 1 ≤ N)
    (hε : ε ≤ ε') (hR : R ≤ R') (hχ : 0 ≤ χ) (hD : 0 ≤ D) :
    L.Good N d depth ε' R' χ D b π ρ := by
  have hpow : N ^ ε ≤ N ^ ε' := Real.rpow_le_rpow_of_exponent_le hN hε
  have hpowR : N ^ R ≤ N ^ R' := Real.rpow_le_rpow_of_exponent_le hN hR
  have hN₀ : 0 < N := lt_of_lt_of_le zero_lt_one hN
  refine ⟨h.1, h.2.1, ?_, h.2.2.2.trans (ENNReal.ofReal_le_ofReal hpow)⟩
  intro i
  obtain ⟨hbin, hq, hdeg, hcoeff, hnorm, hfit, hfloor⟩ := h.2.2.1 i
  refine ⟨?_, hq.trans hpow, hdeg, fun e => (hcoeff e).trans hpowR, ?_, ?_, ?_⟩
  · intro l hl
    obtain ⟨hb₀, hb₁, hb₂, hb⟩ := hbin l hl
    exact ⟨hb₀, hb₁, hb₂, fun e => (hb e).trans hpow⟩
  · intro t ht w hw
    exact (hnorm t ht w hw).trans hpow
  · intro l hl t ht
    exact ⟨(hfit l hl t ht).1.trans (mul_le_mul_of_nonneg_right hpow hD),
      (hfit l hl t ht).2.trans
        (mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hN₀.le _))⟩
  · apply le_trans ?_ hfloor
    apply mul_le_mul_left
    apply ENNReal.ofReal_le_ofReal
    exact div_le_div_of_nonneg_left
      (mul_nonneg (mul_nonneg hχ hD) (Real.rpow_nonneg (Real.rpow_nonneg hN₀.le _) _))
      (Real.rpow_pos_of_pos hN₀ ε) hpow

end ProjectionLayer

/-- A projection step uniform over all dense submeasures of the original residual. -/
def SingleProjection {α : Type} [MeasurableSpace α]
    (N : ℕ → ℝ) (d depth R M Dexp : ℝ) (b : ℕ → α → Fin 6 → ℝ)
    (π : ℕ → Measure ℝ) (ρ : ℕ → Measure (α × ℝ)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ᶠ k in atTop,
    ∀ ζ : Measure (α × ℝ), ζ ≤ ρ k → ENNReal.ofReal (N k ^ (-η)) ≤ ζ univ →
      ∃ (L : ProjectionLayer α) (ζ' : Measure (α × ℝ)),
        ζ' ≤ ζ ∧ ENNReal.ofReal (N k ^ (-ε)) ≤ ζ' univ ∧
        (∀ᵐ p ∂ζ', p ∈ L.covered) ∧
        L.Good (N k) d depth ε R (N k ^ (-M)) (N k ^ (-Dexp)) (b k) (π k) (ρ k)

/-- Successive selections preserve previous coverage under the final submeasure.
The full-domain floors in every layer remain those under `ρ`. -/
theorem three_layers_of_single {α : Type} [MeasurableSpace α]
    (N : ℕ → ℝ) (d R M Dexp : ℝ) (depth : Fin 3 → ℝ)
    (b : ℕ → α → Fin 6 → ℝ) (π : ℕ → Measure ℝ) (ρ : ℕ → Measure (α × ℝ))
    (hN : ∀ k, 1 ≤ N k)
    (hmass : ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ENNReal.ofReal (N k ^ (-η)) ≤ ρ k univ)
    (hstep : ∀ h, SingleProjection N d (depth h) R M Dexp b π ρ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∃ (ζ : Measure (α × ℝ)) (L : Fin 3 → ProjectionLayer α),
      ζ ≤ ρ k ∧ ENNReal.ofReal (N k ^ (-ε)) ≤ ζ univ ∧
      (∀ᵐ p ∂ζ, ∀ h, p ∈ (L h).covered) ∧
      ∀ h, (L h).Good (N k) d (depth h) ε R (N k ^ (-M)) (N k ^ (-Dexp))
        (b k) (π k) (ρ k) := by
  obtain ⟨η₂, hη₂, H₂⟩ := hstep 2 ε hε
  let ε₁ := min ε η₂
  have hε₁ : 0 < ε₁ := lt_min hε hη₂
  obtain ⟨η₁, hη₁, H₁⟩ := hstep 1 ε₁ hε₁
  let ε₀ := min ε η₁
  have hε₀ : 0 < ε₀ := lt_min hε hη₁
  obtain ⟨η₀, hη₀, H₀⟩ := hstep 0 ε₀ hε₀
  filter_upwards [H₀, H₁, H₂, hmass η₀ hη₀] with k H₀ H₁ H₂ hm
  obtain ⟨L₀, ζ₀, hζ₀, hm₀, hc₀, hg₀⟩ := H₀ (ρ k) le_rfl hm
  have hm₁ : ENNReal.ofReal (N k ^ (-η₁)) ≤ ζ₀ univ := by
    apply le_trans (ENNReal.ofReal_le_ofReal ?_) hm₀
    exact Real.rpow_le_rpow_of_exponent_le (hN k) (neg_le_neg (min_le_right _ _))
  obtain ⟨L₁, ζ₁, hζ₁, hm₁', hc₁, hg₁⟩ := H₁ ζ₀ hζ₀ hm₁
  have hm₂ : ENNReal.ofReal (N k ^ (-η₂)) ≤ ζ₁ univ := by
    apply le_trans (ENNReal.ofReal_le_ofReal ?_) hm₁'
    exact Real.rpow_le_rpow_of_exponent_le (hN k) (neg_le_neg (min_le_right _ _))
  obtain ⟨L₂, ζ₂, hζ₂, hm₂', hc₂, hg₂⟩ := H₂ ζ₁ (hζ₁.trans hζ₀) hm₂
  refine ⟨ζ₂, ![L₀, L₁, L₂], hζ₂.trans (hζ₁.trans hζ₀), hm₂', ?_, ?_⟩
  · have hc₀' := (ae_mono (hζ₂.trans hζ₁)) hc₀
    have hc₁' := (ae_mono hζ₂) hc₁
    filter_upwards [hc₀', hc₁', hc₂] with p hp₀ hp₁ hp₂ h
    fin_cases h <;> simpa using (by assumption : p ∈ _)
  · intro h
    have hχ : 0 ≤ N k ^ (-M) := Real.rpow_nonneg (le_trans zero_le_one (hN k)) _
    have hD : 0 ≤ N k ^ (-Dexp) := Real.rpow_nonneg (le_trans zero_le_one (hN k)) _
    fin_cases h
    · exact hg₀.mono (hN k) (min_le_left _ _) le_rfl hχ hD
    · exact hg₁.mono (hN k) (min_le_left _ _) le_rfl hχ hD
    · exact hg₂

end Submission.Obl.k4_horizontal_supercritical_three_projections
