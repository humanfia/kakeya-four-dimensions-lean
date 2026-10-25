import Mathlib

-- Adapted from x0260's Packets.lean on o078 (branch x0260, commit 65d7688), same tree.

namespace Submission.Obl.k4_scalar_terminal_chart_packet_extraction

open MeasureTheory Set
open scoped ENNReal

abbrev Coeff := ℕ × (Fin 5 → ℝ)

def spatial (l : Coeff) (t : ℝ) : ℝ := l.2 0 + t * l.2 1

def hidden (l : Coeff) (t : ℝ) : ℝ := l.2 2 + t * l.2 3 + t ^ 2 * l.2 4

def block (T : ℕ) (j : Fin (2 ^ T)) : Set ℝ :=
  Icc ((j : ℕ) / (2 : ℝ) ^ T) (((j : ℕ) + 1) / (2 : ℝ) ^ T)

/-- The finite output of the frozen exact angular packet theorem, at a single
sample and with its original world measures and weights. -/
def HasPackets (N : ℝ) (W : ℕ) (ω : Fin W → ℝ)
    (μ : Fin W → Measure (Coeff × ℝ)) (L fL h ε : ℝ) : Prop :=
  ∃ (T n : ℕ) (γ : Fin n → Fin W) (j : Fin n → Fin (2 ^ T))
      (A : Fin n → Set Coeff) (P : Fin n → MvPolynomial (Fin 2) ℝ),
    (2 : ℝ) ^ T ≤ N ^ h ∧
    (∀ i, MeasurableSet (A i)) ∧
    (∀ i i', i ≠ i' → γ i = γ i' → j i = j i' → Disjoint (A i) (A i')) ∧
    (∀ i, (P i).totalDegree ≤ 2 ∧
      (∀ t ∈ block T (j i), ∀ w ∈ Icc (-1 : ℝ) 1,
        |MvPolynomial.eval ![t, w] (P i)| ≤ N ^ ε) ∧
      (∀ l ∈ A i, ∀ t ∈ block T (j i),
        |hidden l t - MvPolynomial.eval ![t, spatial l t] (P i)| ≤ N ^ ε * N ^ (-L)) ∧
      ENNReal.ofReal (N ^ (-fL) / (N ^ ε * (2 : ℝ) ^ T)) ≤
        μ (γ i) (A i ×ˢ block T (j i))) ∧
    ENNReal.ofReal (N ^ (-ε)) ≤
      ∑ g : Fin W, ENNReal.ofReal (ω g) *
        μ g {p | ∃ i, γ i = g ∧ p.1 ∈ A i ∧ p.2 ∈ block T (j i)}

/-- Enlarging either output tolerance keeps all assignments and predictors.
The floor weakens in the same original normalization. -/
theorem HasPackets.mono {N : ℝ} {W : ℕ} {ω : Fin W → ℝ}
    {μ : Fin W → Measure (Coeff × ℝ)} {L fL h h' ε ε' : ℝ}
    (hN : 1 ≤ N) (hh : h ≤ h') (hε : ε ≤ ε')
    (hp : HasPackets N W ω μ L fL h ε) : HasPackets N W ω μ L fL h' ε' := by
  obtain ⟨T, n, γ, j, A, P, hT, hA, hd, hP, hm⟩ := hp
  have hN0 : 0 ≤ N := le_trans zero_le_one hN
  refine ⟨T, n, γ, j, A, P, hT.trans (Real.rpow_le_rpow_of_exponent_le hN hh),
    hA, hd, ?_, ?_⟩
  · intro i
    obtain ⟨hdeg, hnorm, hfit, hfloor⟩ := hP i
    refine ⟨hdeg, ?_, ?_, ?_⟩
    · intro t ht w hw
      exact (hnorm t ht w hw).trans (Real.rpow_le_rpow_of_exponent_le hN hε)
    · intro l hl t ht
      exact (hfit l hl t ht).trans (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hN hε) (Real.rpow_nonneg hN0 _))
    · apply le_trans (ENNReal.ofReal_le_ofReal ?_) hfloor
      apply div_le_div_of_nonneg_left (Real.rpow_nonneg hN0 _) (by positivity)
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hN hε)
        (by positivity)
  · exact (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg hε))).trans hm

/-- It suffices to construct packets with equal time and accuracy tolerances.
This is convenient when diagonalizing the exact sequence. -/
theorem forall_frequently_packets_iff_diagonal
    (N : ℕ → ℝ) (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ)
    (μ : (k : ℕ) → Fin (W k) → Measure (Coeff × ℝ)) (L fL : ℝ)
    (hN : ∀ k, 1 ≤ N k) :
    (∀ h ε : ℝ, 0 < h → 0 < ε →
      ∃ᶠ k in Filter.atTop, HasPackets (N k) (W k) (ω k) (μ k) L fL h ε) ↔
    (∀ δ : ℝ, 0 < δ →
      ∃ᶠ k in Filter.atTop, HasPackets (N k) (W k) (ω k) (μ k) L fL δ δ) := by
  constructor
  · intro hp δ hδ
    exact hp δ δ hδ hδ
  · intro hp h ε hh hε
    exact (hp (min h ε) (lt_min hh hε)).mono fun k hk =>
      hk.mono (hN k) (min_le_left _ _) (min_le_right _ _)

end Submission.Obl.k4_scalar_terminal_chart_packet_extraction
