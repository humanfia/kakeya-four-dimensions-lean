-- Adapted from this LOT tree, o287 (k4_physical_parent_potential_source), session x1070
-- (the split of o287), branch x1070, commit fb6d7d14, file
-- Submission/Obl/k4_physical_parent_potential_source/SplitInterface.lean: the `RowPacket`
-- binding and the named frozen statement, verbatim, over the ported `Interface`.
/-
Named forms of the frozen statement of o295 (`k4_physical_row_packet_potential`):
`RowPacket` is its new `match` binding, verbatim; `PhysicalPotentialPacket` and the
other bindings are those of `Interface`.
-/
import Submission.Obl.k4_physical_row_packet_potential.Interface

set_option linter.unusedVariables false

namespace Submission.Obl.k4_physical_row_packet_potential

noncomputable section

/-- The qualified row packet of one old block (new binding of both children). -/
def RowPacket := ((fun M Ep precision loss Nk L d₁ gain κ ν B r T j c u P A F H => (match (δ Nk r) with | a => (match ((((2 : ℝ) ^ T)⁻¹ : ℝ)) with | h => (match (δ Nk (precision * gain * L)) with | ζ => (match (packetBase T j c u) with | z => (match (packetSignal P) with | X => (match ((fun p => X p / a)) with | Xn => (match (ENNReal.ofReal h * ν A) with | ref => ∃ (K ε pv θ : ℝ) (Se Er : Set Ev) (st : Ev → ℕ) (Gs : ℕ → Fin 3 → ℝ) (pal : MeasureTheory.Measure (Fin 2 → ℤ)), MeasureTheory.IsProbabilityMeasure ν ∧ P.totalDegree ≤ 2 ∧ MeasurableSet A ∧ 0 < ε ∧ ε ≤ ζ ∧ ε ≤ (a / h) * ζ ∧ 0 < a ∧ a ≤ K * h ∧ h ≤ ζ ∧ ζ ≤ 1 ∧ 2 ≤ K ∧ κ ≤ K ∧ K ^ Ep ≤ Nk ^ (loss * gain * L) ∧ θ = (a / h) * ζ ^ Ep / K ^ Ep ∧ K ^ Ep * ε ≤ θ ∧ 0 < pv ∧ K ^ Ep * pv ≤ θ ∧ MeasurableSet Se ∧ Se ⊆ H ∩ F ∧ Se ⊆ Er ∧ (∀ p ∈ Se, p.1 ∈ A ∧ p.2 ∈ Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h) ∧ p.2 ∈ Set.Icc (0 : ℝ) 1) ∧ 0 < ref ∧ ref / ENNReal.ofReal K ≤ ((ν.prod MeasureTheory.volume).restrict Se) Set.univ ∧ (∀ p ∈ Se, ‖z p‖ ≤ K ∧ ‖v p.1‖ ≤ K ∧ (∀ t ∈ Set.Icc (0 : ℝ) 1, |MvPolynomial.eval (xp p.1 t) P| ≤ K ∧ |MvPolynomial.eval (xp p.1 t) (MvPolynomial.pderiv 3 P)| ≤ K * B ∧ |MvPolynomial.eval (xp p.1 t) (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 P))| ≤ K * B ^ 2) ∧ B / K ≤ |MvPolynomial.eval (xp p.1 p.2) (MvPolynomial.pderiv 3 P)|) ∧ (∀ U : Set P3, MeasurableSet U → ((ν.prod MeasureTheory.volume).restrict Se) {p | z p ∈ U} ≤ ENNReal.ofReal K * ref * MeasureTheory.volume U) ∧ (∀ (w : ℝ), ε ≤ w → w ≤ 1 → ∀ (U : Set P3), MeasurableSet U → ∀ f : P3 → ℝ, Measurable f → ((ν.prod MeasureTheory.volume).restrict Se) {p | z p ∈ U ∧ |Xn p - f (z p)| ≤ w} ≤ ENNReal.ofReal (K * w ^ d₁) * ref * MeasureTheory.volume U) ∧ (∀ p w : ℝ, ε ≤ p → p ≤ 1 → ε ≤ w → w ≤ 1 → K ^ (100 : ℕ) * h * p ≤ a * w → Set.Finite {k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ Se, (fun e => (fun i : Fin 3 => ⌊z e i / p⌋, ⌊Xn e / w⌋)) e = k} ∧ (({k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ Se, (fun e => (fun i : Fin 3 => ⌊z e i / p⌋, ⌊Xn e / w⌋)) e = k}).ncard : ℝ) ≤ K / (p ^ (3 : ℕ) * w ^ d₁)) ∧ Measurable st ∧ (st '' Se).Finite ∧ (∀ p p' : Ev, st p = st p' → physicalCode z Xn ε p = physicalCode z Xn ε p') ∧ (∀ k : ℕ, ∀ n : P2, ∀ t : ℝ, ‖n‖ = 1 → ((ν.prod MeasureTheory.volume).restrict Se) {p | st p = k ∧ |inner ℝ n (v p.1) - t| ≤ K ^ (-100 : ℝ)} ≤ (1 / 2000000000000 : ENNReal) * ((ν.prod MeasureTheory.volume).restrict Se) {p | st p = k}) ∧ MeasureTheory.IsProbabilityMeasure pal ∧ (∀ k : ℕ, ∀ b : Fin 2 → ℤ, ((ν.prod MeasureTheory.volume).restrict Se) {p | st p = k ∧ (fun i : Fin 2 => ⌊v p.1 i / pv⌋) = b} ≤ ENNReal.ofReal K * ((ν.prod MeasureTheory.volume).restrict Se) {p | st p = k} * pal {b}) ∧ (∀ k : ℕ, ∀ i : Fin 3, |Gs k i| ≤ K) ∧ (∀ p ∈ Se, |(∑ i : Fin 4, MvPolynomial.eval (xp p.1 p.2) (MvPolynomial.pderiv i P) * (![1, p.1.2 3, p.1.2 4, p.1.2 5] : Fin 4 → ℝ) i) - ∑ i : Fin 3, (![1, p.1.2 3, p.1.2 4] : Fin 3 → ℝ) i * Gs (st p) i| ≤ θ) ∧ (∀ c' : Fin 3 → ℝ, ∃ Fc : Finset (Fin 3 → ℤ), (Fc.card : ℝ) ≤ K ∧ ∀ p ∈ Er, (∀ i : Fin 3, |z p i - c' i| ≤ θ) → (fun i : Fin 3 => ⌊Gs (st p) i / θ⌋) ∈ Fc) ∧ ((ν.prod MeasureTheory.volume).restrict Se) {w | ¬ ∃ Pq : Fin 3 → Polynomial ℝ, (∀ i, (Pq i).natDegree ≤ M) ∧ (∀ i n, |(Pq i).coeff n| ≤ K) ∧ (∀ i, |Gs (st w) i - (Pq i).eval ((w.2 - (j : ℝ) * h) / h)| ≤ θ) ∧ ∃ Et : Set ℝ, MeasurableSet Et ∧ Et ⊆ Set.Icc (0 : ℝ) 1 ∧ ENNReal.ofReal (1 / K) ≤ MeasureTheory.volume Et ∧ ∀ s ∈ Et, ((w.1, (j : ℝ) * h + h * s) : Ev) ∈ Er ∧ ∀ i, |Gs (st (w.1, (j : ℝ) * h + h * s)) i - (Pq i).eval s| ≤ θ} ≤ (1 / 10000 : ENNReal) * ((ν.prod MeasureTheory.volume).restrict Se) Set.univ)))))))) : ℕ → ℕ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → MeasureTheory.Measure Ln → ℝ → ℝ → ℕ → ℕ → P2 → P2 → Po → Set Ln → Set Ev → Set Ev → Prop)


/-- The frozen statement of `k4_physical_row_packet_potential`. -/
def RowPotentialAssertion : Prop := ∀ M : ℕ, ∀ d₁ : ℝ, 0 ≤ d₁ → d₁ < 1 → ∃ Ep : ℕ, ∀ q : ℕ, 3 * M + 1 ≤ q → ∀ (precision loss Nk L gain κ : ℝ) (ν : MeasureTheory.Measure Ln) (B r : ℝ) (T j : ℕ) (c u : P2) (P : Po) (A : Set Ln) (F H : Set Ev), RowPacket M Ep precision loss Nk L d₁ gain κ ν B r T j c u P A F H → PhysicalPotentialPacket q precision loss Nk L d₁ gain κ ν B r T j c u P A F H

end

end Submission.Obl.k4_physical_row_packet_potential
