-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Interface, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
/- Named interface for o294. Common bindings are imported from accepted o288.
The new RowPacket and RowDiscoveryTail bindings are adapted verbatim from this
LOT tree, o287, x1070 fb6d7d14, SplitInterface.lean. -/
import Submission.Obl.k4_physical_parent_potential_candidates.PhysicalPotentialPacket

set_option linter.unusedVariables false

namespace Submission.Obl.k4_isotropic_path_improvement.S294

noncomputable section

abbrev Ln := Submission.Obl.k4_physical_parent_potential_candidates.Ln
abbrev Ev := Submission.Obl.k4_physical_parent_potential_candidates.Ev
abbrev P2 := Submission.Obl.k4_physical_parent_potential_candidates.P2
abbrev P3 := Submission.Obl.k4_physical_parent_potential_candidates.P3
abbrev P3c := Submission.Obl.k4_physical_parent_potential_candidates.P3c
abbrev Po := Submission.Obl.k4_physical_parent_potential_candidates.Po
abbrev Ob := Submission.Obl.k4_physical_parent_potential_candidates.Ob
abbrev exf := Submission.Obl.k4_physical_parent_potential_candidates.exf
abbrev xp := Submission.Obl.k4_physical_parent_potential_candidates.xp
abbrev mk := Submission.Obl.k4_physical_parent_potential_candidates.mk
abbrev x := Submission.Obl.k4_physical_parent_potential_candidates.x
abbrev y := Submission.Obl.k4_physical_parent_potential_candidates.y
abbrev v := Submission.Obl.k4_physical_parent_potential_candidates.v
abbrev δ := Submission.Obl.k4_physical_parent_potential_candidates.δ
abbrev obs := Submission.Obl.k4_physical_parent_potential_candidates.obs
abbrev fmt := Submission.Obl.k4_physical_parent_potential_candidates.fmt
abbrev ch := Submission.Obl.k4_physical_parent_potential_candidates.ch
abbrev pb := Submission.Obl.k4_physical_parent_potential_candidates.pb
abbrev path := Submission.Obl.k4_physical_parent_potential_candidates.path
abbrev atlas := Submission.Obl.k4_physical_parent_potential_candidates.atlas
abbrev sy := Submission.Obl.k4_physical_parent_potential_candidates.sy
abbrev wi := Submission.Obl.k4_physical_parent_potential_candidates.wi
abbrev grid := Submission.Obl.k4_physical_parent_potential_candidates.grid
abbrev narrow := Submission.Obl.k4_physical_parent_potential_candidates.narrow
abbrev JointJetBound := Submission.Obl.k4_physical_parent_potential_candidates.JointJetBound
abbrev PhysicalPotentialPacket := Submission.Obl.k4_physical_parent_potential_candidates.PhysicalPotentialPacket
abbrev packetBase := Submission.Obl.k4_physical_parent_potential_candidates.PhysicalPotentialData.packetBase
abbrev packetSignal := Submission.Obl.k4_physical_parent_potential_candidates.PhysicalPotentialData.packetSignal
abbrev physicalCode := Submission.Obl.k4_physical_parent_potential_candidates.PhysicalPotentialData.physicalCode

/-- The qualified row packet of one old block (new binding of both children). -/
def RowPacket := ((fun M Ep precision loss Nk L d₁ gain κ ν B r T j c u P A F H => (match (δ Nk r) with | a => (match ((((2 : ℝ) ^ T)⁻¹ : ℝ)) with | h => (match (δ Nk (precision * gain * L)) with | ζ => (match (packetBase T j c u) with | z => (match (packetSignal P) with | X => (match ((fun p => X p / a)) with | Xn => (match (ENNReal.ofReal h * ν A) with | ref => ∃ (K ε pv θ : ℝ) (Se Er : Set Ev) (st : Ev → ℕ) (Gs : ℕ → Fin 3 → ℝ) (pal : MeasureTheory.Measure (Fin 2 → ℤ)), MeasureTheory.IsProbabilityMeasure ν ∧ P.totalDegree ≤ 2 ∧ MeasurableSet A ∧ 0 < ε ∧ ε ≤ ζ ∧ ε ≤ (a / h) * ζ ∧ 0 < a ∧ a ≤ K * h ∧ h ≤ ζ ∧ ζ ≤ 1 ∧ 2 ≤ K ∧ κ ≤ K ∧ K ^ Ep ≤ Nk ^ (loss * gain * L) ∧ θ = (a / h) * ζ ^ Ep / K ^ Ep ∧ K ^ Ep * ε ≤ θ ∧ 0 < pv ∧ K ^ Ep * pv ≤ θ ∧ MeasurableSet Se ∧ Se ⊆ H ∩ F ∧ Se ⊆ Er ∧ (∀ p ∈ Se, p.1 ∈ A ∧ p.2 ∈ Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h) ∧ p.2 ∈ Set.Icc (0 : ℝ) 1) ∧ 0 < ref ∧ ref / ENNReal.ofReal K ≤ ((ν.prod MeasureTheory.volume).restrict Se) Set.univ ∧ (∀ p ∈ Se, ‖z p‖ ≤ K ∧ ‖v p.1‖ ≤ K ∧ (∀ t ∈ Set.Icc (0 : ℝ) 1, |MvPolynomial.eval (xp p.1 t) P| ≤ K ∧ |MvPolynomial.eval (xp p.1 t) (MvPolynomial.pderiv 3 P)| ≤ K * B ∧ |MvPolynomial.eval (xp p.1 t) (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 P))| ≤ K * B ^ 2) ∧ B / K ≤ |MvPolynomial.eval (xp p.1 p.2) (MvPolynomial.pderiv 3 P)|) ∧ (∀ U : Set P3, MeasurableSet U → ((ν.prod MeasureTheory.volume).restrict Se) {p | z p ∈ U} ≤ ENNReal.ofReal K * ref * MeasureTheory.volume U) ∧ (∀ (w : ℝ), ε ≤ w → w ≤ 1 → ∀ (U : Set P3), MeasurableSet U → ∀ f : P3 → ℝ, Measurable f → ((ν.prod MeasureTheory.volume).restrict Se) {p | z p ∈ U ∧ |Xn p - f (z p)| ≤ w} ≤ ENNReal.ofReal (K * w ^ d₁) * ref * MeasureTheory.volume U) ∧ (∀ p w : ℝ, ε ≤ p → p ≤ 1 → ε ≤ w → w ≤ 1 → K ^ (100 : ℕ) * h * p ≤ a * w → Set.Finite {k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ Se, (fun e => (fun i : Fin 3 => ⌊z e i / p⌋, ⌊Xn e / w⌋)) e = k} ∧ (({k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ Se, (fun e => (fun i : Fin 3 => ⌊z e i / p⌋, ⌊Xn e / w⌋)) e = k}).ncard : ℝ) ≤ K / (p ^ (3 : ℕ) * w ^ d₁)) ∧ Measurable st ∧ (st '' Se).Finite ∧ (∀ p p' : Ev, st p = st p' → physicalCode z Xn ε p = physicalCode z Xn ε p') ∧ (∀ k : ℕ, ∀ n : P2, ∀ t : ℝ, ‖n‖ = 1 → ((ν.prod MeasureTheory.volume).restrict Se) {p | st p = k ∧ |inner ℝ n (v p.1) - t| ≤ K ^ (-100 : ℝ)} ≤ (1 / 2000000000000 : ENNReal) * ((ν.prod MeasureTheory.volume).restrict Se) {p | st p = k}) ∧ MeasureTheory.IsProbabilityMeasure pal ∧ (∀ k : ℕ, ∀ b : Fin 2 → ℤ, ((ν.prod MeasureTheory.volume).restrict Se) {p | st p = k ∧ (fun i : Fin 2 => ⌊v p.1 i / pv⌋) = b} ≤ ENNReal.ofReal K * ((ν.prod MeasureTheory.volume).restrict Se) {p | st p = k} * pal {b}) ∧ (∀ k : ℕ, ∀ i : Fin 3, |Gs k i| ≤ K) ∧ (∀ p ∈ Se, |(∑ i : Fin 4, MvPolynomial.eval (xp p.1 p.2) (MvPolynomial.pderiv i P) * (![1, p.1.2 3, p.1.2 4, p.1.2 5] : Fin 4 → ℝ) i) - ∑ i : Fin 3, (![1, p.1.2 3, p.1.2 4] : Fin 3 → ℝ) i * Gs (st p) i| ≤ θ) ∧ (∀ c' : Fin 3 → ℝ, ∃ Fc : Finset (Fin 3 → ℤ), (Fc.card : ℝ) ≤ K ∧ ∀ p ∈ Er, (∀ i : Fin 3, |z p i - c' i| ≤ θ) → (fun i : Fin 3 => ⌊Gs (st p) i / θ⌋) ∈ Fc) ∧ ((ν.prod MeasureTheory.volume).restrict Se) {w | ¬ ∃ Pq : Fin 3 → Polynomial ℝ, (∀ i, (Pq i).natDegree ≤ M) ∧ (∀ i n, |(Pq i).coeff n| ≤ K) ∧ (∀ i, |Gs (st w) i - (Pq i).eval ((w.2 - (j : ℝ) * h) / h)| ≤ θ) ∧ ∃ Et : Set ℝ, MeasurableSet Et ∧ Et ⊆ Set.Icc (0 : ℝ) 1 ∧ ENNReal.ofReal (1 / K) ≤ MeasureTheory.volume Et ∧ ∀ s ∈ Et, ((w.1, (j : ℝ) * h + h * s) : Ev) ∈ Er ∧ ∀ i, |Gs (st (w.1, (j : ℝ) * h + h * s)) i - (Pq i).eval s| ≤ θ} ≤ (1 / 10000 : ENNReal) * ((ν.prod MeasureTheory.volume).restrict Se) Set.univ)))))))) : ℕ → ℕ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → MeasureTheory.Measure Ln → ℝ → ℝ → ℕ → ℕ → P2 → P2 → Po → Set Ln → Set Ev → Set Ev → Prop)

/-- The discovery tail of `k4_physical_row_packet_source`. -/
def RowDiscoveryTail := ((fun q M Ep precision loss d₁ κ₁ S η _ρ m s gain δ₀ u0 => ∀ N K L d W ω ν E P B f g G, pb N K L d S η W ω ν E P B f g G → (∀ r : ℝ, 0 ≤ r → r ≤ L → |f r - f 0 - d₁ * r| ≤ δ₀ * L) → ∀ Mp Dp : ℕ, ∃ M₀ D₀ : ℕ, ∀ Mi Di : ℕ, M₀ ≤ Mi → D₀ ≤ Di → ∀ τ : ℝ, 0 < τ → ∀ α : ℝ, 0 < α → α ≤ 1 → ∃ σ : ℝ, 0 < σ ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ r T nw κ C lev par γ j c u Q R A F lst, path (N k) L (W k) (ω k) (ν k) (E k) (B k) f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst → ∀ H : Fin (W k) → Set Ev, (∀ w, MeasurableSet (H w) ∧ H w ⊆ {p | ∃ b : Fin C, lev b = m - 1 ∧ γ b = w ∧ p ∈ F b}) → ENNReal.ofReal (κ⁻¹ / 2) ≤ ∑ w, ENNReal.ofReal (ω k w) * ((ν k w).prod MeasureTheory.volume) (H w) → (wi (N k) L (W k) (ω k) (ν k) (E k) (B k) m r T nw gain Mi Di τ ∨ narrow (N k) L (W k) (ω k) (ν k) (E k) (B k) m s r T nw gain u0 κ M₀ D₀ α C lev γ j A F H) ∨ ∃ b : Fin C, lev b < m ∧ r (lev b) + 2 * gain * L ≤ L ∧ (PhysicalPotentialPacket q precision loss (N k) L d₁ gain κ (ν k (γ b)) (B k (γ b)) (r (lev b)) (T (lev b)) (j b) (c b) (u b) (P k (γ b)) (A b) (F b) (H (γ b)) ∨ RowPacket M Ep precision loss (N k) L d₁ gain κ (ν k (γ b)) (B k (γ b)) (r (lev b)) (T (lev b)) (j b) (c b) (u b) (P k (γ b)) (A b) (F b) (H (γ b)))) : ℕ → ℕ → ℕ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℕ → (ℕ → ℝ) → ℝ → ℝ → ℝ → Prop)

/-- The frozen statement of `k4_physical_row_packet_source` (it has no `mk` hypothesis). -/
def RowSourceAssertion : Prop := ∀ d₁ κ₁ S η ρ : ℝ, 0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 → 0 < S → 0 < η → 0 < ρ → d₁ + ρ < 1 → ∃ M : ℕ, 1 ≤ M ∧ ∀ Ep : ℕ, ∀ D₀ : ℕ, ∃ D : ℕ, D₀ ≤ D ∧ max 5186 (864 * (2 * ((3 * M + 1) + 2)) + 2) ≤ D ∧ ∀ J : ℕ, 1 ≤ J → JointJetBound D J → ∀ precision : ℝ, 1 ≤ precision → ∀ loss : ℝ, 0 < loss → loss ≤ 1 → ∀ e0 : ℝ, 0 < e0 → ∃ (m : ℕ) (s : ℕ → ℝ) (gain δ₀ u0 : ℝ), grid κ₁ ρ m s gain δ₀ u0 ∧ gain ≤ e0 ∧ RowDiscoveryTail (3 * M + 1) M Ep precision loss d₁ κ₁ S η ρ m s gain δ₀ u0

end

end Submission.Obl.k4_isotropic_path_improvement.S294
