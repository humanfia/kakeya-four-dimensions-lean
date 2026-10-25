/- Adapted from this LOT tree, o114/x0680 commit133cc8c, Submission/Obl/k4_terminal_representative_atlas/Pairing/TopReduction.lean.
Existing attribution to o156/x0531,x0524,x0575 and accepted imports is retained below. -/

/- Adapted from this LOT tree, o156, session x0524 branch c7cfd90,
Submission/Obl/k4_terminal_local_sheet_pairing/TopReduction.lean. Original authorship/provenance is preserved below.
Namespace and imports adjusted for o114. -/

import Mathlib
import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.Interface

/-! The top-level reduction of o156 to one index at a time.

`OldSample … M D ε k` is the exact body of `trueSys` at index `k`, and
`PairedSample … M D ε k` the exact body of `paired` at index `k`. The statement follows
from a per-index step: for fixed output exponents `M D` and every `ε > 0` there is `ε' > 0`
such that eventually an old sample at tolerance `ε'` yields a paired sample at tolerance `ε`. -/

namespace Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

open MeasureTheory Filter

/-- The body of `trueSys` at one index. -/
def OldSample (N : ℕ → ℝ) (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ)
    (ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 6 → ℝ)))
    (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (B : (k : ℕ) → Fin (W k) → ℝ)
    (f : ℝ → ℝ) (L h : ℝ) (M D : ℕ) (ε : ℝ) (k : ℕ) : Prop :=
  ∃ κ : ℝ, 1 ≤ κ ∧ κ ≤ N k ^ ε ∧ ∃ T C' : ℕ, ∃ (γ : Fin C' → Fin (W k)) (j : Fin C' → Fin (2 ^ T)) (c u : Fin C' → EuclideanSpace ℝ (Fin 2)) (Q : Fin C' → Matrix (Fin 2) (Fin 2) ℝ) (R : Fin C' → MvPolynomial (Fin 4) ℝ) (A : Fin C' → Set (ℕ × (Fin 6 → ℝ))) (F : Fin C' → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)), N k ^ (h - ε) ≤ (2 : ℝ) ^ T ∧ (2 : ℝ) ^ T ≤ N k ^ (h + ε) ∧ (C' : ℝ) ≤ N k ^ M ∧ (∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b')) ∧ (∀ b, chart (N k) M D κ T ((j b : ℕ) : ℝ) L (B k (γ b)) (E k (γ b)) (c b) (u b) (Q b) (R b) (A b) (F b) (ENNReal.ofReal (N k ^ (-f L) * |Matrix.det (Q b)| / ((2 : ℝ) ^ T * κ)) ≤ ((ν k (γ b)).prod MeasureTheory.volume) (F b))) ∧ ENNReal.ofReal κ⁻¹ ≤ ∑ b, ENNReal.ofReal (ω k (γ b)) * ((ν k (γ b)).prod MeasureTheory.volume) (F b)

theorem trueSys_iff (N : ℕ → ℝ) (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ)
    (ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 6 → ℝ)))
    (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (B : (k : ℕ) → Fin (W k) → ℝ)
    (f : ℝ → ℝ) (L h : ℝ) :
    trueSys N W ω ν E B f L h ↔
      ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop, OldSample N W ω ν E B f L h M D ε k :=
  Iff.rfl

/-- The body of `paired` at one index. -/
def PairedSample (N : ℕ → ℝ) (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ)
    (ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 6 → ℝ)))
    (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (B : (k : ℕ) → Fin (W k) → ℝ)
    (L a h : ℝ) (M D : ℕ) (ε : ℝ) (k : ℕ) : Prop :=
  ∃ κ : ℝ, 1 ≤ κ ∧ κ ≤ N k ^ ε ∧ ∃ T m J : ℕ, ∃ (γ : Fin J → Fin (W k)) (j : Fin J → Fin (2 ^ T)) (c u : Fin J → EuclideanSpace ℝ (Fin 2)) (Q : Fin J → Matrix (Fin 2) (Fin 2) ℝ) (frame : Fin m → Fin J) (P : Fin m → MvPolynomial (Fin 4) ℝ) (S : Fin m → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (H : Fin m → Set ((ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ))) (β : Fin m → ℝ) (lst : Fin (W k) → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin m)), (2 : ℝ) ^ T ≤ N k ^ (h + ε) ∧ (m : ℝ) ≤ N k ^ M ∧ (J : ℝ) ≤ N k ^ M ∧ (∀ b, Matrix.det (Q b) ≠ 0 ∧ ‖c b‖ + ‖u b‖ ≤ N k ^ M ∧ (∑ i : Fin 2, ∑ i' : Fin 2, (|Q b i i'| + |(Q b)⁻¹ i i'|)) ≤ N k ^ M ∧ (∑ i : Fin 2, ∑ i' : Fin 2, |Q b i i'|) ≤ κ / (2 : ℝ) ^ T) ∧ (∀ s, (P s).totalDegree ≤ 2 ∧ (∀ d, |(P s).coeff d| ≤ N k ^ M) ∧ |MvPolynomial.eval (0 : Fin 4 → ℝ) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (P s)))| ≤ (δ (N k) L)⁻¹ ∧ (disc (P s)).totalDegree ≤ 2 ∧ (∀ d, |(disc (P s)).coeff d| ≤ N k ^ a)) ∧ (∀ s, MeasurableSet (S s) ∧ (∀ i, fmt 7 (N k ^ M) D {r : Fin 7 → ℝ | ((i, fun z : Fin 6 => r z.castSucc), r 6) ∈ S s}) ∧ ∀ p ∈ S s, p ∈ E k (γ (frame s)) ∧ (p.1.1 : ℝ) ≤ N k ^ M ∧ (∀ d, |p.1.2 d| ≤ N k ^ M) ∧ p.2 ∈ Set.Icc (((j (frame s) : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j (frame s) : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T) ∧ ∀ t ∈ Set.Icc (((j (frame s) : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j (frame s) : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T), ‖Matrix.toEuclideanLin (Q (frame s))⁻¹ (y p.1 t - c (frame s) - t • u (frame s))‖ ≤ κ ∧ |B k (γ (frame s)) * (x p.1 t) 3| ≤ N k ^ M ∧ ‖base T ((j (frame s) : ℕ) : ℝ) κ (c (frame s)) (u (frame s)) (Q (frame s)) p.1 t‖ ≤ (1 : ℝ) / 8 ∧ ∀ t' ∈ Set.Icc (((j (frame s) : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j (frame s) : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T), ‖base T ((j (frame s) : ℕ) : ℝ) κ (c (frame s)) (u (frame s)) (Q (frame s)) p.1 t - base T ((j (frame s) : ℕ) : ℝ) κ (c (frame s)) (u (frame s)) (Q (frame s)) p.1 t'‖ ≤ (2 : ℝ) ^ T * |t - t'|) ∧ (∀ s s', s ≠ s' → γ (frame s) = γ (frame s') → j (frame s) = j (frame s') → Disjoint (S s) (S s')) ∧ (∀ γ₀ o, ((lst γ₀ o).card : ℝ) ≤ κ) ∧ (∀ γ₀ s, MeasurableSet {p | s ∈ lst γ₀ (obs (B k γ₀) (δ (N k) L) p)} ∧ ∀ i, fmt 7 (N k ^ M) D {r : Fin 7 → ℝ | s ∈ lst γ₀ (obs (B k γ₀) (δ (N k) L) ((i, fun z : Fin 6 => r z.castSucc), r 6))}) ∧ (∀ s, MeasurableSet (H s) ∧ ∀ p ∈ H s, (p.1, p.2.1) ∈ S s ∧ p.2.2 ∈ Set.Icc (((j (frame s) : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j (frame s) : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T) ∧ (p.1, p.2.2) ∈ E k (γ (frame s)) ∧ ∃ s' ∈ lst (γ (frame s)) (obs (B k (γ (frame s))) (δ (N k) L) (p.1, p.2.2)), frame s' = frame s ∧ localPair (N k) a (δ (N k) L) ((2 : ℝ) ^ T) (P s) (P s') (base T ((j (frame s) : ℕ) : ℝ) κ (c (frame s)) (u (frame s)) (Q (frame s)) p.1 p.2.1) (base T ((j (frame s) : ℕ) : ℝ) κ (c (frame s)) (u (frame s)) (Q (frame s)) p.1) (fun t => B k (γ (frame s)) * (x p.1 t) 3) p.2.1 (Set.Icc (((j (frame s) : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j (frame s) : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T))) ∧ (∀ s, 0 ≤ β s ∧ ∀ U : Set (EuclideanSpace ℝ (Fin 3)), MeasurableSet U → ENNReal.ofReal ((2 : ℝ) ^ T) ^ 2 * ((ν k (γ (frame s))).prod (MeasureTheory.volume.prod MeasureTheory.volume)) (H s ∩ {p | base T ((j (frame s) : ℕ) : ℝ) κ (c (frame s)) (u (frame s)) (Q (frame s)) p.1 p.2.1 ∈ U}) ≤ ENNReal.ofReal (β s) * MeasureTheory.volume U) ∧ (∑ s, ω k (γ (frame s)) * β s / (2 : ℝ) ^ T) ≤ N k ^ a ∧ ENNReal.ofReal κ⁻¹ ≤ ∑ s, ENNReal.ofReal (ω k (γ (frame s)) * (2 : ℝ) ^ T) * ((ν k (γ (frame s))).prod (MeasureTheory.volume.prod MeasureTheory.volume)) (H s)

theorem paired_iff (N : ℕ → ℝ) (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ)
    (ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 6 → ℝ)))
    (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (B : (k : ℕ) → Fin (W k) → ℝ)
    (L a h : ℝ) :
    paired N W ω ν E B L a h ↔
      ((∀ k, 2 ≤ N k) ∧ Filter.Tendsto N Filter.atTop Filter.atTop ∧ 0 < L ∧ (∀ k γ, 0 ≤ ω k γ) ∧ (∀ k, (∑ γ, ω k γ) = 1) ∧ (∀ k γ, MeasureTheory.IsProbabilityMeasure (ν k γ)) ∧ (∃ Mb : ℕ, ∀ k γ, 0 < B k γ ∧ B k γ ≤ N k ^ Mb ∧ (B k γ)⁻¹ ≤ N k ^ Mb) ∧ (∃ Me De : ℕ, ∀ k γ, MeasurableSet (E k γ) ∧ ∀ i, fmt 7 (N k ^ Me) De {r : Fin 7 → ℝ | ((i, fun z : Fin 6 => r z.castSucc), r 6) ∈ E k γ}) ∧
        ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop, PairedSample N W ω ν E B L a h M D ε k) :=
  Iff.rfl

/-- The per-index step from which the statement follows. -/
def SampleStep : Prop :=
  ∀ (d₀ S η : ℝ), 0 < d₀ → d₀ < 1 → 0 < S → 0 < η → ∃ Cr cr : ℝ, 0 < Cr ∧ 0 < cr ∧
    ∀ N K L d W ω ν E P B f g G, prob N K L d S η W ω ν E P B f g G → d ≤ d₀ →
    ∀ h e : ℝ, 0 < e → e < h → e < cr * L → ∀ M' D' : ℕ, ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε →
    ∃ ε' : ℝ, 0 < ε' ∧ ∀ᶠ k in atTop,
      OldSample N W ω ν E B f L h M' D' ε' k → PairedSample N W ω ν E B L (Cr * e) (h - e) M D ε k

/-- **Top-level reduction.** -/
theorem statement_of_sampleStep (hstep : Matching → SampleStep) : Statement := by
  intro hM d₀ S η hd₁ hS hη
  by_cases hd₀ : 0 < d₀
  swap
  · refine ⟨1, 1, one_pos, one_pos, ?_⟩
    intro N K L d W ω ν E P B f g G hprob hd
    exfalso
    have hdpos : 0 < d := hprob.2.2.2.2.1
    linarith
  obtain ⟨Cr, cr, hCr, hcr, hmain⟩ := hstep hM d₀ S η hd₀ hd₁ hS hη
  refine ⟨Cr, cr, hCr, hcr, ?_⟩
  intro N K L d W ω ν E P B f g G hprob hd h e he heh hecr htrue
  obtain ⟨M', D', hold⟩ := (trueSys_iff N W ω ν E B f L h).mp htrue
  rw [paired_iff]
  have hprob' := hprob
  obtain ⟨hN2, hNt, -, hL, -, -, -, -, hrest⟩ := hprob'
  obtain ⟨⟨Mp, Dp, hworld⟩, -⟩ := hrest
  refine ⟨hN2, hNt, hL, fun k γ => (hworld k).2.1 γ, fun k => (hworld k).2.2.1, fun k γ => ((hworld k).2.2.2.1 γ).1,
    ⟨Mp, fun k γ => ⟨((hworld k).2.2.2.1 γ).2.1, ((hworld k).2.2.2.1 γ).2.2.1, ((hworld k).2.2.2.1 γ).2.2.2.1⟩⟩,
    ⟨Mp, Dp, fun k γ => ⟨((hworld k).2.2.2.1 γ).2.2.2.2.2.2.2.1, ((hworld k).2.2.2.1 γ).2.2.2.2.2.2.2.2.2.2.1⟩⟩, ?_⟩
  obtain ⟨M, D, hstepMD⟩ := hmain N K L d W ω ν E P B f g G hprob hd h e he heh hecr M' D'
  refine ⟨M, D, fun ε hε => ?_⟩
  obtain ⟨ε', hε', hev⟩ := hstepMD ε hε
  exact ((hold ε' hε').and_eventually hev).mono (fun k hk => hk.2 hk.1)

end Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing
