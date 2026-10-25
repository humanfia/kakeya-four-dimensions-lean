-- Adapted from this LOT tree, o206, session x0709, commit f7d6ac58,
-- Submission/Obl/k4_coarse_pair_frame_preparation/Wrapper.lean.
import Submission.Obl.k4_homogeneous_native_pair_preparation.Interface

/-!
# The sequence-level wrapper of o206

`known` and `tested` are cofinal predicates: `∃ M D, ∀ ε > 0, ∃ᶠ k, (one sample at k)`.
`prob` supplies facts for every `k` and three eventual facts: `K k ≤ N k ^ ε`, the typical
density bounds at a depth `r` with tolerance `τ`, and the angular typical bounds.

* `KnownAt` / `TestedAt`: one sample of `known` / of `tested`, with the exact bodies of the
  frozen definitions (`known_iff`, `tested_iff` are `Iff.rfl`).  `KnownSample` /
  `TestedSample` are the same as records over the `k`-th slices (`knownAt_iff`,
  `testedAt_iff`).  The record `TestedSample` follows session x0524's `TestedSample.lean`
  (o156 repository, branch x0524, commit c7cfd90) as adapted by x0472
  (`PrepInterface.lean`, o104 repository, branch x0472); same field names.
* `TypAt` / `AngTypAt`: the typical bounds of `prob` at one index.
* `SampleStep`: the per-sample construction.  For each tolerance `ε` it names finitely many
  (depth, tolerance) pairs of typical bounds it uses; given a common positive exponent `c₀`
  of these bounds it chooses the old tolerance `ε₀` and a size `N₀`, and from the old known
  sample at an index `k` with `N₀ ≤ N k`, `K k ≤ N k ^ ε₀` and the typical bounds at `k`
  it builds the sample of `tested False 4` at `k`.
* `statement_of_sampleStep : SampleStep → PreparationStatement`: the global conjuncts of
  `tested` come from `prob`; frequently (`known`) and eventually (`prob`) is frequently.
-/

namespace Submission.Obl.k4_homogeneous_native_pair_preparation

open MeasureTheory Filter

set_option linter.unusedVariables false

/-! ### One sample of `known` -/

/-- One sample of `known` at index `k`: the body of the frozen `known` after `∃ᶠ k`. -/
def KnownAt (N : ℕ → ℝ) (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 6 → ℝ))) (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (B : (k : ℕ) → Fin (W k) → ℝ)
    (f : ℝ → ℝ) (L h : ℝ) (M D : ℕ) (ε : ℝ) (k : ℕ) : Prop :=
  ∃ κ : ℝ, 1 ≤ κ ∧ κ ≤ N k ^ ε ∧ ∃ T C' : ℕ, ∃ (γ : Fin C' → Fin (W k)) (j : Fin C' → Fin (2 ^ T)) (c u : Fin C' → EuclideanSpace ℝ (Fin 2)) (Q : Fin C' → Matrix (Fin 2) (Fin 2) ℝ) (R : Fin C' → MvPolynomial (Fin 4) ℝ) (A : Fin C' → Set (ℕ × (Fin 6 → ℝ))) (F : Fin C' → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (lst : Fin (W k) → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C')), N k ^ (h - ε) ≤ (2 : ℝ) ^ T ∧ (2 : ℝ) ^ T ≤ N k ^ (h + ε) ∧ (C' : ℝ) ≤ N k ^ M ∧ (∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b')) ∧ (∀ b, chart (N k) M D κ T ((j b : ℕ) : ℝ) L (B k (γ b)) (E k (γ b)) (c b) (u b) (Q b) (R b) (A b) (F b) (ENNReal.ofReal (N k ^ (-f L) * |Matrix.det (Q b)| / ((2 : ℝ) ^ T * κ)) ≤ ((ν k (γ b)).prod MeasureTheory.volume) (F b) ∧ ∀ p ∈ F b, b ∈ lst (γ b) (obs (B k (γ b)) (δ (N k) L) p))) ∧ ENNReal.ofReal κ⁻¹ ≤ ∑ b, ENNReal.ofReal (ω k (γ b)) * ((ν k (γ b)).prod MeasureTheory.volume) (F b) ∧ (∀ γ₀ o, ((lst γ₀ o).card : ℝ) ≤ κ) ∧ (∀ γ₀ b, MeasurableSet {p | b ∈ lst γ₀ (obs (B k γ₀) (δ (N k) L) p)} ∧ ∀ i, fmt 7 (N k ^ M) D {r : Fin 7 → ℝ | b ∈ lst γ₀ (obs (B k γ₀) (δ (N k) L) ((i, fun z : Fin 6 => r z.castSucc), r 6))})

theorem known_iff (N : ℕ → ℝ) (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 6 → ℝ))) (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (B : (k : ℕ) → Fin (W k) → ℝ)
    (f : ℝ → ℝ) (L h : ℝ) :
    known N W ω ν E B f L h ↔
      ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop, KnownAt N W ω ν E B f L h M D ε k :=
  Iff.rfl

/-- One sample of `known` as a record over the `k`-th slices. -/
structure KnownSample (Nk : ℝ) (Wk : ℕ) (ωk : Fin Wk → ℝ) (νk : Fin Wk → Measure (ℕ × (Fin 6 → ℝ))) (Ek : Fin Wk → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (Bk : Fin Wk → ℝ)
    (f : ℝ → ℝ) (L h : ℝ) (M D : ℕ) (ε : ℝ) where
  κ : ℝ
  κ_one : 1 ≤ κ
  κ_le : κ ≤ Nk ^ ε
  T : ℕ
  C' : ℕ
  γ : Fin C' → Fin Wk
  j : Fin C' → Fin (2 ^ T)
  c : Fin C' → EuclideanSpace ℝ (Fin 2)
  u : Fin C' → EuclideanSpace ℝ (Fin 2)
  Q : Fin C' → Matrix (Fin 2) (Fin 2) ℝ
  R : Fin C' → MvPolynomial (Fin 4) ℝ
  A : Fin C' → Set (ℕ × (Fin 6 → ℝ))
  F : Fin C' → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)
  lst : Fin Wk → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C')
  hT₁ : Nk ^ (h - ε) ≤ (2 : ℝ) ^ T
  hT₂ : (2 : ℝ) ^ T ≤ Nk ^ (h + ε)
  hC : (C' : ℝ) ≤ Nk ^ M
  hdisj : (∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b'))
  hchart : (∀ b, chart (Nk) M D κ T ((j b : ℕ) : ℝ) L (Bk (γ b)) (Ek (γ b)) (c b) (u b) (Q b) (R b) (A b) (F b) (ENNReal.ofReal (Nk ^ (-f L) * |Matrix.det (Q b)| / ((2 : ℝ) ^ T * κ)) ≤ ((νk (γ b)).prod MeasureTheory.volume) (F b) ∧ ∀ p ∈ F b, b ∈ lst (γ b) (obs (Bk (γ b)) (δ (Nk) L) p)))
  hcov : ENNReal.ofReal κ⁻¹ ≤ ∑ b, ENNReal.ofReal (ωk (γ b)) * ((νk (γ b)).prod MeasureTheory.volume) (F b)
  hlst : (∀ γ₀ o, ((lst γ₀ o).card : ℝ) ≤ κ)
  hlstfmt : (∀ γ₀ b, MeasurableSet {p | b ∈ lst γ₀ (obs (Bk γ₀) (δ (Nk) L) p)} ∧ ∀ i, fmt 7 (Nk ^ M) D {r : Fin 7 → ℝ | b ∈ lst γ₀ (obs (Bk γ₀) (δ (Nk) L) ((i, fun z : Fin 6 => r z.castSucc), r 6))})

theorem knownAt_iff (N : ℕ → ℝ) (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 6 → ℝ))) (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (B : (k : ℕ) → Fin (W k) → ℝ)
    (f : ℝ → ℝ) (L h : ℝ) (M D : ℕ) (ε : ℝ) (k : ℕ) :
    KnownAt N W ω ν E B f L h M D ε k ↔
      Nonempty (KnownSample (N k) (W k) (ω k) (ν k) (E k) (B k) f L h M D ε) := by
  constructor
  · rintro ⟨κ, κ_one, κ_le, T, C', γ, j, c, u, Q, R, A, F, lst, hT₁, hT₂, hC, hdisj, hchart, hcov, hlst, hlstfmt⟩
    exact ⟨⟨κ, κ_one, κ_le, T, C', γ, j, c, u, Q, R, A, F, lst, hT₁, hT₂, hC, hdisj, hchart, hcov, hlst, hlstfmt⟩⟩
  · rintro ⟨s⟩
    exact ⟨s.κ, s.κ_one, s.κ_le, s.T, s.C', s.γ, s.j, s.c, s.u, s.Q, s.R, s.A, s.F, s.lst, s.hT₁, s.hT₂, s.hC, s.hdisj, s.hchart, s.hcov, s.hlst, s.hlstfmt⟩

end Submission.Obl.k4_homogeneous_native_pair_preparation
