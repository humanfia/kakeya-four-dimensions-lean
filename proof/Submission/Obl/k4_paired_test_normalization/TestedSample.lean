-- Adapted from this LOT tree, o156, session x0524, commit86ade225;
-- Submission/Obl/k4_terminal_local_sheet_pairing/TestedSample.lean. Existing attribution comments are retained below.

import Submission.Obl.k4_paired_test_normalization.Interface
import Submission.Obl.k4_paired_test_normalization.SplitStatements

/-! Exact per-sample record for x0575's split interface, recorded in this tree
at commit401a7a3 in SplitStatements.lean. -/

namespace Submission.Obl.k4_paired_test_normalization.NormalizationStep

open MeasureTheory Set Filter

abbrev Trajectory := ℕ × (Fin 6 → ℝ)
abbrev Incidence := Trajectory × ℝ
abbrev PairPoint := Trajectory × (ℝ × ℝ)

structure TestedSample (cv : Prop) (lam Nk : ℝ) (Wk : ℕ)
    (ωk : Fin Wk → ℝ) (νk : Fin Wk → Measure Trajectory)
    (Ek : Fin Wk → Set Incidence) (Bk : Fin Wk → ℝ)
    (L dc a h : ℝ) (M D : ℕ) (ε : ℝ) where
  κ : ℝ
  κ_one : 1 ≤ κ
  κ_le : κ ≤ Nk ^ ε
  σ : ℝ
  σ_pos : 0 < σ
  T : ℕ
  m : ℕ
  J : ℕ
  γ : Fin J → Fin Wk
  j : Fin J → Fin (2 ^ T)
  c : Fin J → EuclideanSpace ℝ (Fin 2)
  u : Fin J → EuclideanSpace ℝ (Fin 2)
  Q : Fin J → Matrix (Fin 2) (Fin 2) ℝ
  frame : Fin m → Fin J
  P : Fin m → MvPolynomial (Fin 4) ℝ
  S : Fin m → Set Incidence
  H : Fin m → Fin m → Set PairPoint
  β : Fin m → ℝ
  lst : Fin Wk → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin m)
  hT : (2 : ℝ) ^ T ≤ Nk ^ (h + ε)
  hm : (m : ℝ) ≤ Nk ^ M
  hJ : (J : ℝ) ≤ Nk ^ M
  hframe : (∀ b, Matrix.det (Q b) ≠ 0 ∧ ‖c b‖ + ‖u b‖ ≤ Nk ^ M ∧ (∑ i : Fin 2, ∑ i' : Fin 2, (|Q b i i'| + |(Q b)⁻¹ i i'|)) ≤ Nk ^ M ∧ (∑ i : Fin 2, ∑ i' : Fin 2, |Q b i i'|) ≤ κ / (2 : ℝ) ^ T)
  hP : (∀ s, (P s).totalDegree ≤ 2 ∧ (∀ d, |(P s).coeff d| ≤ Nk ^ M) ∧ (cv → |MvPolynomial.eval (0 : Fin 4 → ℝ) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (P s)))| ≤ (δ (Nk) L)⁻¹ ∧ (disc (P s)).totalDegree ≤ 2 ∧ (∀ d, |(disc (P s)).coeff d| ≤ Nk ^ a)))
  hS : (∀ s, MeasurableSet (S s) ∧ (∀ i, fmt 7 (Nk ^ M) D {r : Fin 7 → ℝ | ((i, fun z : Fin 6 => r z.castSucc), r 6) ∈ S s}) ∧ ∀ p ∈ S s, p ∈ Ek (γ (frame s)) ∧ (p.1.1 : ℝ) ≤ Nk ^ M ∧ (∀ d, |p.1.2 d| ≤ Nk ^ M) ∧ p.2 ∈ Set.Icc (((j (frame s) : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j (frame s) : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T) ∧ ∀ t ∈ Set.Icc (((j (frame s) : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j (frame s) : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T), ‖Matrix.toEuclideanLin (Q (frame s))⁻¹ (y p.1 t - c (frame s) - t • u (frame s))‖ ≤ κ ∧ |Bk (γ (frame s)) * (x p.1 t) 3| ≤ Nk ^ M ∧ ‖base T ((j (frame s) : ℕ) : ℝ) κ (c (frame s)) (u (frame s)) (Q (frame s)) p.1 t‖ ≤ (1 : ℝ) / 8 ∧ ∀ t' ∈ Set.Icc (((j (frame s) : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j (frame s) : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T), ‖base T ((j (frame s) : ℕ) : ℝ) κ (c (frame s)) (u (frame s)) (Q (frame s)) p.1 t - base T ((j (frame s) : ℕ) : ℝ) κ (c (frame s)) (u (frame s)) (Q (frame s)) p.1 t'‖ ≤ (2 : ℝ) ^ T * |t - t'|)
  hdisj : (∀ s s', s ≠ s' → γ (frame s) = γ (frame s') → j (frame s) = j (frame s') → Disjoint (S s) (S s'))
  hlst : (∀ γ₀ o, ((lst γ₀ o).card : ℝ) ≤ κ)
  hlstfmt : (∀ γ₀ s, MeasurableSet {p | s ∈ lst γ₀ (obs (Bk γ₀) (δ (Nk) L) p)} ∧ ∀ i, fmt 7 (Nk ^ M) D {r : Fin 7 → ℝ | s ∈ lst γ₀ (obs (Bk γ₀) (δ (Nk) L) ((i, fun z : Fin 6 => r z.castSucc), r 6))})
  hH : (∀ s s', MeasurableSet (H s s') ∧ ∀ p ∈ H s s', (p.1, p.2.1) ∈ S s ∧ p.2.2 ∈ Set.Icc (((j (frame s) : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j (frame s) : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T) ∧ (p.1, p.2.2) ∈ Ek (γ (frame s)) ∧ s' ∈ lst (γ (frame s)) (obs (Bk (γ (frame s))) (δ (Nk) L) (p.1, p.2.2)) ∧ frame s' = frame s ∧ SplitStatements.tst (Nk) a (δ (Nk) L) (P s) (P s') (base T ((j (frame s) : ℕ) : ℝ) κ (c (frame s)) (u (frame s)) (Q (frame s)) p.1) (fun t => Bk (γ (frame s)) * (x p.1 t) 3) p.2.1 (Set.Icc (((j (frame s) : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j (frame s) : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T)) cv)
  hβ : (∀ s, 0 ≤ β s ∧ β s ≤ σ * Nk ^ a ∧ ∀ U : Set (EuclideanSpace ℝ (Fin 3)), MeasurableSet U → ENNReal.ofReal ((2 : ℝ) ^ T) ^ 2 * ((νk (γ (frame s))).prod (MeasureTheory.volume.prod MeasureTheory.volume)) {p | (∃ s', p ∈ H s s') ∧ base T ((j (frame s) : ℕ) : ℝ) κ (c (frame s)) (u (frame s)) (Q (frame s)) p.1 p.2.1 ∈ U} ≤ ENNReal.ofReal (β s) * MeasureTheory.volume U ∧ ENNReal.ofReal ((2 : ℝ) ^ T) ^ 2 * ((νk (γ (frame s))).prod (MeasureTheory.volume.prod MeasureTheory.volume)) {p | (∃ s', p ∈ H s' s) ∧ base T ((j (frame s) : ℕ) : ℝ) κ (c (frame s)) (u (frame s)) (Q (frame s)) p.1 p.2.1 ∈ U} ≤ ENNReal.ofReal (β s) * MeasureTheory.volume U)
  hcount : (∀ (γ₀ : Fin (Wk)) (j₀ : Fin (2 ^ T)), ((Finset.univ.filter (fun s : Fin m => γ (frame s) = γ₀ ∧ j (frame s) = j₀)).card : ℝ) ≤ Nk ^ a / σ)
  hband : (∀ (b : Fin J) (ρ : ℝ) (U : Set (EuclideanSpace ℝ (Fin 3))) (g : EuclideanSpace ℝ (Fin 3) → ℝ), 0 < ρ → MeasurableSet U → Measurable g → ENNReal.ofReal ((2 : ℝ) ^ T) ^ 2 * ((νk (γ b)).prod (MeasureTheory.volume.prod MeasureTheory.volume)) {p | (∃ s s', frame s = b ∧ p ∈ H s s') ∧ base T ((j b : ℕ) : ℝ) κ (c b) (u b) (Q b) p.1 p.2.1 ∈ U ∧ |Bk (γ b) * (x p.1 p.2.1) 3 - g (base T ((j b : ℕ) : ℝ) κ (c b) (u b) (Q b) p.1 p.2.1)| ≤ ρ} ≤ ENNReal.ofReal (σ * Nk ^ a * (max ρ (δ (Nk) L) / δ (Nk) L) ^ dc) * MeasureTheory.volume U)
  hcoverage : ENNReal.ofReal (lam * κ⁻¹) ≤ ∑ s, ENNReal.ofReal (ωk (γ (frame s)) * (2 : ℝ) ^ T) * ((νk (γ (frame s))).prod (MeasureTheory.volume.prod MeasureTheory.volume)) {p | ∃ s', p ∈ H s s'}

/-- The existential form of one frozen tested sample. -/
noncomputable def TestedAt (cv : Prop) (lam Nk : ℝ) (Wk : ℕ)
    (ωk : Fin Wk → ℝ) (νk : Fin Wk → Measure Trajectory)
    (Ek : Fin Wk → Set Incidence) (Bk : Fin Wk → ℝ)
    (L dc a h : ℝ) (M D : ℕ) (ε : ℝ) : Prop :=
  ∃ κ : ℝ, 1 ≤ κ ∧ κ ≤ Nk ^ ε ∧ ∃ σ : ℝ, 0 < σ ∧ ∃ T m J : ℕ, ∃ (γ : Fin J → Fin (Wk)) (j : Fin J → Fin (2 ^ T)) (c u : Fin J → EuclideanSpace ℝ (Fin 2)) (Q : Fin J → Matrix (Fin 2) (Fin 2) ℝ) (frame : Fin m → Fin J) (P : Fin m → MvPolynomial (Fin 4) ℝ) (S : Fin m → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (H : Fin m → Fin m → Set ((ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ))) (β : Fin m → ℝ) (lst : Fin (Wk) → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin m)), (2 : ℝ) ^ T ≤ Nk ^ (h + ε) ∧ (m : ℝ) ≤ Nk ^ M ∧ (J : ℝ) ≤ Nk ^ M ∧ (∀ b, Matrix.det (Q b) ≠ 0 ∧ ‖c b‖ + ‖u b‖ ≤ Nk ^ M ∧ (∑ i : Fin 2, ∑ i' : Fin 2, (|Q b i i'| + |(Q b)⁻¹ i i'|)) ≤ Nk ^ M ∧ (∑ i : Fin 2, ∑ i' : Fin 2, |Q b i i'|) ≤ κ / (2 : ℝ) ^ T) ∧ (∀ s, (P s).totalDegree ≤ 2 ∧ (∀ d, |(P s).coeff d| ≤ Nk ^ M) ∧ (cv → |MvPolynomial.eval (0 : Fin 4 → ℝ) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (P s)))| ≤ (δ (Nk) L)⁻¹ ∧ (disc (P s)).totalDegree ≤ 2 ∧ (∀ d, |(disc (P s)).coeff d| ≤ Nk ^ a))) ∧ (∀ s, MeasurableSet (S s) ∧ (∀ i, fmt 7 (Nk ^ M) D {r : Fin 7 → ℝ | ((i, fun z : Fin 6 => r z.castSucc), r 6) ∈ S s}) ∧ ∀ p ∈ S s, p ∈ Ek (γ (frame s)) ∧ (p.1.1 : ℝ) ≤ Nk ^ M ∧ (∀ d, |p.1.2 d| ≤ Nk ^ M) ∧ p.2 ∈ Set.Icc (((j (frame s) : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j (frame s) : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T) ∧ ∀ t ∈ Set.Icc (((j (frame s) : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j (frame s) : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T), ‖Matrix.toEuclideanLin (Q (frame s))⁻¹ (y p.1 t - c (frame s) - t • u (frame s))‖ ≤ κ ∧ |Bk (γ (frame s)) * (x p.1 t) 3| ≤ Nk ^ M ∧ ‖base T ((j (frame s) : ℕ) : ℝ) κ (c (frame s)) (u (frame s)) (Q (frame s)) p.1 t‖ ≤ (1 : ℝ) / 8 ∧ ∀ t' ∈ Set.Icc (((j (frame s) : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j (frame s) : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T), ‖base T ((j (frame s) : ℕ) : ℝ) κ (c (frame s)) (u (frame s)) (Q (frame s)) p.1 t - base T ((j (frame s) : ℕ) : ℝ) κ (c (frame s)) (u (frame s)) (Q (frame s)) p.1 t'‖ ≤ (2 : ℝ) ^ T * |t - t'|) ∧ (∀ s s', s ≠ s' → γ (frame s) = γ (frame s') → j (frame s) = j (frame s') → Disjoint (S s) (S s')) ∧ (∀ γ₀ o, ((lst γ₀ o).card : ℝ) ≤ κ) ∧ (∀ γ₀ s, MeasurableSet {p | s ∈ lst γ₀ (obs (Bk γ₀) (δ (Nk) L) p)} ∧ ∀ i, fmt 7 (Nk ^ M) D {r : Fin 7 → ℝ | s ∈ lst γ₀ (obs (Bk γ₀) (δ (Nk) L) ((i, fun z : Fin 6 => r z.castSucc), r 6))}) ∧ (∀ s s', MeasurableSet (H s s') ∧ ∀ p ∈ H s s', (p.1, p.2.1) ∈ S s ∧ p.2.2 ∈ Set.Icc (((j (frame s) : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j (frame s) : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T) ∧ (p.1, p.2.2) ∈ Ek (γ (frame s)) ∧ s' ∈ lst (γ (frame s)) (obs (Bk (γ (frame s))) (δ (Nk) L) (p.1, p.2.2)) ∧ frame s' = frame s ∧ SplitStatements.tst (Nk) a (δ (Nk) L) (P s) (P s') (base T ((j (frame s) : ℕ) : ℝ) κ (c (frame s)) (u (frame s)) (Q (frame s)) p.1) (fun t => Bk (γ (frame s)) * (x p.1 t) 3) p.2.1 (Set.Icc (((j (frame s) : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j (frame s) : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T)) cv) ∧ (∀ s, 0 ≤ β s ∧ β s ≤ σ * Nk ^ a ∧ ∀ U : Set (EuclideanSpace ℝ (Fin 3)), MeasurableSet U → ENNReal.ofReal ((2 : ℝ) ^ T) ^ 2 * ((νk (γ (frame s))).prod (MeasureTheory.volume.prod MeasureTheory.volume)) {p | (∃ s', p ∈ H s s') ∧ base T ((j (frame s) : ℕ) : ℝ) κ (c (frame s)) (u (frame s)) (Q (frame s)) p.1 p.2.1 ∈ U} ≤ ENNReal.ofReal (β s) * MeasureTheory.volume U ∧ ENNReal.ofReal ((2 : ℝ) ^ T) ^ 2 * ((νk (γ (frame s))).prod (MeasureTheory.volume.prod MeasureTheory.volume)) {p | (∃ s', p ∈ H s' s) ∧ base T ((j (frame s) : ℕ) : ℝ) κ (c (frame s)) (u (frame s)) (Q (frame s)) p.1 p.2.1 ∈ U} ≤ ENNReal.ofReal (β s) * MeasureTheory.volume U) ∧ (∀ (γ₀ : Fin (Wk)) (j₀ : Fin (2 ^ T)), ((Finset.univ.filter (fun s : Fin m => γ (frame s) = γ₀ ∧ j (frame s) = j₀)).card : ℝ) ≤ Nk ^ a / σ) ∧ (∀ (b : Fin J) (ρ : ℝ) (U : Set (EuclideanSpace ℝ (Fin 3))) (g : EuclideanSpace ℝ (Fin 3) → ℝ), 0 < ρ → MeasurableSet U → Measurable g → ENNReal.ofReal ((2 : ℝ) ^ T) ^ 2 * ((νk (γ b)).prod (MeasureTheory.volume.prod MeasureTheory.volume)) {p | (∃ s s', frame s = b ∧ p ∈ H s s') ∧ base T ((j b : ℕ) : ℝ) κ (c b) (u b) (Q b) p.1 p.2.1 ∈ U ∧ |Bk (γ b) * (x p.1 p.2.1) 3 - g (base T ((j b : ℕ) : ℝ) κ (c b) (u b) (Q b) p.1 p.2.1)| ≤ ρ} ≤ ENNReal.ofReal (σ * Nk ^ a * (max ρ (δ (Nk) L) / δ (Nk) L) ^ dc) * MeasureTheory.volume U) ∧ ENNReal.ofReal (lam * κ⁻¹) ≤ ∑ s, ENNReal.ofReal (ωk (γ (frame s)) * (2 : ℝ) ^ T) * ((νk (γ (frame s))).prod (MeasureTheory.volume.prod MeasureTheory.volume)) {p | ∃ s', p ∈ H s s'}

theorem sample_nonempty_iff (cv : Prop) (lam Nk : ℝ) (Wk : ℕ)
    (ωk : Fin Wk → ℝ) (νk : Fin Wk → Measure Trajectory)
    (Ek : Fin Wk → Set Incidence) (Bk : Fin Wk → ℝ)
    (L dc a h : ℝ) (M D : ℕ) (ε : ℝ) :
    Nonempty (TestedSample cv lam Nk Wk ωk νk Ek Bk L dc a h M D ε) ↔
      TestedAt cv lam Nk Wk ωk νk Ek Bk L dc a h M D ε := by
  constructor
  · rintro ⟨s⟩
    exact ⟨s.κ, s.κ_one, s.κ_le, s.σ, s.σ_pos, s.T, s.m, s.J, s.γ, s.j, s.c, s.u, s.Q, s.frame, s.P, s.S, s.H, s.β, s.lst, s.hT, s.hm, s.hJ, s.hframe, s.hP, s.hS, s.hdisj, s.hlst, s.hlstfmt, s.hH, s.hβ, s.hcount, s.hband, s.hcoverage⟩
  · rintro ⟨κ, hκ1, hκε, σ, hσ, T, m, J, γ, j, c, u, Q, frame, P, S, H, β, lst, hT, hm, hJ, hframe, hP, hS, hdisj, hlst, hlstfmt, hH, hβ, hcount, hband, hcoverage⟩
    exact ⟨⟨κ, hκ1, hκε, σ, hσ, T, m, J, γ, j, c, u, Q, frame, P, S, H, β, lst, hT, hm, hJ, hframe, hP, hS, hdisj, hlst, hlstfmt, hH, hβ, hcount, hband, hcoverage⟩⟩

/-- The exact sequence predicate, with each finite sample packaged as a record. -/
noncomputable def TestedSequence (cv : Prop) (lam : ℝ) (N : ℕ → ℝ) (W : ℕ → ℕ)
    (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → Measure Trajectory)
    (E : (k : ℕ) → Fin (W k) → Set Incidence) (B : (k : ℕ) → Fin (W k) → ℝ)
    (L dc a h : ℝ) : Prop :=
  (∀ k, 2 ≤ N k) ∧ Filter.Tendsto N Filter.atTop Filter.atTop ∧ 0 < L ∧ (∀ k γ, 0 ≤ ω k γ) ∧ (∀ k, (∑ γ, ω k γ) = 1) ∧ (∀ k γ, MeasureTheory.IsProbabilityMeasure (ν k γ)) ∧ (∃ Mb : ℕ, ∀ k γ, 0 < B k γ ∧ B k γ ≤ N k ^ Mb ∧ (B k γ)⁻¹ ≤ N k ^ Mb) ∧ (∃ Me De : ℕ, ∀ k γ, MeasurableSet (E k γ) ∧ ∀ i, fmt 7 (N k ^ Me) De {r : Fin 7 → ℝ | ((i, fun z : Fin 6 => r z.castSucc), r 6) ∈ E k γ}) ∧
    ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop,
      Nonempty (TestedSample cv lam (N k) (W k) (ω k) (ν k) (E k) (B k) L dc a h M D ε)

theorem tested_sequence_iff (cv : Prop) (lam : ℝ) (N : ℕ → ℝ) (W : ℕ → ℕ)
    (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → Measure Trajectory)
    (E : (k : ℕ) → Fin (W k) → Set Incidence) (B : (k : ℕ) → Fin (W k) → ℝ)
    (L dc a h : ℝ) :
    SplitStatements.tested cv lam N W ω ν E B L dc a h ↔
      TestedSequence cv lam N W ω ν E B L dc a h := by
  unfold TestedSequence
  simp_rw [sample_nonempty_iff]
  rfl

end Submission.Obl.k4_paired_test_normalization.NormalizationStep
