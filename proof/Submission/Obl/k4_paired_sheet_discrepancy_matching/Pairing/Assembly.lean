/- Adapted from this LOT tree, o114/x0680 commit133cc8c, Submission/Obl/k4_terminal_representative_atlas/Pairing/Assembly.lean.
Existing attribution to o156/x0531,x0524,x0575 and accepted imports is retained below. -/

/- Adapted from this LOT tree, o156, session x0524 branch c7cfd90,
Submission/Obl/k4_terminal_local_sheet_pairing/Assembly.lean. Original authorship/provenance is preserved below.
Namespace and imports adjusted for o114. -/

import Mathlib
import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.TopReduction

/-! Assembly of one paired sample from frames and entries indexed by arbitrary finite types.

The pair masks are `H s := Cand s \ toMeasurable (Cand s ∩ {¬ good})`: they are measurable,
consist of good pairs only, and lose at most the outer measure of the bad candidates. -/

namespace Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

open MeasureTheory Set

/-- The block interval of a frame. -/
abbrev blockIcc (T : ℕ) (jj : ℕ) : Set ℝ :=
  Set.Icc ((jj : ℝ) / (2 : ℝ) ^ T) (((jj : ℝ) + 1) / (2 : ℝ) ^ T)

section Assembly

variable {N : ℕ → ℝ} {W : ℕ → ℕ} {ω : (k : ℕ) → Fin (W k) → ℝ}
  {ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 6 → ℝ))}
  {E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : (k : ℕ) → Fin (W k) → ℝ}
  {L a h : ℝ} {M D : ℕ} {ε : ℝ} {k : ℕ}

/-- **Assembly of a paired sample.** -/
theorem pairedSample_of_entries
    (κ : ℝ) (hκ1 : 1 ≤ κ) (hκε : κ ≤ N k ^ ε) (T : ℕ) (hT : (2 : ℝ) ^ T ≤ N k ^ (h + ε))
    {Fr En : Type*} [Fintype Fr] [Fintype En] [DecidableEq En]
    (hFr : (Fintype.card Fr : ℝ) ≤ N k ^ M) (hEn : (Fintype.card En : ℝ) ≤ N k ^ M)
    (γ : Fr → Fin (W k)) (j : Fr → Fin (2 ^ T)) (c u : Fr → EuclideanSpace ℝ (Fin 2))
    (Q : Fr → Matrix (Fin 2) (Fin 2) ℝ)
    (hframe : ∀ b, Matrix.det (Q b) ≠ 0 ∧ ‖c b‖ + ‖u b‖ ≤ N k ^ M ∧
      (∑ i : Fin 2, ∑ i' : Fin 2, (|Q b i i'| + |(Q b)⁻¹ i i'|)) ≤ N k ^ M ∧
      (∑ i : Fin 2, ∑ i' : Fin 2, |Q b i i'|) ≤ κ / (2 : ℝ) ^ T)
    (frame : En → Fr) (P : En → MvPolynomial (Fin 4) ℝ)
    (hP : ∀ s, (P s).totalDegree ≤ 2 ∧ (∀ d, |(P s).coeff d| ≤ N k ^ M) ∧
      |MvPolynomial.eval (0 : Fin 4 → ℝ) (MvPolynomial.pderiv (3 : Fin 4)
        (MvPolynomial.pderiv (3 : Fin 4) (P s)))| ≤ (δ (N k) L)⁻¹ ∧
      (disc (P s)).totalDegree ≤ 2 ∧ (∀ d, |(disc (P s)).coeff d| ≤ N k ^ a))
    (S : En → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hS : ∀ s, MeasurableSet (S s) ∧ (∀ i, fmt 7 (N k ^ M) D
        {r : Fin 7 → ℝ | ((i, fun z : Fin 6 => r z.castSucc), r 6) ∈ S s}) ∧
      ∀ p ∈ S s, p ∈ E k (γ (frame s)) ∧ (p.1.1 : ℝ) ≤ N k ^ M ∧ (∀ d, |p.1.2 d| ≤ N k ^ M) ∧
        p.2 ∈ blockIcc T (j (frame s)) ∧ ∀ t ∈ blockIcc T (j (frame s)),
          ‖Matrix.toEuclideanLin (Q (frame s))⁻¹ (y p.1 t - c (frame s) - t • u (frame s))‖ ≤ κ ∧
          |B k (γ (frame s)) * (x p.1 t) 3| ≤ N k ^ M ∧
          ‖base T ((j (frame s) : ℕ) : ℝ) κ (c (frame s)) (u (frame s)) (Q (frame s)) p.1 t‖ ≤
            (1 : ℝ) / 8 ∧ ∀ t' ∈ blockIcc T (j (frame s)),
            ‖base T ((j (frame s) : ℕ) : ℝ) κ (c (frame s)) (u (frame s)) (Q (frame s)) p.1 t -
              base T ((j (frame s) : ℕ) : ℝ) κ (c (frame s)) (u (frame s)) (Q (frame s)) p.1 t'‖ ≤
              (2 : ℝ) ^ T * |t - t'|)
    (hdisj : ∀ s s', s ≠ s' → γ (frame s) = γ (frame s') → j (frame s) = j (frame s') →
      Disjoint (S s) (S s'))
    (lst : Fin (W k) → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset En)
    (hlst : ∀ γ₀ o, ((lst γ₀ o).card : ℝ) ≤ κ)
    (hlstfmt : ∀ γ₀ s, MeasurableSet {p | s ∈ lst γ₀ (obs (B k γ₀) (δ (N k) L) p)} ∧
      ∀ i, fmt 7 (N k ^ M) D {r : Fin 7 → ℝ |
        s ∈ lst γ₀ (obs (B k γ₀) (δ (N k) L) ((i, fun z : Fin 6 => r z.castSucc), r 6))})
    (Cand : En → Set ((ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ)))
    (hCand : ∀ s, MeasurableSet (Cand s) ∧ ∀ p ∈ Cand s, (p.1, p.2.1) ∈ S s ∧
      p.2.2 ∈ blockIcc T (j (frame s)) ∧ (p.1, p.2.2) ∈ E k (γ (frame s)))
    (β : En → ℝ)
    (hβ : ∀ s, 0 ≤ β s ∧ ∀ U : Set (EuclideanSpace ℝ (Fin 3)), MeasurableSet U →
      ENNReal.ofReal ((2 : ℝ) ^ T) ^ 2 * ((ν k (γ (frame s))).prod (volume.prod volume))
        (Cand s ∩ {p | base T ((j (frame s) : ℕ) : ℝ) κ (c (frame s)) (u (frame s))
          (Q (frame s)) p.1 p.2.1 ∈ U}) ≤ ENNReal.ofReal (β s) * volume U)
    (hbudget : (∑ s, ω k (γ (frame s)) * β s / (2 : ℝ) ^ T) ≤ N k ^ a)
    (Xbad : ENNReal) (hXbad : Xbad ≠ ⊤)
    (hbad : ∑ s, ENNReal.ofReal (ω k (γ (frame s)) * (2 : ℝ) ^ T) *
      ((ν k (γ (frame s))).prod (volume.prod volume)) (Cand s ∩ {p | ¬ ∃ s' ∈ lst (γ (frame s))
        (obs (B k (γ (frame s))) (δ (N k) L) (p.1, p.2.2)), frame s' = frame s ∧
        localPair (N k) a (δ (N k) L) ((2 : ℝ) ^ T) (P s) (P s')
          (base T ((j (frame s) : ℕ) : ℝ) κ (c (frame s)) (u (frame s)) (Q (frame s)) p.1 p.2.1)
          (base T ((j (frame s) : ℕ) : ℝ) κ (c (frame s)) (u (frame s)) (Q (frame s)) p.1)
          (fun t => B k (γ (frame s)) * (x p.1 t) 3) p.2.1 (blockIcc T (j (frame s)))}) ≤ Xbad)
    (hcand : ENNReal.ofReal κ⁻¹ + Xbad ≤ ∑ s, ENNReal.ofReal (ω k (γ (frame s)) * (2 : ℝ) ^ T) *
      ((ν k (γ (frame s))).prod (volume.prod volume)) (Cand s)) :
    PairedSample N W ω ν E B L a h M D ε k := by
  classical
  -- the good predicate and the pair masks
  let μs : En → Measure ((ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ)) :=
    fun s => (ν k (γ (frame s))).prod (volume.prod volume)
  let Good : En → ((ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ)) → Prop := fun s p =>
    ∃ s' ∈ lst (γ (frame s)) (obs (B k (γ (frame s))) (δ (N k) L) (p.1, p.2.2)),
      frame s' = frame s ∧
      localPair (N k) a (δ (N k) L) ((2 : ℝ) ^ T) (P s) (P s')
        (base T ((j (frame s) : ℕ) : ℝ) κ (c (frame s)) (u (frame s)) (Q (frame s)) p.1 p.2.1)
        (base T ((j (frame s) : ℕ) : ℝ) κ (c (frame s)) (u (frame s)) (Q (frame s)) p.1)
        (fun t => B k (γ (frame s)) * (x p.1 t) 3) p.2.1 (blockIcc T (j (frame s)))
  let Bad : En → Set ((ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ)) := fun s => Cand s ∩ {p | ¬ Good s p}
  let H : En → Set ((ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ)) := fun s =>
    Cand s \ toMeasurable (μs s) (Bad s)
  have hHmeas : ∀ s, MeasurableSet (H s) :=
    fun s => (hCand s).1.diff (measurableSet_toMeasurable _ _)
  have hHgood : ∀ s, ∀ p ∈ H s, Good s p := by
    intro s p ⟨hpC, hpT⟩
    by_contra hng
    exact hpT (subset_toMeasurable (μs s) (Bad s) ⟨hpC, hng⟩)
  have hHsub : ∀ s, H s ⊆ Cand s := fun s => diff_subset
  have hCandle : ∀ s, μs s (Cand s) ≤ μs s (H s) + μs s (Bad s) := by
    intro s
    calc μs s (Cand s) ≤ μs s (H s ∪ toMeasurable (μs s) (Bad s)) := by
          apply measure_mono
          intro p hp
          by_cases hpT : p ∈ toMeasurable (μs s) (Bad s)
          · exact Or.inr hpT
          · exact Or.inl ⟨hp, hpT⟩
      _ ≤ μs s (H s) + μs s (toMeasurable (μs s) (Bad s)) := measure_union_le _ _
      _ = μs s (H s) + μs s (Bad s) := by rw [measure_toMeasurable]
  have hcover : ENNReal.ofReal κ⁻¹ ≤ ∑ s, ENNReal.ofReal (ω k (γ (frame s)) * (2 : ℝ) ^ T) *
      μs s (H s) := by
    have h1 : ENNReal.ofReal κ⁻¹ + Xbad ≤
        (∑ s, ENNReal.ofReal (ω k (γ (frame s)) * (2 : ℝ) ^ T) * μs s (H s)) + Xbad := by
      calc ENNReal.ofReal κ⁻¹ + Xbad ≤ ∑ s, ENNReal.ofReal (ω k (γ (frame s)) * (2 : ℝ) ^ T) *
            μs s (Cand s) := hcand
        _ ≤ ∑ s, (ENNReal.ofReal (ω k (γ (frame s)) * (2 : ℝ) ^ T) * μs s (H s) +
            ENNReal.ofReal (ω k (γ (frame s)) * (2 : ℝ) ^ T) * μs s (Bad s)) := by
            apply Finset.sum_le_sum
            intro s _
            rw [← mul_add]
            exact mul_le_mul_right (hCandle s) _
        _ = (∑ s, ENNReal.ofReal (ω k (γ (frame s)) * (2 : ℝ) ^ T) * μs s (H s)) +
            ∑ s, ENNReal.ofReal (ω k (γ (frame s)) * (2 : ℝ) ^ T) * μs s (Bad s) :=
            Finset.sum_add_distrib
        _ ≤ _ := add_le_add le_rfl hbad
    exact (ENNReal.add_le_add_iff_right hXbad).mp h1
  -- reindex
  let eF : Fr ≃ Fin (Fintype.card Fr) := Fintype.equivFin Fr
  let eE : En ≃ Fin (Fintype.card En) := Fintype.equivFin En
  refine ⟨κ, hκ1, hκε, T, Fintype.card En, Fintype.card Fr,
    fun b => γ (eF.symm b), fun b => j (eF.symm b), fun b => c (eF.symm b),
    fun b => u (eF.symm b), fun b => Q (eF.symm b),
    fun s => eF (frame (eE.symm s)), fun s => P (eE.symm s), fun s => S (eE.symm s),
    fun s => H (eE.symm s), fun s => β (eE.symm s),
    fun γ₀ o => (lst γ₀ o).map eE.toEmbedding, hT, hEn, hFr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro b; exact hframe _
  · intro s; exact hP _
  · intro s
    simpa only [Equiv.symm_apply_apply] using hS (eE.symm s)
  · intro s s' hss' hγ hj
    simp only [Equiv.symm_apply_apply] at hγ hj
    exact hdisj _ _ (fun h => hss' (eE.symm.injective h)) hγ hj
  · intro γ₀ o
    simpa only [Finset.card_map] using hlst γ₀ o
  · intro γ₀ s
    have hmem : ∀ o, s ∈ (lst γ₀ o).map eE.toEmbedding ↔ eE.symm s ∈ lst γ₀ o := by
      intro o
      simp only [Finset.mem_map_equiv]
    simp only [hmem]
    exact hlstfmt γ₀ (eE.symm s)
  · intro s
    refine ⟨hHmeas _, ?_⟩
    intro p hp
    obtain ⟨hpS, hpI, hpE⟩ := (hCand (eE.symm s)).2 p (hHsub _ hp)
    simp only [Equiv.symm_apply_apply]
    refine ⟨hpS, hpI, hpE, ?_⟩
    obtain ⟨s', hs', hfr, hloc⟩ := hHgood (eE.symm s) p hp
    refine ⟨eE s', ?_, ?_, ?_⟩
    · simp only [Finset.mem_map_equiv, Equiv.coe_toEmbedding]
      simpa using hs'
    · simp only [Equiv.symm_apply_apply, hfr]
    · simpa only [Equiv.symm_apply_apply] using hloc
  · intro s
    refine ⟨(hβ (eE.symm s)).1, fun U hU => ?_⟩
    simp only [Equiv.symm_apply_apply]
    refine le_trans ?_ ((hβ (eE.symm s)).2 U hU)
    gcongr
    exact hHsub _
  · simp only [Equiv.symm_apply_apply]
    refine le_trans (le_of_eq ?_) hbudget
    exact Equiv.sum_comp eE.symm (fun s => ω k (γ (frame s)) * β s / (2 : ℝ) ^ T)
  · simp only [Equiv.symm_apply_apply]
    refine le_trans hcover (le_of_eq ?_)
    exact (Equiv.sum_comp eE.symm (fun s => ENNReal.ofReal (ω k (γ (frame s)) * (2 : ℝ) ^ T) *
      μs s (H s))).symm

end Assembly

end Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing
