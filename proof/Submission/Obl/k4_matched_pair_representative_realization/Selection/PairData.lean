/- Adapted within this LOT tree from o190/x0630, commit adb2f45f4ccde121d91c5954051b6c45263cd6de,
Submission/Obl/k4_pair_bin_atlas_assembly/PairData.lean. Existing provenance comments are retained below. -/
import Submission.Obl.k4_matched_pair_representative_realization.Selection.Kernel

namespace Submission.Obl.k4_matched_pair_representative_realization.Selection

open MeasureTheory
open Submission.Obl.k4_quadratic_atlas_normalization

set_option autoImplicit false

/-- One finite sample of the frozen paired-sheet system, without changing its
original worlds, prior laws or time normalization. -/
structure PairData (Nk : ℝ) (Wk : ℕ)
    (ωk : Fin Wk → ℝ) (νk : Fin Wk → Measure (ℕ × (Fin 6 → ℝ)))
    (Ek : Fin Wk → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (Bk : Fin Wk → ℝ)
    (L a h : ℝ) (M D : ℕ) (ε : ℝ) where
  κ : ℝ
  κ_one : 1 ≤ κ
  κ_upper : κ ≤ Nk ^ ε
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
  S : Fin m → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)
  H : Fin m → Set ((ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ))
  β : Fin m → ℝ
  lst : Fin Wk → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin m)
  horizon : (2 : ℝ) ^ T ≤ Nk ^ (h + ε)
  source_count : (m : ℝ) ≤ Nk ^ M
  frame_count : (J : ℝ) ≤ Nk ^ M
  frames : (∀ b, Matrix.det (Q b) ≠ 0 ∧ ‖c b‖ + ‖u b‖ ≤ Nk ^ M ∧ (∑ i : Fin 2, ∑ i' : Fin 2, (|Q b i i'| + |(Q b)⁻¹ i i'|)) ≤ Nk ^ M ∧ (∑ i : Fin 2, ∑ i' : Fin 2, |Q b i i'|) ≤ κ / (2 : ℝ) ^ T)
  tests : (∀ s, (P s).totalDegree ≤ 2 ∧ (∀ d, |(P s).coeff d| ≤ Nk ^ M) ∧ |MvPolynomial.eval (0 : Fin 4 → ℝ) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (P s)))| ≤ (δ (Nk) L)⁻¹ ∧ (disc (P s)).totalDegree ≤ 2 ∧ (∀ d, |(disc (P s)).coeff d| ≤ Nk ^ a))
  sources : (∀ s, MeasurableSet (S s) ∧ (∀ i, fmt 7 (Nk ^ M) D {r : Fin 7 → ℝ | ((i, fun z : Fin 6 => r z.castSucc), r 6) ∈ S s}) ∧ ∀ p ∈ S s, p ∈ Ek (γ (frame s)) ∧ (p.1.1 : ℝ) ≤ Nk ^ M ∧ (∀ d, |p.1.2 d| ≤ Nk ^ M) ∧ p.2 ∈ Set.Icc (((j (frame s) : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j (frame s) : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T) ∧ ∀ t ∈ Set.Icc (((j (frame s) : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j (frame s) : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T), ‖Matrix.toEuclideanLin (Q (frame s))⁻¹ (y p.1 t - c (frame s) - t • u (frame s))‖ ≤ κ ∧ |Bk (γ (frame s)) * (x p.1 t) 3| ≤ Nk ^ M ∧ ‖base T ((j (frame s) : ℕ) : ℝ) κ (c (frame s)) (u (frame s)) (Q (frame s)) p.1 t‖ ≤ (1 : ℝ) / 8 ∧ ∀ t' ∈ Set.Icc (((j (frame s) : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j (frame s) : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T), ‖base T ((j (frame s) : ℕ) : ℝ) κ (c (frame s)) (u (frame s)) (Q (frame s)) p.1 t - base T ((j (frame s) : ℕ) : ℝ) κ (c (frame s)) (u (frame s)) (Q (frame s)) p.1 t'‖ ≤ (2 : ℝ) ^ T * |t - t'|)
  source_disjoint : (∀ s s', s ≠ s' → γ (frame s) = γ (frame s') → j (frame s) = j (frame s') → Disjoint (S s) (S s'))
  list_size : (∀ γ₀ o, ((lst γ₀ o).card : ℝ) ≤ κ)
  list_format : (∀ γ₀ s, MeasurableSet {p | s ∈ lst γ₀ (obs (Bk γ₀) (δ (Nk) L) p)} ∧ ∀ i, fmt 7 (Nk ^ M) D {r : Fin 7 → ℝ | s ∈ lst γ₀ (obs (Bk γ₀) (δ (Nk) L) ((i, fun z : Fin 6 => r z.castSucc), r 6))})
  pairs : (∀ s, MeasurableSet (H s) ∧ ∀ p ∈ H s, (p.1, p.2.1) ∈ S s ∧ p.2.2 ∈ Set.Icc (((j (frame s) : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j (frame s) : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T) ∧ (p.1, p.2.2) ∈ Ek (γ (frame s)) ∧ ∃ s' ∈ lst (γ (frame s)) (obs (Bk (γ (frame s))) (δ (Nk) L) (p.1, p.2.2)), frame s' = frame s ∧ localPair (Nk) a (δ (Nk) L) ((2 : ℝ) ^ T) (P s) (P s') (base T ((j (frame s) : ℕ) : ℝ) κ (c (frame s)) (u (frame s)) (Q (frame s)) p.1 p.2.1) (base T ((j (frame s) : ℕ) : ℝ) κ (c (frame s)) (u (frame s)) (Q (frame s)) p.1) (fun t => Bk (γ (frame s)) * (x p.1 t) 3) p.2.1 (Set.Icc (((j (frame s) : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j (frame s) : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T)))
  base_density : (∀ s, 0 ≤ β s ∧ ∀ U : Set (EuclideanSpace ℝ (Fin 3)), MeasurableSet U → ENNReal.ofReal ((2 : ℝ) ^ T) ^ 2 * ((νk (γ (frame s))).prod (MeasureTheory.volume.prod MeasureTheory.volume)) (H s ∩ {p | base T ((j (frame s) : ℕ) : ℝ) κ (c (frame s)) (u (frame s)) (Q (frame s)) p.1 p.2.1 ∈ U}) ≤ ENNReal.ofReal (β s) * MeasureTheory.volume U)
  density_budget : (∑ s, ωk (γ (frame s)) * β s / (2 : ℝ) ^ T) ≤ Nk ^ a
  mass_floor : ENNReal.ofReal κ⁻¹ ≤ ∑ s, ENNReal.ofReal (ωk (γ (frame s)) * (2 : ℝ) ^ T) * ((νk (γ (frame s))).prod (MeasureTheory.volume.prod MeasureTheory.volume)) (H s)

theorem paired_has_samples
    {N : ℕ → ℝ} {W : ℕ → ℕ}
    {ω : (k : ℕ) → Fin (W k) → ℝ}
    {ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 6 → ℝ))}
    {E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {B : (k : ℕ) → Fin (W k) → ℝ} {L a h : ℝ}
    (hp : paired N W ω ν E B L a h) :
    ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop,
      Nonempty (PairData (N k) (W k) (ω k) (ν k) (E k) (B k) L a h M D ε) := by
  obtain ⟨_, _, _, _, _, _, _, _, M, D, hsamples⟩ := hp
  refine ⟨M, D, fun ε hε => (hsamples ε hε).mono ?_⟩
  rintro k ⟨κ, hκone, hκupper, T, m, J, γ, j, c, u, Q, frame, P, S, H, β, lst,
    hhorizon, hsource_count, hframe_count, hframes, htests, hsources, hsource_disjoint,
    hlist_size, hlist_format, hpairs, hbase_density, hdensity_budget, hmass_floor⟩
  exact ⟨⟨κ, hκone, hκupper, T, m, J, γ, j, c, u, Q, frame, P, S, H, β, lst,
    hhorizon, hsource_count, hframe_count, hframes, htests, hsources, hsource_disjoint,
    hlist_size, hlist_format, hpairs, hbase_density, hdensity_budget, hmass_floor⟩⟩


end Submission.Obl.k4_matched_pair_representative_realization.Selection
