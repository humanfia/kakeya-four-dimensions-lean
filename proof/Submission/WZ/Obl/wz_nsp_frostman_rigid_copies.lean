-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_frostman_rigid_copies.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy
import Submission.WZ.Obl.wz_nsp_separated_full_subtree

set_option linter.unusedVariables false

namespace WangZahlLot.Obl.wz_nsp_frostman_rigid_copies

def FullHierarchy (T : ℝ → LeanEval.Analysis.WangZahlKakeya.Space → LeanEval.Analysis.WangZahlKakeya.Space → Set LeanEval.Analysis.WangZahlKakeya.Space) :=
  (fun (δ a b : ℝ) (B m : ℕ) (x v : Fin m → LeanEval.Analysis.WangZahlKakeya.Space) =>
 (∀ s : Fin m, ‖v s‖ = 1 ∧ T δ (x s) (v s) ⊆ Metric.ball 0 1) ∧
 (∀ W : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → ENNReal.ofReal ((Set.ncard {s : Fin m | T δ (x s) (v s) ⊆ W} : ℝ) * δ ^ 2) ≤ ENNReal.ofReal (δ ^ (-b)) * MeasureTheory.volume W) ∧
 ∃ J : ℕ, 0 < J ∧ J ≤ B ∧
 ∃ (r : Fin J → ℝ) (k : Fin J → ℕ) (z w : (j : Fin J) → Fin (k j) → LeanEval.Analysis.WangZahlKakeya.Space) (f : (j : Fin J) → Fin m → Fin (k j)),
 (∀ j : Fin J, δ ≤ r j ∧ r j ≤ 1 ∧ 0 < k j) ∧
 (∀ ρ₀ : ℝ, δ ≤ ρ₀ → ρ₀ ≤ 1 → ∃ j : Fin J, ρ₀ ≤ r j ∧ r j ≤ δ ^ (-a) * ρ₀) ∧
 (∀ (j : Fin J) (i : Fin (k j)), ‖w j i‖ = 1) ∧
 (∀ j : Fin J, Function.Surjective (f j)) ∧
 (∀ (j : Fin J) (s : Fin m), T δ (x s) (v s) ⊆ T (r j) (z j (f j s)) (w j (f j s))) ∧
 (∀ (j : Fin J) (i : Fin (k j)), δ ^ b * (r j) ^ 2 ≤ (Set.ncard {s : Fin m | f j s = i} : ℝ) * δ ^ 2) ∧
 (∀ j j' : Fin J, j ≤ j' → r j' ≤ r j ∧ ∃ p : Fin (k j') → Fin (k j),
 (∀ i' : Fin (k j'), T (r j') (z j' i') (w j' i') ⊆ T (r j) (z j (p i')) (w j (p i'))) ∧
 (∀ s : Fin m, f j s = p (f j' s))))

def FrostmanAllScales (T : ℝ → LeanEval.Analysis.WangZahlKakeya.Space → LeanEval.Analysis.WangZahlKakeya.Space → Set LeanEval.Analysis.WangZahlKakeya.Space) :=
  (fun (δ K : ℝ) (m : ℕ) (x' v' : Fin m → LeanEval.Analysis.WangZahlKakeya.Space) => ∀ ρ₀ : ℝ, δ ≤ ρ₀ → ρ₀ ≤ 1 → ∃ ρ : ℝ, ρ₀ ≤ ρ ∧ ρ ≤ 1 ∧ ρ ≤ K * ρ₀ ∧ ∃ k : ℕ, 0 < k ∧ ∃ (z w : Fin k → LeanEval.Analysis.WangZahlKakeya.Space), (∀ j : Fin k, ‖w j‖ = 1) ∧ (∀ j j' : Fin k, j ≠ j' → MeasureTheory.volume (T ρ (z j) (w j) ∩ T ρ (z j') (w j')) ≤ (1 / 2 : ENNReal) * MeasureTheory.volume (T ρ (z j) (w j))) ∧ (∀ i : Fin m, ∃! j : Fin k, T δ (x' i) (v' i) ⊆ T ρ (z j) (w j)) ∧ (∀ j : Fin k, ∃ i : Fin m, T δ (x' i) (v' i) ⊆ T ρ (z j) (w j)) ∧ (∀ j j' : Fin k, (((Set.ncard {i : Fin m | T δ (x' i) (v' i) ⊆ T ρ (z j) (w j)} : ℕ) : ℝ)) ≤ K * (((Set.ncard {i : Fin m | T δ (x' i) (v' i) ⊆ T ρ (z j') (w j')} : ℕ) : ℝ))) ∧ (∀ j : Fin k, ∀ W : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → ENNReal.ofReal ((((Set.ncard {i : Fin m | T δ (x' i) (v' i) ⊆ T ρ (z j) (w j) ∧ T δ (x' i) (v' i) ⊆ W} : ℕ) : ℝ)) * ρ ^ 2) ≤ ENNReal.ofReal (K * (((Set.ncard {i : Fin m | T δ (x' i) (v' i) ⊆ T ρ (z j) (w j)} : ℕ) : ℝ))) * MeasureTheory.volume W))

end WangZahlLot.Obl.wz_nsp_frostman_rigid_copies

theorem WangZahlLot.wz_nsp_frostman_rigid_copies : ∀ T, T = (fun (d : ℝ) (p q : LeanEval.Analysis.WangZahlKakeya.Space) => Metric.thickening d (segment ℝ p (p + q))) → (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (r ρ M L : ℝ) (K n : ℕ) (y w : Fin K → LeanEval.Analysis.WangZahlKakeya.Space) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (g : Fin n → Fin K), 0 < r → r ≤ ρ → ρ ≤ 1 → 1 ≤ M → (∀ k : Fin K, ‖w k‖ = 1 ∧ ((Set.ncard {i : Fin n | g i = k} : ℕ) : ℝ) ≤ M) → (∀ i : Fin n, ‖v i‖ = 1 ∧ T r (x i) (v i) ⊆ Metric.ball 0 1 ∧ T r (x i) (v i) ⊆ T ρ (y (g i)) (w (g i))) → (∀ (k : Fin K) (W : Set LeanEval.Analysis.WangZahlKakeya.Space), Convex ℝ W → ENNReal.ofReal (((Set.ncard {i : Fin n | g i = k ∧ T r (x i) (v i) ⊆ W} : ℕ) : ℝ) * r ^ 2) ≤ ENNReal.ofReal L * MeasureTheory.volume W) → ∃ (N : ℕ) (A : Fin N → (LeanEval.Analysis.WangZahlKakeya.Space ≃ᵃⁱ[ℝ] LeanEval.Analysis.WangZahlKakeya.Space)), ρ ^ 2 ≤ (N : ℝ) * M * r ^ 2 ∧ (N : ℝ) * M * r ^ 2 ≤ ρ ^ 2 + M * r ^ 2 ∧ (∀ (j : Fin N) (p : LeanEval.Analysis.WangZahlKakeya.Space), ‖p‖ < 1 → ‖A j p - p‖ ≤ ρ) ∧ ∀ (k : Fin K) (W : Set LeanEval.Analysis.WangZahlKakeya.Space), Convex ℝ W → ENNReal.ofReal (((Set.ncard {q : Fin N × Fin n | g q.2 = k ∧ T r (A q.1 (x q.2)) ((A q.1).linear (v q.2)) ⊆ W} : ℕ) : ℝ) * r ^ 2) ≤ ENNReal.ofReal (C * r ^ (-ε) * Real.log (2 + (K : ℝ)) * L) * MeasureTheory.volume W) → ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space), 0 < n → (∀ i : Fin n, ‖v i‖ = 1 ∧ T δ (x i) (v i) ⊆ Metric.ball 0 1) → (∀ i j : Fin n, i ≠ j → MeasureTheory.volume (T δ (x i) (v i) ∩ T δ (x j) (v j)) ≤ (1 / 2 : ENNReal) * MeasureTheory.volume (T δ (x i) (v i))) → (∀ ρ₀ : ℝ, δ ≤ ρ₀ → ρ₀ ≤ 1 → ∃ ρ : ℝ, ρ₀ ≤ ρ ∧ ρ < δ ^ (-η) * ρ₀ ∧ ∃ (N : ℕ) (y w : Fin N → LeanEval.Analysis.WangZahlKakeya.Space) (f : Fin n → Fin N), (∀ k : Fin N, ‖w k‖ = 1) ∧ (∀ i : Fin n, T δ (x i) (v i) ⊆ T ρ (y (f i)) (w (f i))) ∧ (∀ k k' : Fin N, ((Set.ncard {i : Fin n | f i = k} : ℕ) : ℝ) ≤ δ ^ (-η) * ((Set.ncard {i : Fin n | f i = k'} : ℕ) : ℝ)) ∧ (∀ W : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → ENNReal.ofReal (((Set.ncard {k : Fin N | T ρ (y k) (w k) ⊆ W} : ℕ) : ℝ) * ρ ^ 2) ≤ ENNReal.ofReal (δ ^ (-η)) * MeasureTheory.volume W)) → ∀ G : Finset (Fin n), δ ^ η * (n : ℝ) ≤ (G.card : ℝ) → ∃ (N m : ℕ) (A : Fin N → (LeanEval.Analysis.WangZahlKakeya.Space ≃ᵃⁱ[ℝ] LeanEval.Analysis.WangZahlKakeya.Space)) (c : Fin m → Fin n) (g : Fin m → Fin N) (x' v' : Fin m → LeanEval.Analysis.WangZahlKakeya.Space), 0 < m ∧ (N : ℝ) * (G.card : ℝ) * δ ^ 2 ≤ C * δ ^ (-ε) ∧ (∀ s : Fin m, c s ∈ G ∧ x' s = A (g s) (x (c s)) ∧ v' s = (A (g s)).linear (v (c s)) ∧ T δ (x' s) (v' s) ⊆ Metric.ball 0 1) ∧ (∀ s t : Fin m, s ≠ t → MeasureTheory.volume (T δ (x' s) (v' s) ∩ T δ (x' t) (v' t)) ≤ (1 / 2 : ENNReal) * MeasureTheory.volume (T δ (x' s) (v' s))) ∧ (∀ ρ₀ : ℝ, δ ≤ ρ₀ → ρ₀ ≤ 1 → ∃ ρ : ℝ, ρ₀ ≤ ρ ∧ ρ ≤ 1 ∧ ρ ≤ δ ^ (-ε) * ρ₀ ∧ ∃ k : ℕ, 0 < k ∧ ∃ (z w : Fin k → LeanEval.Analysis.WangZahlKakeya.Space), (∀ j : Fin k, ‖w j‖ = 1) ∧ (∀ j j' : Fin k, j ≠ j' → MeasureTheory.volume (T ρ (z j) (w j) ∩ T ρ (z j') (w j')) ≤ (1 / 2 : ENNReal) * MeasureTheory.volume (T ρ (z j) (w j))) ∧ (∀ i : Fin m, ∃! j : Fin k, T δ (x' i) (v' i) ⊆ T ρ (z j) (w j)) ∧ (∀ j : Fin k, ∃ i : Fin m, T δ (x' i) (v' i) ⊆ T ρ (z j) (w j)) ∧ (∀ j j' : Fin k, (((Set.ncard {i : Fin m | T δ (x' i) (v' i) ⊆ T ρ (z j) (w j)} : ℕ) : ℝ)) ≤ δ ^ (-ε) * (((Set.ncard {i : Fin m | T δ (x' i) (v' i) ⊆ T ρ (z j') (w j')} : ℕ) : ℝ))) ∧ (∀ j : Fin k, ∀ W : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → ENNReal.ofReal ((((Set.ncard {i : Fin m | T δ (x' i) (v' i) ⊆ T ρ (z j) (w j) ∧ T δ (x' i) (v' i) ⊆ W} : ℕ) : ℝ)) * ρ ^ 2) ≤ ENNReal.ofReal (δ ^ (-ε) * (((Set.ncard {i : Fin m | T δ (x' i) (v' i) ⊆ T ρ (z j) (w j)} : ℕ) : ℝ))) * MeasureTheory.volume W)) := by
  intro T hT hsingle ε hε
  let Q := WangZahlLot.Obl.wz_nsp_frostman_rigid_copies.FullHierarchy T
  let F := WangZahlLot.Obl.wz_nsp_frostman_rigid_copies.FrostmanAllScales T
  obtain ⟨B, hB, hbuild⟩ :=
    WangZahlLot.wz_nsp_full_counted_hierarchy T hT Q rfl hsingle ε hε
  obtain ⟨b, hb, d₂, hd₂, hselect⟩ :=
    WangZahlLot.wz_nsp_separated_full_subtree T hT Q rfl F rfl ε hε B hB
  obtain ⟨η, hη, d₁, hd₁, C, hC, hcopies⟩ := hbuild b hb
  refine ⟨η, hη, min d₁ d₂, lt_min hd₁ hd₂, C, hC, ?_⟩
  intro δ hδ hδ₀ n x v hn hadm hdistinct hscales G hG
  obtain ⟨N, m, A, c, g, x', v', hm, hN, hcopy, hQ⟩ :=
    hcopies δ hδ (hδ₀.trans (min_le_left _ _)) n x v hn hadm hdistinct hscales G hG
  obtain ⟨m', e, hm', _he, hdistinct', hF⟩ :=
    hselect δ hδ (hδ₀.trans (min_le_right _ _)) m x' v' hm hQ
  refine ⟨N, m', A, (fun s => c (e s)), (fun s => g (e s)),
    (fun s => x' (e s)), (fun s => v' (e s)), hm', hN, ?_, hdistinct', hF⟩
  intro s
  exact ⟨(hcopy (e s)).1, (hcopy (e s)).2.1, (hcopy (e s)).2.2,
    (hQ.1 (e s)).2⟩
