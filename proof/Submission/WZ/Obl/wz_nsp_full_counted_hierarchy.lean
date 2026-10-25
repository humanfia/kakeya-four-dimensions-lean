-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_full_counted_hierarchy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.SourceCopy
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.SourcePreparation
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_nsp_full_counted_hierarchy`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_nsp_full_counted_hierarchy`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_nsp_full_counted_hierarchy/`
belong to this obligation.
-/

open WangZahlLot.Obl.wz_nsp_full_counted_hierarchy

theorem WangZahlLot.wz_nsp_full_counted_hierarchy : ∀ T, T = (fun (d:ℝ) (p q:LeanEval.Analysis.WangZahlKakeya.Space) => Metric.thickening d (segment ℝ p (p + q))) → ∀ Q, Q = (fun (δ a b:ℝ) (B m:ℕ) (x v:Fin m → LeanEval.Analysis.WangZahlKakeya.Space) => (∀ s:Fin m, ‖v s‖ = 1 ∧ T δ (x s) (v s) ⊆ Metric.ball 0 1) ∧ (∀ W:Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → ENNReal.ofReal ((Set.ncard {s:Fin m | T δ (x s) (v s) ⊆ W}:ℝ) * δ ^ 2) ≤ ENNReal.ofReal (δ ^ (-b)) * MeasureTheory.volume W) ∧ ∃ J:ℕ, 0 < J ∧ J ≤ B ∧ ∃ (r:Fin J → ℝ) (k:Fin J → ℕ) (z w:(j:Fin J) → Fin (k j) → LeanEval.Analysis.WangZahlKakeya.Space) (f:(j:Fin J) → Fin m → Fin (k j)), (∀ j:Fin J, δ ≤ r j ∧ r j ≤ 1 ∧ 0 < k j) ∧ (∀ ρ₀:ℝ, δ ≤ ρ₀ → ρ₀ ≤ 1 → ∃ j:Fin J, ρ₀ ≤ r j ∧ r j ≤ δ ^ (-a) * ρ₀) ∧ (∀ (j:Fin J) (i:Fin (k j)), ‖w j i‖ = 1) ∧ (∀ j:Fin J, Function.Surjective (f j)) ∧ (∀ (j:Fin J) (s:Fin m), T δ (x s) (v s) ⊆ T (r j) (z j (f j s)) (w j (f j s))) ∧ (∀ (j:Fin J) (i:Fin (k j)), δ ^ b * (r j) ^ 2 ≤ (Set.ncard {s:Fin m | f j s = i}:ℝ) * δ ^ 2) ∧ (∀ j j':Fin J, j ≤ j' → r j' ≤ r j ∧ ∃ p:Fin (k j') → Fin (k j), (∀ i':Fin (k j'), T (r j') (z j' i') (w j' i') ⊆ T (r j) (z j (p i')) (w j (p i'))) ∧ (∀ s:Fin m, f j s = p (f j' s)))) → (∀ ε:ℝ, 0 < ε → ∃ C:ℝ, 0 < C ∧ ∀ (r ρ M L:ℝ) (K n:ℕ) (y w:Fin K → LeanEval.Analysis.WangZahlKakeya.Space) (x v:Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (g:Fin n → Fin K), 0 < r → r ≤ ρ → ρ ≤ 1 → 1 ≤ M → (∀ k:Fin K, ‖w k‖ = 1 ∧ ((Set.ncard {i:Fin n | g i = k}:ℕ):ℝ) ≤ M) → (∀ i:Fin n, ‖v i‖ = 1 ∧ T r (x i) (v i) ⊆ Metric.ball 0 1 ∧ T r (x i) (v i) ⊆ T ρ (y (g i)) (w (g i))) → (∀ (k:Fin K) (W:Set LeanEval.Analysis.WangZahlKakeya.Space), Convex ℝ W → ENNReal.ofReal (((Set.ncard {i:Fin n | g i = k ∧ T r (x i) (v i) ⊆ W}:ℕ):ℝ) * r ^ 2) ≤ ENNReal.ofReal L * MeasureTheory.volume W) → ∃ (N:ℕ) (A:Fin N → (LeanEval.Analysis.WangZahlKakeya.Space ≃ᵃⁱ[ℝ] LeanEval.Analysis.WangZahlKakeya.Space)), ρ ^ 2 ≤ (N:ℝ) * M * r ^ 2 ∧ (N:ℝ) * M * r ^ 2 ≤ ρ ^ 2 + M * r ^ 2 ∧ (∀ (j:Fin N) (p:LeanEval.Analysis.WangZahlKakeya.Space), ‖p‖ < 1 → ‖A j p - p‖ ≤ ρ) ∧ ∀ (k:Fin K) (W:Set LeanEval.Analysis.WangZahlKakeya.Space), Convex ℝ W → ENNReal.ofReal (((Set.ncard {q:Fin N × Fin n | g q.2 = k ∧ T r (A q.1 (x q.2)) ((A q.1).linear (v q.2)) ⊆ W}:ℕ):ℝ) * r ^ 2) ≤ ENNReal.ofReal (C * r ^ (-ε) * Real.log (2 + (K:ℝ)) * L) * MeasureTheory.volume W) → ∀ ε:ℝ, 0 < ε → ∃ B:ℕ, 0 < B ∧ ∀ b:ℝ, 0 < b → ∃ η:ℝ, 0 < η ∧ ∃ δ₀:ℝ, 0 < δ₀ ∧ ∃ C:ℝ, 0 < C ∧ ∀ δ:ℝ, 0 < δ → δ ≤ δ₀ → ∀ (n:ℕ) (x v:Fin n → LeanEval.Analysis.WangZahlKakeya.Space), 0 < n → (∀ i:Fin n, ‖v i‖ = 1 ∧ T δ (x i) (v i) ⊆ Metric.ball 0 1) → (∀ i j:Fin n, i ≠ j → MeasureTheory.volume (T δ (x i) (v i) ∩ T δ (x j) (v j)) ≤ (1 / 2:ENNReal) * MeasureTheory.volume (T δ (x i) (v i))) → (∀ ρ₀:ℝ, δ ≤ ρ₀ → ρ₀ ≤ 1 → ∃ ρ:ℝ, ρ₀ ≤ ρ ∧ ρ < δ ^ (-η) * ρ₀ ∧ ∃ (N:ℕ) (y w:Fin N → LeanEval.Analysis.WangZahlKakeya.Space) (f:Fin n → Fin N), (∀ k:Fin N, ‖w k‖ = 1) ∧ (∀ i:Fin n, T δ (x i) (v i) ⊆ T ρ (y (f i)) (w (f i))) ∧ (∀ k k':Fin N, ((Set.ncard {i:Fin n | f i = k}:ℕ):ℝ) ≤ δ ^ (-η) * ((Set.ncard {i:Fin n | f i = k'}:ℕ):ℝ)) ∧ (∀ W:Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → ENNReal.ofReal (((Set.ncard {k:Fin N | T ρ (y k) (w k) ⊆ W}:ℕ):ℝ) * ρ ^ 2) ≤ ENNReal.ofReal (δ ^ (-η)) * MeasureTheory.volume W)) → ∀ G:Finset (Fin n), δ ^ η * (n:ℝ) ≤ (G.card:ℝ) → ∃ (N m:ℕ) (A:Fin N → (LeanEval.Analysis.WangZahlKakeya.Space ≃ᵃⁱ[ℝ] LeanEval.Analysis.WangZahlKakeya.Space)) (c:Fin m → Fin n) (g:Fin m → Fin N) (x' v':Fin m → LeanEval.Analysis.WangZahlKakeya.Space), 0 < m ∧ (N:ℝ) * (G.card:ℝ) * δ ^ 2 ≤ C * δ ^ (-ε) ∧ (∀ s:Fin m, c s ∈ G ∧ x' s = A (g s) (x (c s)) ∧ v' s = (A (g s)).linear (v (c s))) ∧ Q δ ε b B m x' v' := by
  intro T hT Q hQ hSS a ha
  subst T
  subst Q
  change SingleScale at hSS
  obtain ⟨B, hB, hprepare⟩ := prepare_source_tower ha
  refine ⟨B, hB, ?_⟩
  intro b hb
  obtain ⟨u, hu, dCopy, hdCopy, C, hC, hcopy⟩ := source_tower_copies hSS ha hb B
  obtain ⟨η, hη, dSource, hdSource, hsource⟩ := hprepare u hu
  refine ⟨η, hη, min dCopy dSource, lt_min hdCopy hdSource, C, hC, ?_⟩
  intro δ hδ hδd n x v hn htubes hsep hcover G hG
  have hGne : G.Nonempty := by
    apply Finset.card_pos.mp
    have hh : (0 : ℝ) < δ ^ η * (n : ℝ) :=
      mul_pos (Real.rpow_pos_of_pos hδ η) (by exact_mod_cast hn)
    exact_mod_cast hh.trans_le hG
  have hsupply : CoverSupply δ η n x v := by
    intro ρ₀ hδρ hρ1
    obtain ⟨ρ, hlo, hhi, k, y, w, f, hw, hsub, _, hc⟩ := hcover ρ₀ hδρ hρ1
    exact ⟨ρ, hlo, hhi.le, k, y, w, f, hw, hsub, hc⟩
  obtain ⟨m, c, D, hcG, hmass, hsourceTower⟩ :=
    hsource δ hδ (hδd.trans (min_le_right _ _)) n x v htubes hsep hsupply G hGne
  obtain ⟨N, m', A, c', g, x', v', hm', hN, hrel, hhierarchy⟩ :=
    hcopy δ hδ (hδd.trans (min_le_left _ _)) m
      (fun i => D (x (c i))) (fun i => D.linear (v (c i))) G.card hmass hsourceTower
  refine ⟨N, m', (fun j => D.trans (A j)), c ∘ c', g, x', v', hm', hN, ?_, hhierarchy⟩
  intro s
  exact ⟨hcG (c' s), (hrel s).1, (hrel s).2⟩
