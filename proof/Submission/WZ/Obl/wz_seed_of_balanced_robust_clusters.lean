-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_seed_of_balanced_robust_clusters.ScaleCases
import Submission.WZ.ChallengeDeps
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_seed_of_balanced_robust_clusters`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_seed_of_balanced_robust_clusters/`
belong to this obligation.
-/

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters

theorem WangZahlLot.wz_seed_of_balanced_robust_clusters : (fun (μ:MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) (B:Set (EuclideanSpace ℝ (Fin 3))) (T:ℝ → (EuclideanSpace ℝ (Fin 3)) → (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))) (D:(EuclideanSpace ℝ (Fin 3)) → (EuclideanSpace ℝ (Fin 3)) → ℝ) => (∃ C:ℝ, 1 ≤ C ∧ ∀ β:ℝ, 0 < β → β ≤ 1 → ∃ d:ℝ, 0 < d ∧ d ≤ (1 / 100:ℝ) ∧ ∀ δ lam:ℝ, 0 < δ → δ ≤ d → 0 < lam → lam ≤ 1 → ∀ (n:ℕ) (x v:Fin n → (EuclideanSpace ℝ (Fin 3))) (Y:Fin n → Set (EuclideanSpace ℝ (Fin 3))), 0 < n → (∀ i, ‖v i‖ = 1) → (∀ i, T δ (x i) (v i) ⊆ B) → (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ T δ (x i) (v i)) → (ENNReal.ofReal ((lam) * (n:ℝ) * (δ) ^ 2) ≤ Finset.sum Finset.univ (fun i:Fin n => μ (Y i))) → ∃ θ:ℝ, δ ≤ θ ∧ θ ≤ 1 ∧ ∃ (J:ℕ) (k:Fin J → ℕ) (f:(j:Fin J) → Fin (k j) → Fin n) (z w:Fin J → (EuclideanSpace ℝ (Fin 3))) (Z:(j:Fin J) → Fin (k j) → Set (EuclideanSpace ℝ (Fin 3))), 0 < J ∧ (∀ j, 0 < k j) ∧ (∀ j, Function.Injective (f j)) ∧ (∀ j, ‖w j‖ = 1) ∧ (∀ j i, MeasurableSet (Z j i)) ∧ (∀ j i, Z j i ⊆ Y (f j i)) ∧ (∀ j i, D (v (f j i)) (w j) ≤ C * θ) ∧ (∀ j i, T δ (x (f j i)) (v (f j i)) ⊆ Metric.thickening (C * θ) (segment ℝ (z j) ((z j) + (6:ℝ) • (w j)))) ∧ (∀ j j', j ≠ j' → Disjoint (⋃ i:Fin (k j), Z j i) (⋃ i:Fin (k j'), Z j' i)) ∧ (∀ j, (∀ p u r, ‖u‖ = 1 → δ ≤ r → (Set.ncard {i:Fin (k j) | p ∈ (Z j) i ∧ D ((fun i => v (f j i)) i) (u) ≤ r}:ℝ) ≤ C * (r / θ) ^ β * (Set.ncard {i:Fin (k j) | p ∈ (Z j) i}:ℝ))) ∧ (∀ j, ENNReal.ofReal ((δ ^ (C * β) * lam) * (k j:ℝ) * (δ) ^ 2) ≤ Finset.sum Finset.univ (fun i:Fin (k j) => μ ((Z j) i))) ∧ δ ^ (C * β) * lam * (n:ℝ) ≤ Finset.sum Finset.univ (fun j:Fin J => (k j:ℝ)) ∧ Finset.sum Finset.univ (fun j:Fin J => (k j:ℝ)) ≤ C * (n:ℝ)) → (∃ K:ℝ, 1 ≤ K ∧ ∀ C β α:ℝ, 1 ≤ C → 0 < β → β ≤ 1 → 0 < α → ∃ c:ℝ, 0 < c ∧ ∃ s:ℝ, 0 < s ∧ s ≤ (1 / 100:ℝ) ∧ ∀ δ θ lam m:ℝ, 0 < δ → δ ≤ (1 / 100:ℝ) → δ ≤ θ → θ ≤ 1 → δ ≤ s * θ → 0 < lam → lam ≤ 1 → 1 ≤ m → ∀ (n:ℕ) (x v:Fin n → (EuclideanSpace ℝ (Fin 3))) (Y:Fin n → Set (EuclideanSpace ℝ (Fin 3))) (z w:(EuclideanSpace ℝ (Fin 3))), 0 < n → (∀ i, ‖v i‖ = 1) → ‖w‖ = 1 → (∀ i, D (v i) (w) ≤ C * θ) → (∀ i, T δ (x i) (v i) ⊆ Metric.thickening (C * θ) (segment ℝ (z) ((z) + (6:ℝ) • (w)))) → (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ T δ (x i) (v i)) → (ENNReal.ofReal ((lam) * (n:ℝ) * (δ) ^ 2) ≤ Finset.sum Finset.univ (fun i:Fin n => μ (Y i))) → (∀ W:Set (EuclideanSpace ℝ (Fin 3)), Convex ℝ W → ENNReal.ofReal ((Set.ncard {i:Fin n | T δ (x i) (v i) ⊆ W}:ℝ) * (δ) ^ 2) ≤ ENNReal.ofReal (m) * μ W) → (∀ p u r, ‖u‖ = 1 → δ ≤ r → (Set.ncard {i:Fin n | p ∈ Y i ∧ D (v i) (u) ≤ r}:ℝ) ≤ C * (r / θ) ^ β * (Set.ncard {i:Fin n | p ∈ Y i}:ℝ)) → ENNReal.ofReal (c * δ ^ ((3 / 2:ℝ) + α) * θ ^ ((1 / 2:ℝ) - α) * lam ^ K * m ^ (-K) * (n:ℝ) ^ (1 / 2:ℝ)) ≤ μ ((⋃ i:Fin n, Y i))) → (∀ ε:ℝ, 0 < ε → ∃ a:ℝ, 0 < a ∧ ∃ η:ℝ, 0 < η ∧ ∀ δ:ℝ, 0 < δ → δ ≤ (1 / 100:ℝ) → ∀ (n:ℕ) (x v:Fin n → (EuclideanSpace ℝ (Fin 3))) (Y:Fin n → Set (EuclideanSpace ℝ (Fin 3))), 0 < n → (∀ i, ‖v i‖ = 1) → (∀ i, T δ (x i) (v i) ⊆ B) → (∀ i j:Fin n, i ≠ j → μ (T δ (x i) (v i) ∩ T δ (x j) (v j)) ≤ (1 / 2:ENNReal) * μ (T δ (x i) (v i))) → (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ T δ (x i) (v i)) → ENNReal.ofReal (δ ^ η * (n:ℝ) * δ ^ 2) ≤ Finset.sum Finset.univ (fun i:Fin n => μ (Y i)) → (∀ W:Set (EuclideanSpace ℝ (Fin 3)), Convex ℝ W → ENNReal.ofReal ((Set.ncard {i:Fin n | T δ (x i) (v i) ⊆ W}:ℝ) * δ ^ 2) ≤ ENNReal.ofReal (δ ^ (-η)) * μ W) → (∀ (u:(EuclideanSpace ℝ (Fin 3))) (t r:ℝ), ‖u‖ = 1 → 0 < r → ENNReal.ofReal (((Set.ncard {i:Fin n | T δ (x i) (v i) ⊆ (B ∩ {p:(EuclideanSpace ℝ (Fin 3)) | |inner ℝ u p - t| ≤ r})}:ℕ):ℝ)) ≤ ENNReal.ofReal ((δ ^ (-η)) * (n:ℝ)) * μ (B ∩ {p:(EuclideanSpace ℝ (Fin 3)) | |inner ℝ u p - t| ≤ r})) → ENNReal.ofReal (a * δ ^ ((0) + ε) * ((n:ℝ) * δ ^ 2) * ((n:ℝ) * δ) ^ (-(((1 / 2:ℝ)):ℝ))) ≤ μ (⋃ i:Fin n, Y i))) MeasureTheory.volume (Metric.ball (0:(EuclideanSpace ℝ (Fin 3))) 1) (fun (δ:ℝ) (x v:(EuclideanSpace ℝ (Fin 3))) => Metric.thickening δ (segment ℝ x (x + v))) (fun (v w:(EuclideanSpace ℝ (Fin 3))) => min ‖v - w‖ ‖v + w‖) := by
  classical
  intro hbal hrob ε hε
  obtain ⟨C, hC, hbal⟩ := hbal
  obtain ⟨K, hK, hrob⟩ := hrob
  obtain ⟨q, hq, hq1, heF, heC⟩ := choose_exponents hC hK hε
  obtain ⟨d, hd, hd100, hbal⟩ := hbal q hq hq1
  obtain ⟨c, hc, s, hs, hs100, hrob⟩ := hrob C q q hC hq hq1 hq
  have hC0 : 0 < C := by linarith
  let G : ℝ := 8 * (6 + C) * C ^ 2
  have hG : 0 < G := by dsimp [G]; positivity
  let B : ℝ := Vol (ball (0 : Space) 1) + 1
  have hB : 0 < B := by dsimp [B]; positivity
  let a : ℝ := min (c / (8 * C)) (min (s ^ 2 / (8 * G)) (d ^ 6 / B))
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨a, ha, q, hq, ?_⟩
  intro δ hδ hδ100 n x v Y hn hv ht hdistinct hYm hYT hdensity hconvex hslab
  have hδ1 : δ ≤ 1 := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm1 : 1 ≤ δ ^ (-q) := neg_rpow_ge_one hδ hδ1 hq.le
  have hm0 : 0 ≤ δ ^ (-q) := by positivity
  have hU : (⋃ i, Y i) ⊆ ball (0 : Space) 1 :=
    iUnion_subset (fun i => (hYT i).trans (ht i))
  have hUfin : volume (⋃ i, Y i) ≠ ⊤ := finite_volume_of_subset_ball hU
  apply (ENNReal.ofReal_le_iff_le_toReal hUfin).mpr
  rw [zero_add, target_identity hδ hn0 a ε]
  by_cases hsmall : δ ≤ d
  · have hlam : 0 < δ ^ q := Real.rpow_pos_of_pos hδ q
    have hlam1 : δ ^ q ≤ 1 := Real.rpow_le_one hδ.le hδ1 hq.le
    obtain ⟨θ, hδθ, hθ1, J, k, f, z, w, Z, hJ, hk, hf, hw, hZm, hZY,
        hdir, hcyl, hdisj, hrobust, hdens, hmass, hupper⟩ :=
      hbal δ (δ ^ q) hδ hsmall hlam hlam1 n x v Y hn hv ht hYm hYT hdensity
    have hθ : 0 < θ := hδ.trans_le hδθ
    let E : Fin J → Set Space := fun j => ⋃ i, Z j i
    have hEU : ∀ j, E j ⊆ ⋃ i, Y i := by
      intro j p hp
      obtain ⟨i, hi⟩ := mem_iUnion.mp hp
      exact mem_iUnion.mpr ⟨f j i, hZY j i hi⟩
    have hEfin : ∀ j, volume (E j) ≠ ⊤ := fun j =>
      ne_top_of_le_ne_top hUfin (measure_mono (hEU j))
    have hsum : ∑ j, Vol (E j) ≤ Vol (⋃ i, Y i) :=
      disjoint_sum_le hUfin (fun j => MeasurableSet.iUnion (hZm j)) hdisj hEU
    have hk0 : ∀ j, (0 : ℝ) ≤ k j := fun _ => Nat.cast_nonneg _
    have hL : 0 < δ ^ (C * q) * δ ^ q := by positivity
    have hL1 : δ ^ (C * q) * δ ^ q ≤ 1 := by
      calc
        δ ^ (C * q) * δ ^ q ≤ 1 * 1 := by
          gcongr
          exact Real.rpow_le_one hδ.le hδ1 (by positivity)
        _ = 1 := one_mul _
    by_cases hrelative : δ ≤ s * θ
    · have hcount : ∀ j, (k j : ℝ) ≤ (8 * C) * δ ^ (-q) * θ * (n : ℝ) :=
        fun j => cluster_slab_count hm0 hC0 hθ hslab ht (hf j) (hw j) (hcyl j)
      have hlocal : ∀ j,
          c * δ ^ ((3 / 2 : ℝ) + q) * θ ^ ((1 / 2 : ℝ) - q) *
            (δ ^ (C * q) * δ ^ q) ^ K * (δ ^ (-q)) ^ (-K) *
              (k j : ℝ) ^ (1 / 2 : ℝ) ≤ Vol (E j) := by
        intro j
        apply (ENNReal.ofReal_le_iff_le_toReal (hEfin j)).mp
        exact hrob δ θ (δ ^ (C * q) * δ ^ q) (δ ^ (-q)) hδ hδ100 hδθ hθ1
          hrelative hL hL1 hm1 (k j) (fun i => x (f j i)) (fun i => v (f j i))
          (Z j) (z j) (w j) (hk j) (fun i => hv (f j i)) (hw j) (hdir j) (hcyl j)
          (hZm j) (fun i => (hZY j i).trans (hYT (f j i))) (hdens j)
          (convex_count_subfamily hconvex (hf j)) (hrobust j)
      have hbound := fine_estimate (fun j => (k j : ℝ)) (fun j => Vol (E j))
        hδ hδ1 hθ hθ1 hC hq hc hn0 heF hk0 hcount hlocal hmass hsum
      apply le_trans _ hbound
      gcongr
      exact min_le_left _ _
    · have hcount : ∀ j, (k j : ℝ) * δ ^ 2 ≤ δ ^ (-q) * G * θ ^ 2 :=
        fun j => cylinder_count hm0 hC0.le hθ.le hθ1
          (convex_count_subfamily hconvex (hf j)) (hw j) (hcyl j)
      have hlocal : ∀ j, (δ ^ (C * q) * δ ^ q) * δ ^ 2 ≤ Vol (E j) := by
        intro j
        apply density_union_lower (hk j) (hEfin j)
        convert hdens j using 1
        congr 1
        ring
      have hlower := slab_count_lower hδ hm0 hn hv hslab ht
      have hbound := coarse_estimate (fun j => (k j : ℝ)) (fun j => Vol (E j))
        hδ hδ1 hθ.le hq hG hs hn0 (not_le.mp hrelative).le heC hk0
        hcount hlocal hmass hlower hsum
      apply le_trans _ hbound
      gcongr
      exact (min_le_right _ _).trans (min_le_left _ _)
  · have hvol : δ ^ q * δ ^ 2 ≤ Vol (⋃ i, Y i) := by
      apply density_union_lower hn hUfin
      convert hdensity using 1
      congr 1
      ring
    have hcount : (n : ℝ) * δ ^ 2 ≤ δ ^ (-q) * B := by
      apply (global_count hm0 hconvex ht).trans
      gcongr
      dsimp [B]
      linarith
    have hbound := compact_estimate hδ hδ1 hd (not_le.mp hsmall).le hq1 hn1 hB hε hvol hcount
    apply le_trans _ hbound
    gcongr
    exact (min_le_right _ _).trans (min_le_right _ _)
