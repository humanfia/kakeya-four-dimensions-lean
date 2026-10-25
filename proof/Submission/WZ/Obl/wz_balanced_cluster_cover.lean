-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_balanced_cluster_cover.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_balanced_cluster_cover.Clusters
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_balanced_cluster_cover`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_balanced_cluster_cover`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_balanced_cluster_cover/`
belong to this obligation.
-/


namespace WangZahlLot.Obl.wz_balanced_cluster_cover

open MeasureTheory Metric Set

/-- The obligation with its anonymous-function arguments beta-reduced. -/
theorem main (hsel : ∃ A : ℝ, 1 ≤ A ∧ ∀ β : ℝ, 0 < β → β ≤ 1 → ∃ d : ℝ, 0 < d ∧
    d ≤ (1 / 100 : ℝ) ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d → ∀ (n : ℕ) (v : Fin n → V)
    (Y : Fin n → Set V), 0 < n → (∀ i, ‖v i‖ = 1) → (∀ i, MeasurableSet (Y i)) →
    (∀ i, volume (Y i) ≠ ⊤) → ∃ θ : ℝ, δ ≤ θ ∧ θ ≤ 1 ∧ ∃ (Z : Fin n → Set V)
    (a : V → Fin n), (∀ i, MeasurableSet (Z i)) ∧ (∀ i, Z i ⊆ Y i) ∧
    (∀ i, MeasurableSet {p : V | a p = i}) ∧
    (∀ p i, p ∈ Z i → min ‖v i - v (a p)‖ ‖v i + v (a p)‖ ≤ A * θ) ∧
    (∀ p u r, ‖u‖ = 1 → δ ≤ r →
      (Set.ncard {i : Fin n | p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} : ℝ) ≤
        A * (r / θ) ^ β * (Set.ncard {i : Fin n | p ∈ Z i} : ℝ)) ∧
    ENNReal.ofReal (δ ^ (A * β)) * ∑ i, volume (Y i) ≤ ∑ i, volume (Z i)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ β : ℝ, 0 < β → β ≤ 1 → ∃ d : ℝ, 0 < d ∧ d ≤ (1 / 100 : ℝ) ∧
      ∀ δ lam : ℝ, 0 < δ → δ ≤ d → 0 < lam → lam ≤ 1 → ∀ (n : ℕ) (x v : Fin n → V)
      (Y : Fin n → Set V), 0 < n → (∀ i, ‖v i‖ = 1) →
      (∀ i, thickening δ (segment ℝ (x i) (x i + v i)) ⊆ ball 0 1) →
      (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ thickening δ (segment ℝ (x i) (x i + v i))) →
      (ENNReal.ofReal (lam * (n : ℝ) * δ ^ 2) ≤ ∑ i, volume (Y i)) →
      ∃ θ : ℝ, δ ≤ θ ∧ θ ≤ 1 ∧ ∃ (J : ℕ) (k : Fin J → ℕ) (f : (j : Fin J) → Fin (k j) → Fin n)
        (z w : Fin J → V) (Z : (j : Fin J) → Fin (k j) → Set V),
        0 < J ∧ (∀ j, 0 < k j) ∧ (∀ j, Function.Injective (f j)) ∧ (∀ j, ‖w j‖ = 1) ∧
        (∀ j i, MeasurableSet (Z j i)) ∧ (∀ j i, Z j i ⊆ Y (f j i)) ∧
        (∀ j i, min ‖v (f j i) - w j‖ ‖v (f j i) + w j‖ ≤ C * θ) ∧
        (∀ j i, thickening δ (segment ℝ (x (f j i)) (x (f j i) + v (f j i))) ⊆
          thickening (C * θ) (segment ℝ (z j) (z j + (6 : ℝ) • w j))) ∧
        (∀ j j', j ≠ j' → Disjoint (⋃ i : Fin (k j), Z j i) (⋃ i : Fin (k j'), Z j' i)) ∧
        (∀ j, ∀ p u r, ‖u‖ = 1 → δ ≤ r →
          (Set.ncard {i : Fin (k j) | p ∈ Z j i ∧
              min ‖v (f j i) - u‖ ‖v (f j i) + u‖ ≤ r} : ℝ) ≤
            C * (r / θ) ^ β * (Set.ncard {i : Fin (k j) | p ∈ Z j i} : ℝ)) ∧
        (∀ j, ENNReal.ofReal ((δ ^ (C * β) * lam) * (k j : ℝ) * δ ^ 2) ≤
          ∑ i, volume (Z j i)) ∧
        δ ^ (C * β) * lam * (n : ℝ) ≤ ∑ j, (k j : ℝ) ∧ ∑ j, (k j : ℝ) ≤ C * (n : ℝ) := by
  obtain ⟨A, hA, hsel⟩ := hsel
  set C₀ : ℝ := 2 * (2 * A + 2) ^ 3 * (4 * A + 14) ^ 3 with hC₀
  have hC₀nn : 0 ≤ C₀ := by positivity
  set C : ℝ := C₀ + A + 6 with hC
  refine ⟨C, by linarith, fun β hβ hβ1 => ?_⟩
  obtain ⟨d₁, hd₁, hd₁', hsel⟩ := hsel β hβ hβ1
  set K : ℝ := 2 * C₀ + 768 with hK
  have hKpos : 0 < K := by positivity
  set d₂ : ℝ := (1 / K) ^ (1 / β) with hd₂
  have hd₂pos : 0 < d₂ := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨min d₁ d₂, lt_min hd₁ hd₂pos, (min_le_left _ _).trans hd₁', ?_⟩
  intro δ lam hδ hδd hlam hlam1 n x v Y hn hv hTB hYm hYT hY
  have hδ1 : δ ≤ d₁ := hδd.trans (min_le_left _ _)
  have hδ2 : δ ≤ d₂ := hδd.trans (min_le_right _ _)
  have hYfin : ∀ i, volume (Y i) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top (measure_ball_lt_top (x := (0 : V)) (r := 1)).ne
      (measure_mono ((hYT i).trans (hTB i)))
  obtain ⟨θ, hδθ, hθ1, Z, a, hZm, hZY, ham, hdir, hcount, hZmass⟩ :=
    hsel δ hδ hδ1 n v Y hn hv hYm hYfin
  refine ⟨θ, hδθ, hθ1, ?_⟩
  have hδle1 : δ ≤ 1 := hδθ.trans hθ1
  have hEsmall : δ ^ (C * β) * K ≤ δ ^ (A * β) := by
    have e1 : δ ^ (C * β) = δ ^ (A * β) * δ ^ ((C - A) * β) := by
      rw [← Real.rpow_add hδ]
      congr 1
      ring
    have e2 : δ ^ ((C - A) * β) ≤ δ ^ β := by
      apply Real.rpow_le_rpow_of_exponent_ge hδ hδle1
      have : 1 ≤ C - A := by linarith
      nlinarith
    have e3 : δ ^ β ≤ 1 / K := by
      calc δ ^ β ≤ d₂ ^ β := Real.rpow_le_rpow hδ.le hδ2 hβ.le
        _ = 1 / K := by
          rw [hd₂, one_div β, Real.rpow_inv_rpow (by positivity) hβ.ne']
    have hDA : 0 < δ ^ (A * β) := Real.rpow_pos_of_pos hδ _
    rw [e1]
    calc δ ^ (A * β) * δ ^ ((C - A) * β) * K ≤ δ ^ (A * β) * (1 / K) * K := by
          gcongr
          exact e2.trans e3
      _ = δ ^ (A * β) := by field_simp
  have hmass : ENNReal.ofReal (δ ^ (A * β) * (lam * n * δ ^ 2)) ≤ ∑ i, volume (Z i) := by
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]
    exact (mul_le_mul_of_nonneg_left hY zero_le).trans hZmass
  exact exists_clusters hA (by linarith) (by linarith) hδ hδθ hθ1 hlam
    (Real.rpow_pos_of_pos hδ _) hEsmall hn x v Y Z a hv hTB hYT hZm hZY ham hdir hcount hmass

end WangZahlLot.Obl.wz_balanced_cluster_cover

theorem WangZahlLot.wz_balanced_cluster_cover : (fun (μ:MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) (B:Set (EuclideanSpace ℝ (Fin 3))) (T:ℝ → (EuclideanSpace ℝ (Fin 3)) → (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))) (D:(EuclideanSpace ℝ (Fin 3)) → (EuclideanSpace ℝ (Fin 3)) → ℝ) => (∃ A:ℝ, 1 ≤ A ∧ ∀ β:ℝ, 0 < β → β ≤ 1 → ∃ d:ℝ, 0 < d ∧ d ≤ (1 / 100:ℝ) ∧ ∀ δ:ℝ, 0 < δ → δ ≤ d → ∀ (n:ℕ) (v:Fin n → (EuclideanSpace ℝ (Fin 3))) (Y:Fin n → Set (EuclideanSpace ℝ (Fin 3))), 0 < n → (∀ i, ‖v i‖ = 1) → (∀ i, MeasurableSet (Y i)) → (∀ i, μ (Y i) ≠ ⊤) → ∃ θ:ℝ, δ ≤ θ ∧ θ ≤ 1 ∧ ∃ (Z:Fin n → Set (EuclideanSpace ℝ (Fin 3))) (a:(EuclideanSpace ℝ (Fin 3)) → Fin n), (∀ i, MeasurableSet (Z i)) ∧ (∀ i, Z i ⊆ Y i) ∧ (∀ i, MeasurableSet {p:(EuclideanSpace ℝ (Fin 3)) | a p = i}) ∧ (∀ p i, p ∈ Z i → D (v i) (v (a p)) ≤ A * θ) ∧ (∀ p u r, ‖u‖ = 1 → δ ≤ r → (Set.ncard {i:Fin n | p ∈ Z i ∧ D (v i) (u) ≤ r}:ℝ) ≤ A * (r / θ) ^ β * (Set.ncard {i:Fin n | p ∈ Z i}:ℝ)) ∧ ENNReal.ofReal (δ ^ (A * β)) * Finset.sum Finset.univ (fun i:Fin n => μ (Y i)) ≤ Finset.sum Finset.univ (fun i:Fin n => μ (Z i))) → (∃ C:ℝ, 1 ≤ C ∧ ∀ β:ℝ, 0 < β → β ≤ 1 → ∃ d:ℝ, 0 < d ∧ d ≤ (1 / 100:ℝ) ∧ ∀ δ lam:ℝ, 0 < δ → δ ≤ d → 0 < lam → lam ≤ 1 → ∀ (n:ℕ) (x v:Fin n → (EuclideanSpace ℝ (Fin 3))) (Y:Fin n → Set (EuclideanSpace ℝ (Fin 3))), 0 < n → (∀ i, ‖v i‖ = 1) → (∀ i, T δ (x i) (v i) ⊆ B) → (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ T δ (x i) (v i)) → (ENNReal.ofReal ((lam) * (n:ℝ) * (δ) ^ 2) ≤ Finset.sum Finset.univ (fun i:Fin n => μ (Y i))) → ∃ θ:ℝ, δ ≤ θ ∧ θ ≤ 1 ∧ ∃ (J:ℕ) (k:Fin J → ℕ) (f:(j:Fin J) → Fin (k j) → Fin n) (z w:Fin J → (EuclideanSpace ℝ (Fin 3))) (Z:(j:Fin J) → Fin (k j) → Set (EuclideanSpace ℝ (Fin 3))), 0 < J ∧ (∀ j, 0 < k j) ∧ (∀ j, Function.Injective (f j)) ∧ (∀ j, ‖w j‖ = 1) ∧ (∀ j i, MeasurableSet (Z j i)) ∧ (∀ j i, Z j i ⊆ Y (f j i)) ∧ (∀ j i, D (v (f j i)) (w j) ≤ C * θ) ∧ (∀ j i, T δ (x (f j i)) (v (f j i)) ⊆ Metric.thickening (C * θ) (segment ℝ (z j) ((z j) + (6:ℝ) • (w j)))) ∧ (∀ j j', j ≠ j' → Disjoint (⋃ i:Fin (k j), Z j i) (⋃ i:Fin (k j'), Z j' i)) ∧ (∀ j, (∀ p u r, ‖u‖ = 1 → δ ≤ r → (Set.ncard {i:Fin (k j) | p ∈ (Z j) i ∧ D ((fun i => v (f j i)) i) (u) ≤ r}:ℝ) ≤ C * (r / θ) ^ β * (Set.ncard {i:Fin (k j) | p ∈ (Z j) i}:ℝ))) ∧ (∀ j, ENNReal.ofReal ((δ ^ (C * β) * lam) * (k j:ℝ) * (δ) ^ 2) ≤ Finset.sum Finset.univ (fun i:Fin (k j) => μ ((Z j) i))) ∧ δ ^ (C * β) * lam * (n:ℝ) ≤ Finset.sum Finset.univ (fun j:Fin J => (k j:ℝ)) ∧ Finset.sum Finset.univ (fun j:Fin J => (k j:ℝ)) ≤ C * (n:ℝ))) MeasureTheory.volume (Metric.ball (0:(EuclideanSpace ℝ (Fin 3))) 1) (fun (δ:ℝ) (x v:(EuclideanSpace ℝ (Fin 3))) => Metric.thickening δ (segment ℝ x (x + v))) (fun (v w:(EuclideanSpace ℝ (Fin 3))) => min ‖v - w‖ ‖v + w‖) := by
  intro hsel
  exact WangZahlLot.Obl.wz_balanced_cluster_cover.main hsel
