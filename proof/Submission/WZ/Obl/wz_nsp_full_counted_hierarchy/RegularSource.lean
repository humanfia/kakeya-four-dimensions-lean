-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_full_counted_hierarchy.RegularSource.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.RestrictedTree
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.BufferGeometry
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.Certificates

namespace WangZahlLot.Obl.wz_nsp_full_counted_hierarchy

open Set LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_tower_convex_count_composition (Counts)

/-- A buffered but unbalanced source tree can be regularized without changing
its radii or increasing its convex counts. -/
theorem regularize_source_tower {δ a u : ℝ} {B J Q : ℕ}
    (hJ : 0 < J) (hJB : J + 2 ≤ B) (hQ : 0 < Q)
    (r : ℕ → ℝ) (n : ℕ → ℕ) (z w : ∀ j, Fin (n j) → Space)
    (f : ∀ j, Fin (n (j + 1)) → Fin (n j))
    (p : ∀ j, Fin (n J) → Fin (n j))
    (hcoh : ∀ j, j < J → ∀ i, f j (p (j + 1) i) = p j i)
    (hpJ : ∀ i, p J i = i)
    (hnest : ∀ j k, j ≤ k → k < J + 1 → ∀ i i', p k i = p k i' → p j i = p j i')
    (color : ℕ → Fin Q)
    (hcolor : ∀ a b : ℕ, 0 < a → a ≤ n J → 0 < b → b ≤ n J →
      color a = color b → (a : ℝ) ≤ (4 / 3 : ℝ) * b)
    (hr0 : r 0 = (1 / 100 : ℝ)) (hrJ : r J = δ) (hn0 : n 0 = 1)
    (hnJ : 0 < n J) (htop : δ ^ (a / 2) ≤ (1 / 100 : ℝ))
    (hcard : (n J : ℝ) ≤ δ ^ (-7 : ℝ))
    (hl : ∀ j, j ≤ J → δ ≤ r j ∧ r j ≤ (1 / 100 : ℝ) ∧
      (∀ i, ‖w j i‖ = 1 ∧ Tube (r j) (z j i) (w j i) ⊆ Metric.ball 0 (3 / 4 : ℝ)) ∧
      Counts (r j) (δ ^ (-u)) (n j) (z j) (w j))
    (hedge : ∀ j, j < J → 16 * r (j + 1) ≤ r j ∧ δ ^ (a / 2) * r j ≤ r (j + 1) ∧
      ∀ i, Tube (r (j + 1)) (z (j + 1) i) (w (j + 1) i) ⊆
        Tube (r j / 4) (z j (f j i)) (w j (f j i))) :
    ∃ (m : ℕ) (c : Fin m → Fin (n J)), Function.Injective c ∧
      n J ≤ Q ^ (J + 1) * m ∧ SourceTower Tube δ a u B m (z J ∘ c) (w J ∘ c) := by
  classical
  have hU : (Finset.univ : Finset (Fin (n J))).Nonempty :=
    ⟨⟨0, hnJ⟩, Finset.mem_univ _⟩
  obtain ⟨S, hSU, hSne, hmass, hbranch⟩ := regularize_branches p J Q (n J) hQ
    color hcolor hnest Finset.univ (by simp) hU
  obtain ⟨k, q, g, hq, hg⟩ := restrict_partition_tower n J p f hcoh S hSne
  have hkJ : k J = S.card := by
    have hp : p J = id := funext hpJ
    calc
      k J = (Set.range (q J)).ncard := by
        simpa only [Set.ncard_range_of_injective (hq J).2.1, Nat.card_fin]
      _ = S.card := by rw [(hq J).2.2, hp]; simp
  have hk0 : k 0 = 1 := by
    have hc : k 0 ≤ n 0 := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective (q 0) (hq 0).2.1
    have := (hq 0).1
    omega
  have hm : (k J : ℝ) ≤ δ ^ (-7 : ℝ) := by
    apply le_trans _ hcard
    exact_mod_cast (show k J ≤ n J by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective (q J) (hq J).2.1)
  have hM (j) : ∃ M : ℝ, j < J → 1 ≤ M ∧ ∀ i ∈ S,
      M / 2 ≤ ((branchFiber S (p j) (p (j + 1)) i).card : ℝ) ∧
      ((branchFiber S (p j) (p (j + 1)) i).card : ℝ) ≤ M := by
    by_cases hj : j < J
    · obtain ⟨M, hM, hbranch'⟩ := hbranch j hj
      exact ⟨M, fun _ => ⟨hM, hbranch'⟩⟩
    · exact ⟨1, fun h => (hj h).elim⟩
  choose M hM using hM
  refine ⟨k J, q J, (hq J).2.1, ?_, ?_⟩
  · simpa only [Finset.card_univ, Fintype.card_fin, ← hkJ] using hmass
  · refine ⟨J, hJ, hJB, r, k, (fun j => z j ∘ q j), (fun j => w j ∘ q j),
      g, M, hr0, hrJ, hk0, ⟨Equiv.refl _, fun _ => ⟨rfl, rfl⟩⟩, htop, hm, ?_, ?_⟩
    · intro j hj
      refine ⟨(hl j hj).1, (hl j hj).2.1, (hq j).1, ?_, ?_⟩
      · intro i
        exact (hl j hj).2.2.1 (q j i)
      · exact counts_injective (z j) (w j) (q j) (hq j).2.1 (hl j hj).2.2.2
    · intro j hj
      refine ⟨(hedge j hj).1, (hedge j hj).2.1, (hM j hj).1, ?_, ?_⟩
      · intro t
        have ht : q j t ∈ (S.image (p j) : Set (Fin (n j))) := by
          rw [← (hq j).2.2]
          exact ⟨t, rfl⟩
        obtain ⟨i, hi, hpi⟩ := Finset.mem_image.mp ht
        rw [(hg j hj).2 t i hi hpi]
        exact (hM j hj).2 i hi
      · intro i
        change Tube (r (j + 1)) (z (j + 1) (q (j + 1) i)) (w (j + 1) (q (j + 1) i)) ⊆
          Tube (r j / 4) (z j (q j (g j i))) (w j (q j (g j i)))
        rw [(hg j hj).1]
        exact (hedge j hj).2.2 (q (j + 1) i)

end WangZahlLot.Obl.wz_nsp_full_counted_hierarchy
