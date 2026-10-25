-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_full_counted_hierarchy.Hierarchy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.Geometry
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.Counting
import Submission.WZ.Obl.wz_tower_convex_count_composition.Composition

namespace WangZahlLot.Obl.wz_nsp_full_counted_hierarchy

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_tower_balanced_refinement
open WangZahlLot.Obl.wz_tower_convex_count_composition (Counts counts_compose counts_mono counts_root)

/-- The exact counted certificate used in the frozen statement. -/
abbrev FullHierarchy (δ a b : ℝ) (B m : ℕ) (x v : Fin m → Space) : Prop :=
  (∀ s, ‖v s‖ = 1 ∧ Tube δ (x s) (v s) ⊆ ball 0 1) ∧
  Counts δ (δ ^ (-b)) m x v ∧
  ∃ J : ℕ, 0 < J ∧ J ≤ B ∧ ∃ (r : Fin J → ℝ) (k : Fin J → ℕ)
    (z w : (j : Fin J) → Fin (k j) → Space) (f : (j : Fin J) → Fin m → Fin (k j)),
    (∀ j, δ ≤ r j ∧ r j ≤ 1 ∧ 0 < k j) ∧
    (∀ ρ₀ : ℝ, δ ≤ ρ₀ → ρ₀ ≤ 1 → ∃ j, ρ₀ ≤ r j ∧ r j ≤ δ ^ (-a) * ρ₀) ∧
    (∀ j i, ‖w j i‖ = 1) ∧
    (∀ j, Function.Surjective (f j)) ∧
    (∀ j s, Tube δ (x s) (v s) ⊆ Tube (r j) (z j (f j s)) (w j (f j s))) ∧
    (∀ j i, δ ^ b * (r j) ^ 2 ≤ (Set.ncard {s | f j s = i} : ℝ) * δ ^ 2) ∧
    (∀ j j', j ≤ j' → r j' ≤ r j ∧ ∃ p : Fin (k j') → Fin (k j),
      (∀ i', Tube (r j') (z j' i') (w j' i') ⊆
        Tube (r j) (z j (p i')) (w j (p i'))) ∧
      (∀ s, f j s = p (f j' s)))

/-- Compose the local convex bounds while retaining the particular tower. -/
theorem chain_convex_counts (J : ℕ) (r : ℕ → ℝ) (n : ℕ → ℕ)
    (x v : ∀ j, Fin (n j) → Space) (f : ∀ j, Fin (n (j + 1)) → Fin (n j))
    (L : ℝ) (hL : 0 ≤ L) (hr0 : r 0 = 1) (hn0 : n 0 = 1)
    (hr : ∀ j, j ≤ J → 0 < r j ∧ r j ≤ 1)
    (hv : ∀ j, j ≤ J → ∀ i, ‖v j i‖ = 1)
    (hsub : ∀ j, j < J → ∀ i,
      Tube (r (j + 1)) (x (j + 1) i) (v (j + 1) i) ⊆
        Tube (r j) (x j (f j i)) (v j (f j i)))
    (hlocal : ∀ j, j < J → ∀ k W, Convex ℝ W →
      ENNReal.ofReal ((Set.ncard {i | f j i = k ∧
        Tube (r (j + 1)) (x (j + 1) i) (v (j + 1) i) ⊆ W} : ℝ) * (r (j + 1)) ^ 2) ≤
      ENNReal.ofReal L * volume W) :
    ∀ j, j ≤ J → Counts (r j) ((131072 * L) ^ j) (n j) (x j) (v j) := by
  intro j
  induction j with
  | zero =>
      intro _
      simpa only [hr0, pow_zero] using counts_root hn0 (x 0) (v 0) (hv 0 (Nat.zero_le J))
  | succ j ih =>
      intro hj
      have hjlt : j < J := by omega
      have hjle : j ≤ J := by omega
      have hc := counts_compose (hr (j + 1) hj).1 (hr j hjle).1 (hr j hjle).2
        (show 0 ≤ (131072 * L) ^ j by positivity) hL
        (x (j + 1)) (v (j + 1)) (x j) (v j) (f j)
        (hv (j + 1) hj) (hv j hjle) (hsub j hjlt) (ih hjle) (hlocal j hjlt)
      convert hc using 1
      rw [pow_succ]
      ring

/-- Assemble a local-count tower into the full counted certificate. The two
budget inequalities isolate all losses from the geometric construction. -/
theorem hierarchy_of_chain {δ a b L κ : ℝ} {B J : ℕ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (ha : 0 < a)
    (hL : 0 ≤ L) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hJB : J + 1 ≤ B)
    (r : ℕ → ℝ) (n : ℕ → ℕ) (x v : ∀ j, Fin (n j) → Space)
    (f : ∀ j, Fin (n (j + 1)) → Fin (n j))
    (hr0 : r 0 = 1) (hrJ : r J = δ) (hn0 : n 0 = 1) (hnJ : 0 < n J)
    (hr : ∀ j, j ≤ J → δ ≤ r j ∧ r j ≤ 1)
    (hmono : ∀ j, j < J → r (j + 1) ≤ r j)
    (hgap : ∀ j, j < J → δ ^ (a / 2) * r j ≤ r (j + 1))
    (hv : ∀ j, j ≤ J → ∀ i, ‖v j i‖ = 1)
    (hball : ∀ i, Tube δ (x J i) (v J i) ⊆ ball 0 1)
    (hsub : ∀ j, j < J → ∀ i,
      Tube (r (j + 1)) (x (j + 1) i) (v (j + 1) i) ⊆
        Tube (r j) (x j (f j i)) (v j (f j i)))
    (hfull : ∀ j, j < J → ∀ i : Fin (n j),
      κ * (r j) ^ 2 ≤ (Set.ncard {s | f j s = i} : ℝ) * (r (j + 1)) ^ 2)
    (hlocal : ∀ j, j < J → ∀ k W, Convex ℝ W →
      ENNReal.ofReal ((Set.ncard {i | f j i = k ∧
        Tube (r (j + 1)) (x (j + 1) i) (v (j + 1) i) ⊆ W} : ℝ) * (r (j + 1)) ^ 2) ≤
      ENNReal.ofReal L * volume W)
    (hupper : (131072 * L) ^ J ≤ δ ^ (-b)) (hlower : δ ^ b ≤ κ ^ J) :
    FullHierarchy δ a b B (n J) (x J) (v J) := by
  classical
  have hrpos (j : ℕ) (hj : j ≤ J) : 0 < r j := hδ.trans_le (hr j hj).1
  have hdesc (j : ℕ) (hj : j ≤ J) (i : Fin (n j)) :
      δ ^ b * (r j) ^ 2 ≤ (Set.ncard {s | ancestor f hj s = i} : ℝ) * δ ^ 2 := by
    have hf := descendant_fullness n f r κ hκ.le J hfull hj (Nat.le_refl J) i
    rw [hrJ] at hf
    exact (mul_le_mul_of_nonneg_right
      (hlower.trans (pow_le_pow_of_le_one hκ.le hκ1 (Nat.sub_le _ _)))
      (sq_nonneg (r j))).trans hf
  have hsurj (j : ℕ) (hj : j ≤ J) : Function.Surjective (ancestor f hj) :=
    surjective_of_fullness (ancestor f hj) (Real.rpow_pos_of_pos hδ b) (hrpos j hj)
      (hdesc j hj)
  have hm (j k : ℕ) (hjk : j ≤ k) (hk : k ≤ J) : r k ≤ r j := by
    induction k, hjk using Nat.le_induction with
    | base => exact le_rfl
    | succ k hjk ih => exact (hmono k (by omega)).trans (ih (by omega))
  refine ⟨(fun i => ⟨hv J le_rfl i, hball i⟩), ?_, J + 1,
    Nat.succ_pos J, hJB, (fun j => r j), (fun j => n j),
    (fun j => x j), (fun j => v j), (fun j => ancestor f (by omega : j.val ≤ J)),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hc := chain_convex_counts J r n x v f L hL hr0 hn0
      (fun j hj => ⟨hrpos j hj, (hr j hj).2⟩) hv hsub hlocal J le_rfl
    rw [hrJ] at hc
    exact counts_mono hc hupper
  · intro j
    have hj : j.val ≤ J := by omega
    have hne : Nonempty (Fin (n j)) := ⟨ancestor f hj ⟨0, hnJ⟩⟩
    exact ⟨(hr j hj).1, (hr j hj).2, Fin.pos_iff_nonempty.mpr hne⟩
  · intro ρ₀ hρδ hρ1
    obtain ⟨j, hj, hρj, hjρ⟩ := select_radius r J δ (a / 2) a ρ₀
      hδ hδ1 (by positivity) (by linarith) hr0 hrJ hgap hρδ hρ1
    exact ⟨⟨j, by omega⟩, hρj, hjρ.le⟩
  · intro j i
    exact hv j (by omega) i
  · intro j
    exact hsurj j (by omega)
  · intro j s
    simpa only [hrJ] using ancestor_containment f
      (fun j i => Tube (r j) (x j i) (v j i)) J hsub (by omega : j.val ≤ J) le_rfl s
  · intro j i
    exact hdesc j (by omega) i
  · intro j j' hjj'
    have hjk : j.val ≤ j'.val := hjj'
    refine ⟨hm j j' hjk (by omega), ancestor f hjk, ?_, ?_⟩
    · intro i
      exact ancestor_containment f (fun j i => Tube (r j) (x j i) (v j i))
        J hsub hjk (by omega) i
    · intro s
      exact (ancestor_comp f hjk (by omega : j'.val ≤ J) s).symm

end WangZahlLot.Obl.wz_nsp_full_counted_hierarchy
