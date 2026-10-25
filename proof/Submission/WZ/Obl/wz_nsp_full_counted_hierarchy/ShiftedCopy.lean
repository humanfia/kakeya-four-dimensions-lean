-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_full_counted_hierarchy.ShiftedCopy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.CopiedHierarchy
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.Mass

namespace WangZahlLot.Obl.wz_nsp_full_counted_hierarchy

open Set MeasureTheory LeanEval.Analysis.WangZahlKakeya
open scoped BigOperators

/-- Coherent copied containment keeps every descendant in the unmoved root
region, without estimating accumulated displacements. -/
theorem copied_tubes_in_set (r : ℕ → ℝ) (n D : ℕ → ℕ)
    (x v : ∀ j, Fin (n j) → Space)
    (f : ∀ j, Fin (n (j + 1)) → Fin (n j))
    (A : ∀ j, Fin (D j) → (Space ≃ᵃⁱ[ℝ] Space)) (J : ℕ) (W : Set Space)
    (hroot : ∀ i, Tube (r 0) (x 0 i) (v 0 i) ⊆ W)
    (hsub : ∀ j, j < J → ∀ a i, Tube (r (j + 1))
      (A j a (x (j + 1) i)) ((A j a).linear (v (j + 1) i)) ⊆
      Tube (r j) (x j (f j i)) (v j (f j i))) :
    ∀ j, j ≤ J → ∀ u : MotionWord D j, ∀ i,
      Tube (r j) (composedMotion D A j u (x j i))
        ((composedMotion D A j u).linear (v j i)) ⊆ W := by
  intro j
  induction j with
  | zero => intro hj u i; exact hroot i
  | succ j ih =>
      intro hj u i
      exact (copied_containment D n A x v f r j (hsub j (by omega)) (u, i)).trans
        (ih (by omega) (Fin.init u) (f j i))

/-- Add a single unmoved radius-one layer above a copied tower with a small
root. The extra level preserves the requested mesh and all count budgets. -/
theorem hierarchy_of_shifted_copies {δ a b h L κ : ℝ} {B J : ℕ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (ha : 0 < a) (hh : 0 < h) (hh1 : h ≤ 1)
    (hL : 1 ≤ L) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hκh : κ ≤ h ^ 2) (hκstep : κ ≤ (1 / 32 : ℝ)) (hJB : J + 2 ≤ B)
    (r : ℕ → ℝ) (n D : ℕ → ℕ) (x v : ∀ j, Fin (n j) → Space)
    (f : ∀ j, Fin (n (j + 1)) → Fin (n j))
    (A : ∀ j, Fin (D j) → (Space ≃ᵃⁱ[ℝ] Space))
    (hr0 : r 0 = h) (hrJ : r J = δ) (hn0 : n 0 = 1) (hnJ : 0 < n J)
    (hD : ∀ j, j < J → 0 < D j)
    (hr : ∀ j, j ≤ J → δ ≤ r j ∧ r j ≤ 1)
    (hmono : ∀ j, j < J → r (j + 1) ≤ r j)
    (htop : δ ^ (a / 2) ≤ h)
    (hgap : ∀ j, j < J → δ ^ (a / 2) * r j ≤ r (j + 1))
    (hv : ∀ j, j ≤ J → ∀ i, ‖v j i‖ = 1)
    (hroot : ∀ i, Tube (r 0) (x 0 i) (v 0 i) ⊆ Metric.ball 0 1)
    (hsub : ∀ j, j < J → ∀ a i, Tube (r (j + 1))
      (A j a (x (j + 1) i)) ((A j a).linear (v (j + 1) i)) ⊆
      Tube (r j) (x j (f j i)) (v j (f j i)))
    (hfull : ∀ j, j < J → ∀ i : Fin (n j),
      (1 / 32 : ℝ) * (r j) ^ 2 ≤
        (D j : ℝ) * (Set.ncard {s | f j s = i} : ℝ) * (r (j + 1)) ^ 2)
    (hlocal : ∀ j, j < J → ∀ k W, Convex ℝ W →
      ENNReal.ofReal ((Set.ncard {q : Fin (D j) × Fin (n (j + 1)) |
        f j q.2 = k ∧ Tube (r (j + 1)) (A j q.1 (x (j + 1) q.2))
          ((A j q.1).linear (v (j + 1) q.2)) ⊆ W} : ℝ) * (r (j + 1)) ^ 2) ≤
        ENNReal.ofReal L * volume W)
    (hupper : (131072 * L) ^ (J + 1) ≤ δ ^ (-b)) (hlower : δ ^ b ≤ κ ^ (J + 1)) :
    let I := MotionWord D J × Fin (n J)
    let e := (Fintype.equivFin I).symm
    FullHierarchy δ a b B (Fintype.card I)
      (fun s => composedMotion D A J (e s).1 (x J (e s).2))
      (fun s => (composedMotion D A J (e s).1).linear (v J (e s).2)) := by
  classical
  let I (j : ℕ) := MotionWord D (j - 1) × Fin (n (j - 1))
  let xn (j : ℕ) (s : I j) := composedMotion D A (j - 1) s.1 (x (j - 1) s.2)
  let vn (j : ℕ) (s : I j) := (composedMotion D A (j - 1) s.1).linear (v (j - 1) s.2)
  let r' : ℕ → ℝ | 0 => 1 | j + 1 => r j
  let f' : ∀ j, I (j + 1) → I j | 0 => id | j + 1 => copiedParent f j
  have hcard0 : Fintype.card (I 0) = 1 := by
    simp only [I, Nat.zero_sub, Fintype.card_prod, card_motionWord,
      Finset.range_zero, Finset.prod_empty, Fintype.card_fin, one_mul, hn0]
  have hcardJ : 0 < Fintype.card (I (J + 1)) := by
    simp only [I, Nat.add_sub_cancel, Fintype.card_prod, card_motionWord, Fintype.card_fin]
    exact Nat.mul_pos (Finset.prod_pos (fun j hj => hD j (Finset.mem_range.mp hj))) hnJ
  have hv' : ∀ j, j ≤ J + 1 → ∀ i, ‖vn j i‖ = 1 := by
    intro j hj i
    exact rigid_unit _ (hv (j - 1) (by omega) i.2)
  apply hierarchy_of_finite_chain hδ hδ1 ha (by linarith : 0 ≤ L) hκ hκ1 hJB
    r' I xn vn f' rfl hrJ hcard0 hcardJ
  · intro j hj
    cases j with
    | zero => exact ⟨hδ1.le, le_rfl⟩
    | succ j => exact hr j (by omega)
  · intro j hj
    cases j with
    | zero => simpa only [r', hr0] using hh1
    | succ j => exact hmono j (by omega)
  · intro j hj
    cases j with
    | zero => simpa only [r', hr0, mul_one] using htop
    | succ j => exact hgap j (by omega)
  · exact hv'
  · intro s
    change Tube δ (composedMotion D A J s.1 (x J s.2))
      ((composedMotion D A J s.1).linear (v J s.2)) ⊆ Metric.ball 0 1
    rw [← hrJ]
    exact copied_tubes_in_set r n D x v f A J (Metric.ball 0 1) hroot hsub J le_rfl s.1 s.2
  · intro j hj i
    cases j with
    | zero =>
        change Tube (r 0) (x 0 i.2) (v 0 i.2) ⊆ Tube 1 (x 0 i.2) (v 0 i.2)
        apply Metric.thickening_mono
        rwa [hr0]
    | succ j => exact copied_containment D n A x v f r j (hsub j (by omega)) i
  · intro j hj i
    cases j with
    | zero =>
        change κ * 1 ^ 2 ≤ (Set.ncard {s : I 0 | s = i} : ℝ) * (r 0) ^ 2
        simpa only [Set.ofPred_eq_eq_singleton, Set.ncard_singleton, Nat.cast_one,
          one_pow, mul_one, one_mul, hr0] using hκh
    | succ j =>
        change κ * (r j) ^ 2 ≤ (Set.ncard {s | copiedParent f j s = (i.1, i.2)} : ℝ) * (r (j + 1)) ^ 2
        rw [copied_fiber_card f j i.1 i.2, Nat.cast_mul]
        exact (mul_le_mul_of_nonneg_right hκstep (sq_nonneg _)).trans (hfull j (by omega) i.2)
  · intro j hj k W hW
    cases j with
    | zero =>
        have hsingle : ∀ i : Fin (n 0), ‖v 0 i‖ = 1 := hv 0 (by omega)
        have hc := singleton_convex_counts (hr0 ▸ hh) hn0 (x 0) (v 0) hsingle W hW
        change ENNReal.ofReal ((Set.ncard {s : I 0 | s = k ∧
          Tube (r 0) (x 0 s.2) (v 0 s.2) ⊆ W} : ℝ) * (r 0) ^ 2) ≤ _
        have he : Set.ncard {s : I 0 | s = k ∧ Tube (r 0) (x 0 s.2) (v 0 s.2) ⊆ W} ≤
            Set.ncard {i : Fin (n 0) | Tube (r 0) (x 0 i) (v 0 i) ⊆ W} := by
          apply Set.ncard_le_ncard_of_injOn (fun s => s.2)
          · intro s hs; exact hs.2
          · intro s hs t ht he
            exact hs.1.trans ht.1.symm
        apply (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr he) (sq_nonneg _))).trans
        exact hc.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hL) le_rfl)
    | succ j =>
        exact copied_convex_counts D n A x v f j (r (j + 1)) L
          (hlocal j (by omega)) k.1 k.2 W hW
  · exact hupper
  · exact hlower

end WangZahlLot.Obl.wz_nsp_full_counted_hierarchy
