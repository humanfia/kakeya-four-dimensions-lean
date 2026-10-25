-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_full_counted_hierarchy.CopiedHierarchy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.CopiedCounts
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.FiniteChain

namespace WangZahlLot.Obl.wz_nsp_full_counted_hierarchy

open Set MeasureTheory LeanEval.Analysis.WangZahlKakeya
open scoped BigOperators

/-- An accumulated displacement bound preserves the final ball containment. -/
theorem composed_tube_ball (D : ℕ → ℕ)
    (A : ∀ j, Fin (D j) → (Space ≃ᵃⁱ[ℝ] Space)) (t : ℕ → ℝ)
    (J : ℕ) (hA : ∀ j, j < J → ∀ u p, ‖p‖ < 1 → ‖A j u p - p‖ ≤ t j)
    {δ R : ℝ} (hR : R ≤ 1) (hsum : R + ∑ i ∈ Finset.range J, t i ≤ 1)
    {x v : Space} (hball : Tube δ x v ⊆ Metric.ball 0 R) (u : MotionWord D J) :
    Tube δ (composedMotion D A J u x) ((composedMotion D A J u).linear v) ⊆ Metric.ball 0 1 := by
  rw [← rigid_tube_image]
  rintro _ ⟨p, hp, rfl⟩
  have hpR : ‖p‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hball hp
  have hd := composed_displacement D A t J hA (Nat.le_refl J) u (hpR.trans_le hR)
  have ht : ‖composedMotion D A J u p‖ ≤ ‖composedMotion D A J u p - p‖ + ‖p‖ := by
    simpa only [sub_add_cancel] using norm_add_le (composedMotion D A J u p - p) p
  have hout : ‖composedMotion D A J u p‖ < 1 := by linarith
  simpa only [Metric.mem_ball, dist_zero_right] using hout

/-- Duplicate the whole finite tower coherently, using one common list of rigid
motions at each depth. Local count and fullness estimates survive all prefixes. -/
theorem hierarchy_of_copied_chain {δ a b L κ : ℝ} {B J : ℕ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (ha : 0 < a)
    (hL : 0 ≤ L) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hJB : J + 1 ≤ B)
    (r : ℕ → ℝ) (n D : ℕ → ℕ) (x v : ∀ j, Fin (n j) → Space)
    (f : ∀ j, Fin (n (j + 1)) → Fin (n j))
    (A : ∀ j, Fin (D j) → (Space ≃ᵃⁱ[ℝ] Space))
    (hr0 : r 0 = 1) (hrJ : r J = δ) (hn0 : n 0 = 1) (hnJ : 0 < n J)
    (hD : ∀ j, j < J → 0 < D j)
    (hr : ∀ j, j ≤ J → δ ≤ r j ∧ r j ≤ 1)
    (hmono : ∀ j, j < J → r (j + 1) ≤ r j)
    (hgap : ∀ j, j < J → δ ^ (a / 2) * r j ≤ r (j + 1))
    (hv : ∀ j, j ≤ J → ∀ i, ‖v j i‖ = 1)
    (hball : ∀ u : MotionWord D J, ∀ i,
      Tube δ (composedMotion D A J u (x J i))
        ((composedMotion D A J u).linear (v J i)) ⊆ Metric.ball 0 1)
    (hsub : ∀ j, j < J → ∀ a i, Tube (r (j + 1))
      (A j a (x (j + 1) i)) ((A j a).linear (v (j + 1) i)) ⊆
      Tube (r j) (x j (f j i)) (v j (f j i)))
    (hfull : ∀ j, j < J → ∀ i : Fin (n j),
      κ * (r j) ^ 2 ≤ (D j : ℝ) * (Set.ncard {s | f j s = i} : ℝ) * (r (j + 1)) ^ 2)
    (hlocal : ∀ j, j < J → ∀ k W, Convex ℝ W →
      ENNReal.ofReal ((Set.ncard {q : Fin (D j) × Fin (n (j + 1)) |
        f j q.2 = k ∧ Tube (r (j + 1)) (A j q.1 (x (j + 1) q.2))
          ((A j q.1).linear (v (j + 1) q.2)) ⊆ W} : ℝ) * (r (j + 1)) ^ 2) ≤
        ENNReal.ofReal L * volume W)
    (hupper : (131072 * L) ^ J ≤ δ ^ (-b)) (hlower : δ ^ b ≤ κ ^ J) :
    let I := MotionWord D J × Fin (n J)
    let e := (Fintype.equivFin I).symm
    FullHierarchy δ a b B (Fintype.card I)
      (fun s => composedMotion D A J (e s).1 (x J (e s).2))
      (fun s => (composedMotion D A J (e s).1).linear (v J (e s).2)) := by
  let I (j : ℕ) := MotionWord D j × Fin (n j)
  let xn (j : ℕ) (s : I j) := composedMotion D A j s.1 (x j s.2)
  let vn (j : ℕ) (s : I j) := (composedMotion D A j s.1).linear (v j s.2)
  have hn0' : Fintype.card (I 0) = 1 := by
    simp only [I, Fintype.card_prod, card_motionWord, Finset.range_zero, Finset.prod_empty,
      Fintype.card_fin, one_mul, hn0]
  have hnJ' : 0 < Fintype.card (I J) := by
    simp only [I, Fintype.card_prod, card_motionWord, Fintype.card_fin]
    exact Nat.mul_pos (Finset.prod_pos (fun j hj => hD j (Finset.mem_range.mp hj))) hnJ
  apply hierarchy_of_finite_chain hδ hδ1 ha hL hκ hκ1 hJB r I xn vn
    (copiedParent f) hr0 hrJ hn0' hnJ' hr hmono hgap
  · intro j hj s
    exact rigid_unit (composedMotion D A j s.1) (hv j hj s.2)
  · intro s
    exact hball s.1 s.2
  · intro j hj s
    exact copied_containment D n A x v f r j (hsub j hj) s
  · intro j hj i
    dsimp only [I]
    rw [copied_fiber_card f j i.1 i.2, Nat.cast_mul]
    exact hfull j hj i.2
  · intro j hj k W hW
    exact copied_convex_counts D n A x v f j (r (j + 1)) L (hlocal j hj) k.1 k.2 W hW
  · exact hupper
  · exact hlower

end WangZahlLot.Obl.wz_nsp_full_counted_hierarchy
