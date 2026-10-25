-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_full_counted_hierarchy.FiniteChain.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.Hierarchy
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.Equivariance

namespace WangZahlLot.Obl.wz_nsp_full_counted_hierarchy

open Set MeasureTheory LeanEval.Analysis.WangZahlKakeya

/-- Enumerate a tower indexed by arbitrary finite types, preserving its precise
fiber cardinalities and convex counts. -/
theorem hierarchy_of_finite_chain {δ a b L κ : ℝ} {B J : ℕ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (ha : 0 < a)
    (hL : 0 ≤ L) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hJB : J + 1 ≤ B)
    (r : ℕ → ℝ) (I : ℕ → Type*) [∀ j, Fintype (I j)]
    (x v : ∀ j, I j → Space) (f : ∀ j, I (j + 1) → I j)
    (hr0 : r 0 = 1) (hrJ : r J = δ) (hn0 : Fintype.card (I 0) = 1)
    (hnJ : 0 < Fintype.card (I J))
    (hr : ∀ j, j ≤ J → δ ≤ r j ∧ r j ≤ 1)
    (hmono : ∀ j, j < J → r (j + 1) ≤ r j)
    (hgap : ∀ j, j < J → δ ^ (a / 2) * r j ≤ r (j + 1))
    (hv : ∀ j, j ≤ J → ∀ i, ‖v j i‖ = 1)
    (hball : ∀ i, Tube δ (x J i) (v J i) ⊆ Metric.ball 0 1)
    (hsub : ∀ j, j < J → ∀ i,
      Tube (r (j + 1)) (x (j + 1) i) (v (j + 1) i) ⊆
        Tube (r j) (x j (f j i)) (v j (f j i)))
    (hfull : ∀ j, j < J → ∀ i : I j,
      κ * (r j) ^ 2 ≤ (Set.ncard {s | f j s = i} : ℝ) * (r (j + 1)) ^ 2)
    (hlocal : ∀ j, j < J → ∀ k W, Convex ℝ W →
      ENNReal.ofReal ((Set.ncard {i | f j i = k ∧
        Tube (r (j + 1)) (x (j + 1) i) (v (j + 1) i) ⊆ W} : ℝ) * (r (j + 1)) ^ 2) ≤
      ENNReal.ofReal L * volume W)
    (hupper : (131072 * L) ^ J ≤ δ ^ (-b)) (hlower : δ ^ b ≤ κ ^ J) :
    FullHierarchy δ a b B (Fintype.card (I J))
      (x J ∘ (Fintype.equivFin (I J)).symm)
      (v J ∘ (Fintype.equivFin (I J)).symm) := by
  classical
  let e (j : ℕ) := (Fintype.equivFin (I j)).symm
  let fn (j : ℕ) (i : Fin (Fintype.card (I (j + 1)))) := (e j).symm (f j (e (j + 1) i))
  apply hierarchy_of_chain hδ hδ1 ha hL hκ hκ1 hJB r
    (fun j => Fintype.card (I j)) (fun j => x j ∘ e j) (fun j => v j ∘ e j)
    fn hr0 hrJ hn0 hnJ hr hmono hgap
  · intro j hj i
    exact hv j hj (e j i)
  · intro i
    exact hball (e J i)
  · intro j hj i
    simpa only [Function.comp_apply, fn, Equiv.apply_symm_apply] using hsub j hj (e (j + 1) i)
  · intro j hj i
    have hc := ncard_equiv (e (j + 1)) (fun s => f j s = e j i)
    have he : Set.ncard {s | fn j s = i} = Set.ncard {s | f j s = e j i} := by
      simpa only [fn, Equiv.symm_apply_eq] using hc
    rw [he]
    exact hfull j hj (e j i)
  · intro j hj k W hW
    have hc := ncard_equiv (e (j + 1)) (fun i => f j i = e j k ∧
      Tube (r (j + 1)) (x (j + 1) i) (v (j + 1) i) ⊆ W)
    have he : Set.ncard {i | fn j i = k ∧ Tube (r (j + 1))
        ((x (j + 1) ∘ e (j + 1)) i) ((v (j + 1) ∘ e (j + 1)) i) ⊆ W} =
        Set.ncard {i | f j i = e j k ∧ Tube (r (j + 1))
          (x (j + 1) i) (v (j + 1) i) ⊆ W} := by
      simpa only [fn, Function.comp_apply, Equiv.symm_apply_eq] using hc
    rw [he]
    exact hlocal j hj (e j k) W hW
  · exact hupper
  · exact hlower

end WangZahlLot.Obl.wz_nsp_full_counted_hierarchy
