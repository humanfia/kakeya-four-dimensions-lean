-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_concentrated_convex_factorization.Enumeration.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_concentrated_convex_factorization.Coefficient
import Submission.WZ.Obl.wz_tower_balanced_refinement.Reindex

namespace WangZahlLot.Obl.wz_concentrated_convex_factorization

open Set MeasureTheory
open WangZahlLot.Obl.wz_tower_balanced_refinement
  (enumerate enumerate_mem enumerate_injective exists_enumerate enumerate_fiber_card)

noncomputable section
attribute [local instance] Classical.propDecidable

lemma enumerate_ncard {α : Type*} [DecidableEq α] (S : Finset α) (P : α → Prop) :
    ncard {i : Fin S.card | P (enumerate S i)} = (S.filter P).card := by
  classical
  simpa only [eq_iff_iff, iff_true] using enumerate_fiber_card S P True

lemma count_enumerate {α : Type*} [DecidableEq α] (S : Finset α) (T : α → Set Space)
    (U : Set Space) : ncard {i : Fin S.card | T (enumerate S i) ⊆ U} = count T S U :=
  enumerate_ncard S (fun i => T i ⊆ U)

lemma count_filter_enumerate {α : Type*} [DecidableEq α] (S : Finset α)
    (T : α → Set Space) (V U : Set Space) :
    ncard {i : Fin S.card | T (enumerate S i) ⊆ V ∧ T (enumerate S i) ⊆ U} =
      count T (S.filter fun i => T i ⊆ V) U := by
  rw [enumerate_ncard S (fun i => T i ⊆ V ∧ T i ⊆ U)]
  unfold count
  congr 1
  ext i
  simp only [Finset.mem_filter, and_assoc]

lemma ncard_fintype {α : Type*} [Fintype α] [DecidableEq α] (P : α → Prop) :
    ncard {i | P i} = (Finset.univ.filter P).card := by
  rw [Set.ncard_eq_toFinset_card]
  congr 1
  ext i
  simp

lemma count_univ {n : ℕ} (T : Fin n → Set Space) (U : Set Space) :
    count T Finset.univ U = ncard {i : Fin n | T i ⊆ U} := by
  classical
  rw [Set.ncard_eq_toFinset_card]
  unfold count
  congr 1
  ext i
  simp

lemma Upper.real {α : Type*} [DecidableEq α] {T : α → Set Space} {w c : ℝ}
    {S : Finset α} (h : Upper T w S c) (hc : 0 ≤ c) {U : Set Space}
    (hU : Convex ℝ U) (hfin : volume U ≠ ⊤) :
    (count T S U : ℝ) * w ≤ c * (volume U).toReal := by
  have hr := (ENNReal.ofReal_le_iff_le_toReal
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin)).mp (h U hU)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc] using hr

end
end WangZahlLot.Obl.wz_concentrated_convex_factorization
