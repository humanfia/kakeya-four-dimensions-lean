-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.TwoClassEmbeddings.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.TwoClassPairs
namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area
open Finset
open scoped Classical
private noncomputable def twoEmbeddingOffDiagEquiv {α : Type*} [Fintype α] :
    (Fin 2 ↪ α) ≃ ↥((Finset.univ : Finset α).offDiag) where
  toFun e := ⟨(e 0,e 1), by
    simp only [Finset.mem_offDiag, Finset.mem_univ, true_and]
    exact e.injective.ne (by decide)⟩
  invFun p := ⟨![p.val.1,p.val.2], by
    intro i j hij
    have hp := (Finset.mem_offDiag.mp p.property).2.2
    fin_cases i <;> fin_cases j <;> simp_all⟩
  left_inv e := by ext i; fin_cases i <;> rfl
  right_inv p := by apply Subtype.ext; rfl

theorem card_two_embeddings_le_four_same_add_two {α : Type*} [Fintype α]
    (color : α → Bool) :
    (Fintype.card (Fin 2 ↪ α):ℝ) ≤
      4*(Fintype.card {e : Fin 2 ↪ α // color (e 0)=color (e 1)}:ℝ)+2 := by
  have h := card_offDiag_le_four_mul_same_class_add_two color
  have ht : Fintype.card (Fin 2 ↪ α)=((Finset.univ : Finset α).offDiag).card := by
    rw [Fintype.card_congr twoEmbeddingOffDiagEquiv, Fintype.card_coe]
  have hs : Fintype.card {e : Fin 2 ↪ α // color (e 0)=color (e 1)}=
      (((Finset.univ : Finset α).offDiag).filter (fun p => color p.1=color p.2)).card := by
    calc
      _ = Fintype.card {p : ↥((Finset.univ : Finset α).offDiag) //
          color p.val.1=color p.val.2} := by
        apply Fintype.card_congr
        exact twoEmbeddingOffDiagEquiv.subtypeEquiv (fun _ => Iff.rfl)
      _ = Fintype.card {p : α × α //
          p ∈ (Finset.univ : Finset α).offDiag ∧ color p.1=color p.2} := by
        exact Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
          (fun p : α × α => p ∈ (Finset.univ : Finset α).offDiag)
          (fun p : α × α => color p.1=color p.2))
      _ = _ := Fintype.card_of_subtype _ (by intro p; simp only [Finset.mem_filter])
  rw [ht, hs]
  exact h

/-- The two-class bound restricted to pairs of elements satisfying a predicate. -/
theorem card_neighbor_embeddings_le_four_same_add_two {α : Type*} [Fintype α]
    (P : α → Prop) (color : α → Bool) :
    (Fintype.card {e : Fin 2 ↪ α // ∀ t, P (e t)}:ℝ) ≤
      4*(Fintype.card {e : Fin 2 ↪ α //
        (∀ t, P (e t)) ∧ color (e 0)=color (e 1)}:ℝ)+2 := by
  have h := card_two_embeddings_le_four_same_add_two
    (fun a : {a // P a} => color a.val)
  have ht : Fintype.card {e : Fin 2 ↪ α // ∀ t, P (e t)}=
      Fintype.card (Fin 2 ↪ {a // P a}) :=
    Fintype.card_congr (Equiv.codRestrict (Fin 2) {a | P a})
  have hs : Fintype.card {e : Fin 2 ↪ α //
      (∀ t, P (e t)) ∧ color (e 0)=color (e 1)}=
      Fintype.card {e : Fin 2 ↪ {a // P a} //
        color (e 0).val=color (e 1).val} := by
    apply Fintype.card_congr
    exact (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun e : Fin 2 ↪ α => ∀ t, P (e t))
      (fun e : Fin 2 ↪ α => color (e 0)=color (e 1))).symm.trans
      ((Equiv.codRestrict (Fin 2) {a | P a}).subtypeEquiv (fun _ => Iff.rfl))
  rw [ht, hs]
  exact h

/-- All same-class common-neighbor pairs either descend or are charged to
an exceptional set. This is the local hypothesis for the pair-rank count. -/
theorem neighbor_pair_count_le_rank_descent {α : Type*} [Fintype α]
    (P : α → Prop) (color : α → Bool) (Bad : (Fin 2 ↪ α) → Prop)
    (r : (Fin 2 ↪ α) → ℕ) (h : ℕ)
    (hgood : ∀ e, (∀ t, P (e t)) → color (e 0)=color (e 1) → ¬Bad e → r e<h) :
    (∑ e : Fin 2 ↪ α, if ∀ t, P (e t) then (1:ℝ) else 0) ≤
      4*(∑ e : Fin 2 ↪ α, if (∀ t, P (e t)) ∧ r e<h then (1:ℝ) else 0)+
      4*(∑ e : Fin 2 ↪ α, if (∀ t, P (e t)) ∧ Bad e then (1:ℝ) else 0)+2 := by
  have hclasses : (∑ e : Fin 2 ↪ α, if ∀ t, P (e t) then (1:ℝ) else 0) ≤
      4*(∑ e : Fin 2 ↪ α,
        if (∀ t, P (e t)) ∧ color (e 0)=color (e 1) then (1:ℝ) else 0)+2 := by
    simpa only [Fintype.card_subtype, Finset.sum_boole] using
      card_neighbor_embeddings_le_four_same_add_two P color
  have hcharge :
      (∑ e : Fin 2 ↪ α,
        if (∀ t, P (e t)) ∧ color (e 0)=color (e 1) then (1:ℝ) else 0) ≤
      (∑ e : Fin 2 ↪ α, if (∀ t, P (e t)) ∧ r e<h then (1:ℝ) else 0)+
      (∑ e : Fin 2 ↪ α, if (∀ t, P (e t)) ∧ Bad e then (1:ℝ) else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro e he
    by_cases hP : ∀ t, P (e t)
    · by_cases hc : color (e 0)=color (e 1)
      · by_cases hb : Bad e
        · simp only [hP, hc, hb, true_and, ite_true, le_add_iff_nonneg_left]
          split_ifs <;> norm_num
        · simp [hP, hc, hb, hgood e hP hc hb]
      · simp [hP, hc]
        split_ifs <;> norm_num
    · simp [hP]
  linarith

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
