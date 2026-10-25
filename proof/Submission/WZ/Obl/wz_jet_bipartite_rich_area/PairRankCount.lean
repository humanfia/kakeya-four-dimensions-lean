-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.PairRankCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.ExponentialRankFlow
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.FourCycleCount

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Finset
open scoped Classical
set_option backward.isDefEq.respectTransparency false

/-- Apply rank descent to the bipartite graph whose vertices are ordered
same-color pairs and whose edges are four-cycles of the original graph. -/
theorem four_cycle_count_le_of_pair_rank_descent {α β : Type*}
    [Fintype α] [Fintype β] (R : α → β → Prop)
    (rA : (Fin 2 ↪ α) → ℕ) (rB : (Fin 2 ↪ β) → ℕ) (h : ℕ)
    {k : ℝ} (hk : 1 ≤ k) (hrA : ∀ e, rA e ≤ h) (hrB : ∀ e, rB e ≤ h)
    (bA : (Fin 2 ↪ α) → ℝ) (bB : (Fin 2 ↪ β) → ℝ)
    (hbA : ∀ e, 0 ≤ bA e) (hbB : ∀ e, 0 ≤ bB e)
    (hpartA : ∀ e, (∑ f : Fin 2 ↪ β, if ∀ s t, R (e s) (f t) then (1:ℝ) else 0) ≤
      k*(∑ f : Fin 2 ↪ β,
        if (∀ s t, R (e s) (f t)) ∧ rB f < rA e then (1:ℝ) else 0)+bA e)
    (hpartB : ∀ f, (∑ e : Fin 2 ↪ α, if ∀ s t, R (e s) (f t) then (1:ℝ) else 0) ≤
      k*(∑ e : Fin 2 ↪ α,
        if (∀ s t, R (e s) (f t)) ∧ rA e < rB f then (1:ℝ) else 0)+bB f) :
    2*(Fintype.card {p : (Fin 2 ↪ β) × (Fin 2 ↪ α) //
      ∀ s t, R (p.2 s) (p.1 t)} : ℝ) ≤
      (k^(h+1)+1)*((∑ e, bA e)+(∑ f, bB f)) := by
  classical
  let S : ((Fin 2 ↪ α) ⊕ (Fin 2 ↪ β)) → ((Fin 2 ↪ α) ⊕ (Fin 2 ↪ β)) → Prop
    | .inl e, .inr f => ∀ s t, R (e s) (f t)
    | .inr f, .inl e => ∀ s t, R (e s) (f t)
    | _, _ => False
  let r := Sum.elim rA rB
  let b := Sum.elim bA bB
  have hsymm : ∀ ⦃i j⦄, S i j → S j i := by
    intro i j
    cases i <;> cases j <;> exact id
  have hr : ∀ i, r i ≤ h := by
    intro i
    cases i with
    | inl e => exact hrA e
    | inr f => exact hrB f
  have hb : ∀ i, 0 ≤ b i := by
    intro i
    cases i with
    | inl e => exact hbA e
    | inr f => exact hbB f
  have hpart : ∀ i, (∑ j, if S i j then (1:ℝ) else 0) ≤
      k*(∑ j, if S i j ∧ r j<r i then (1:ℝ) else 0)+b i := by
    intro i
    cases i with
    | inl e =>
      simp +instances only [Fintype.sum_sum_type, S, r, b, false_and, ite_false,
        Finset.sum_const_zero, zero_add, Sum.elim_inl, Sum.elim_inr]
      simpa only [Fin.forall_fin_two, Finset.sum_boole] using hpartA e
    | inr f =>
      simp +instances only [Fintype.sum_sum_type, S, r, b, false_and, ite_false,
        Finset.sum_const_zero, add_zero, Sum.elim_inl, Sum.elim_inr]
      simpa only [Fin.forall_fin_two, Finset.sum_boole] using hpartB f
  have hbound := degree_sum_le_of_exp_rank_descent S hsymm r h hk hr b hb hpart
  have hcard :
      (Fintype.card {p : (Fin 2 ↪ β) × (Fin 2 ↪ α) //
        ∀ s t, R (p.2 s) (p.1 t)} : ℝ) =
      ∑ f : Fin 2 ↪ β, ∑ e : Fin 2 ↪ α,
        if ∀ s t, R (e s) (f t) then (1:ℝ) else 0 := by
    calc
      _ = ∑ p : (Fin 2 ↪ β) × (Fin 2 ↪ α),
          if ∀ s t, R (p.2 s) (p.1 t) then (1:ℝ) else 0 := by
        simp only [Fintype.card_subtype, Finset.sum_boole]
      _ = _ := Fintype.sum_prod_type _
  rw [hcard]
  simp +instances only [Fintype.sum_sum_type, S, b, Sum.elim_inl, Sum.elim_inr,
    ite_false, Finset.sum_const_zero, zero_add, add_zero, Finset.sum_add_distrib,
    two_mul] at hbound ⊢
  have hcomm := Finset.sum_comm (s := (Finset.univ : Finset (Fin 2 ↪ α)))
    (t := (Finset.univ : Finset (Fin 2 ↪ β)))
    (f := fun (e : Fin 2 ↪ α) (f : Fin 2 ↪ β) =>
      if ∀ s t, R (e s) (f t) then (1:ℝ) else 0)
  dsimp +instances only [S] at hbound
  simp only [Fin.forall_fin_two] at hbound hcomm ⊢
  simp only [Finset.sum_boole] at hbound hcomm ⊢
  linarith only [hbound, hcomm]

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
