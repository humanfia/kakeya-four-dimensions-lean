-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.TwoClassRank.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.PairRankCount
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.TwoClassEmbeddings

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Finset
open scoped Classical

/-- A two-class lens descent bounds all four-cycles, with an explicit
allowance for the exceptional cycles where nearby contacts spoil descent. -/
theorem four_cycle_count_le_of_two_class_rank {α β : Type*}
    [Fintype α] [Fintype β] (R : α → β → Prop)
    (rA : (Fin 2 ↪ α) → ℕ) (rB : (Fin 2 ↪ β) → ℕ) (h : ℕ)
    (hrA : ∀ e, rA e ≤ h) (hrB : ∀ e, rB e ≤ h)
    (colorA : (Fin 2 ↪ α) → β → Bool) (colorB : (Fin 2 ↪ β) → α → Bool)
    (Bad : (Fin 2 ↪ α) → (Fin 2 ↪ β) → Prop)
    (hgoodA : ∀ e f, (∀ s t, R (e s) (f t)) →
      colorA e (f 0)=colorA e (f 1) → ¬Bad e f → rB f<rA e)
    (hgoodB : ∀ e f, (∀ s t, R (e s) (f t)) →
      colorB f (e 0)=colorB f (e 1) → ¬Bad e f → rA e<rB f) :
    (Fintype.card {p : (Fin 2 ↪ β) × (Fin 2 ↪ α) //
      ∀ s t, R (p.2 s) (p.1 t)} : ℝ) ≤
      ((4:ℝ)^(h+1)+1)*(((Fintype.card α:ℝ)+(Fintype.card β:ℝ))^2+
        4*(∑ f : Fin 2 ↪ β, ∑ e : Fin 2 ↪ α,
          if (∀ s t, R (e s) (f t)) ∧ Bad e f then (1:ℝ) else 0)) := by
  let bA : (Fin 2 ↪ α) → ℝ := fun e =>
    4*(∑ f : Fin 2 ↪ β,
      if (∀ s t, R (e s) (f t)) ∧ Bad e f then (1:ℝ) else 0)+2
  let bB : (Fin 2 ↪ β) → ℝ := fun f =>
    4*(∑ e : Fin 2 ↪ α,
      if (∀ s t, R (e s) (f t)) ∧ Bad e f then (1:ℝ) else 0)+2
  have hbA : ∀ e, 0 ≤ bA e := by intro e; dsimp [bA]; positivity
  have hbB : ∀ f, 0 ≤ bB f := by intro f; dsimp [bB]; positivity
  have hpartA : ∀ e, (∑ f : Fin 2 ↪ β, if ∀ s t, R (e s) (f t) then (1:ℝ) else 0) ≤
      4*(∑ f : Fin 2 ↪ β,
        if (∀ s t, R (e s) (f t)) ∧ rB f < rA e then (1:ℝ) else 0)+bA e := by
    intro e
    have hh := neighbor_pair_count_le_rank_descent (fun b => ∀ s, R (e s) b)
      (colorA e) (Bad e) rB (rA e)
      (fun f hf hc hb => hgoodA e f (fun s t => hf t s) hc hb)
    simpa only [Fin.forall_fin_two, and_assoc, and_left_comm, and_comm, bA, add_assoc] using hh
  have hpartB : ∀ f, (∑ e : Fin 2 ↪ α, if ∀ s t, R (e s) (f t) then (1:ℝ) else 0) ≤
      4*(∑ e : Fin 2 ↪ α,
        if (∀ s t, R (e s) (f t)) ∧ rA e < rB f then (1:ℝ) else 0)+bB f := by
    intro f
    have hh := neighbor_pair_count_le_rank_descent (fun a => ∀ t, R a (f t))
      (colorB f) (fun e => Bad e f) rA (rB f)
      (fun e he hc hb => hgoodB e f he hc hb)
    simpa only [Fin.forall_fin_two, bB, add_assoc] using hh
  have hflow := four_cycle_count_le_of_pair_rank_descent R rA rB h (by norm_num : (1:ℝ) ≤ 4)
    hrA hrB bA bB hbA hbB hpartA hpartB
  let Qbad : ℝ := ∑ f : Fin 2 ↪ β, ∑ e : Fin 2 ↪ α,
    if (∀ s t, R (e s) (f t)) ∧ Bad e f then (1:ℝ) else 0
  have hbudget : (∑ e, bA e)+(∑ f, bB f)=
      2*((Fintype.card (Fin 2 ↪ α):ℝ)+(Fintype.card (Fin 2 ↪ β):ℝ))+8*Qbad := by
    simp only [bA, bB, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    have hcomm := Finset.sum_comm (s := (Finset.univ : Finset (Fin 2 ↪ α)))
      (t := (Finset.univ : Finset (Fin 2 ↪ β)))
      (f := fun (e : Fin 2 ↪ α) (f : Fin 2 ↪ β) =>
        if (∀ s t, R (e s) (f t)) ∧ Bad e f then (1:ℝ) else 0)
    dsimp [Qbad]
    linarith only [hcomm]
  have hpA : (Fintype.card (Fin 2 ↪ α):ℝ) ≤ (Fintype.card α:ℝ)^2 := by
    simp only [Fintype.card_embedding_eq, Fintype.card_fin]
    exact_mod_cast Nat.descFactorial_le_pow (Fintype.card α) 2
  have hpB : (Fintype.card (Fin 2 ↪ β):ℝ) ≤ (Fintype.card β:ℝ)^2 := by
    simp only [Fintype.card_embedding_eq, Fintype.card_fin]
    exact_mod_cast Nat.descFactorial_le_pow (Fintype.card β) 2
  have hpairs : (Fintype.card (Fin 2 ↪ α):ℝ)+(Fintype.card (Fin 2 ↪ β):ℝ) ≤
      ((Fintype.card α:ℝ)+(Fintype.card β:ℝ))^2 := by
    nlinarith only [hpA, hpB,
      mul_nonneg (Nat.cast_nonneg (Fintype.card α) : (0:ℝ) ≤ _) (Nat.cast_nonneg (Fintype.card β))]
  rw [hbudget] at hflow
  have hmult := mul_le_mul_of_nonneg_left hpairs
    (show 0 ≤ (4:ℝ)^(h+1)+1 by positivity)
  change _ ≤ ((4:ℝ)^(h+1)+1)*(_+4*Qbad)
  nlinarith only [hflow, hmult]

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
