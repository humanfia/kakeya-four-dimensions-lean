import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.PathLemma

namespace Submission.Obl.k4_graph_bsg

open scoped BigOperators
open WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

/-- A dense bipartite graph has a large rectangle with many retained edges and
many length-three walks between every pair of its vertices. -/
theorem retained_paths {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (A : Finset X) (B : Finset Y) (E : Finset (X × Y))
    (hE : E ⊆ A ×ˢ B) (hA : A.Nonempty) (hB : B.Nonempty)
    {θ : ℝ} (hθ : 0 < θ) (hdense : θ * (A.card : ℝ) * (B.card : ℝ) ≤ (E.card : ℝ)) :
    ∃ A' ⊆ A, ∃ B' ⊆ B,
      θ * (A.card : ℝ) / 6 ≤ (A'.card : ℝ) ∧
      θ * (B.card : ℝ) / 12 ≤ (B'.card : ℝ) ∧
      θ ^ 2 * (A.card : ℝ) * (B.card : ℝ) / 36 ≤ ((E ∩ A' ×ˢ B').card : ℝ) ∧
      ∀ a ∈ A', ∀ b ∈ B',
        θ ^ 5 * (A.card : ℝ) * (B.card : ℝ) / 6144 ≤
          ((pathSet A B E a b).card : ℝ) := by
  classical
  obtain ⟨U, hUA, hUdeg, hUcard, hUbad⟩ :=
    bsg_popular_vertex A B E hE hA hB hθ hdense
  let m : ℝ := U.card
  let t : ℝ := θ ^ 3 / 128 * (B.card : ℝ)
  have hm : 0 < m := lt_of_lt_of_le (by positivity : 0 < θ * (A.card : ℝ) / 3) hUcard
  have ht : 0 < t := by dsimp [t]; positivity
  let bad : X → Finset X := fun x => U.filter (fun z => ((commonNbhd B E x z).card : ℝ) < t)
  have hbad_sum : ∑ x ∈ U, ((bad x).card : ℝ) = ((badPairs U B E t).card : ℝ) := by
    have hc := card_filter_product_eq_sum U U
      (fun p => ((commonNbhd B E p.1 p.2).card : ℝ) < t)
    exact_mod_cast hc.symm
  have hbad_bound : ∑ x ∈ U, ((bad x).card : ℝ) ≤ θ * m ^ 2 / 16 := by
    rw [hbad_sum]
    have hu : (16 / θ) * ((badPairs U B E t).card : ℝ) ≤ m ^ 2 := hUbad
    rw [div_mul_eq_mul_div, div_le_iff₀ hθ] at hu
    linarith
  let A' := U.filter (fun a => ((bad a).card : ℝ) ≤ 3 * θ * m / 16)
  have hA'U : A' ⊆ U := Finset.filter_subset _ _
  have hA'bad (a : X) (ha : a ∈ A') : ((bad a).card : ℝ) ≤ 3 * θ * m / 16 :=
    (Finset.mem_filter.mp ha).2
  have hA'card : 2 * m / 3 ≤ (A'.card : ℝ) := by
    let R := U.filter (fun a => ¬ ((bad a).card : ℝ) ≤ 3 * θ * m / 16)
    have hsplit : (A'.card : ℝ) + (R.card : ℝ) = m := by
      dsimp [A', R, m]
      exact_mod_cast Finset.card_filter_add_card_filter_not
        (s := U) (p := fun a => ((bad a).card : ℝ) ≤ 3 * θ * m / 16)
    have hsumR : (R.card : ℝ) * (3 * θ * m / 16) ≤ θ * m ^ 2 / 16 := by
      calc (R.card : ℝ) * (3 * θ * m / 16) = ∑ a ∈ R, 3 * θ * m / 16 := by simp
           _ ≤ ∑ a ∈ R, ((bad a).card : ℝ) := Finset.sum_le_sum (fun a ha =>
             (not_le.mp (Finset.mem_filter.mp ha).2).le)
           _ ≤ ∑ a ∈ U, ((bad a).card : ℝ) :=
             Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Nat.cast_nonneg _)
           _ ≤ θ * m ^ 2 / 16 := hbad_bound
    have hc : (3 * (R.card : ℝ)) * (θ * m / 16) ≤ m * (θ * m / 16) := by
      nlinarith only [hsumR]
    have hRcard := le_of_mul_le_mul_right hc (by positivity : 0 < θ * m / 16)
    linarith
  let B' := B.filter (fun b => θ * m / 4 ≤ ((leftNbhd A' E b).card : ℝ))
  have hB'B : B' ⊆ B := Finset.filter_subset _ _
  have hB'deg (b : Y) (hb : b ∈ B') : θ * m / 4 ≤ ((leftNbhd A' E b).card : ℝ) :=
    (Finset.mem_filter.mp hb).2
  have htotal : (A'.card : ℝ) * (θ * (B.card : ℝ) / 2) ≤
      ∑ b ∈ B, ((leftNbhd A' E b).card : ℝ) := by
    have hswap := sum_card_filter_swap A' B (fun a b => (a, b) ∈ E)
    have hswap' : ∑ b ∈ B, ((leftNbhd A' E b).card : ℝ) =
        ∑ a ∈ A', (rightDeg B E a : ℝ) := by exact_mod_cast hswap
    rw [hswap']
    calc (A'.card : ℝ) * (θ * (B.card : ℝ) / 2) = ∑ a ∈ A', θ * (B.card : ℝ) / 2 := by simp
         _ ≤ ∑ a ∈ A', (rightDeg B E a : ℝ) :=
           Finset.sum_le_sum (fun a ha => hUdeg a (hA'U ha))
  have hedges_sum : ((E ∩ A' ×ˢ B').card : ℝ) =
      ∑ b ∈ B', ((leftNbhd A' E b).card : ℝ) := by
    have heq : E ∩ A' ×ˢ B' = (A' ×ˢ B').filter (fun p => p ∈ E) := by
      ext p
      simp only [Finset.mem_inter, Finset.mem_filter, and_comm]
    rw [heq, card_filter_product_eq_sum]
    have hswap := sum_card_filter_swap A' B' (fun a b => (a, b) ∈ E)
    exact_mod_cast hswap.symm
  have hedges : θ * m * (B.card : ℝ) / 12 ≤ ((E ∩ A' ×ˢ B').card : ℝ) := by
    have hsplit := Finset.sum_filter_add_sum_filter_not B
      (fun b => θ * m / 4 ≤ ((leftNbhd A' E b).card : ℝ))
      (fun b => ((leftNbhd A' E b).card : ℝ))
    have hout : ∑ b ∈ B.filter (fun b => ¬ θ * m / 4 ≤ ((leftNbhd A' E b).card : ℝ)),
        ((leftNbhd A' E b).card : ℝ) ≤ (B.card : ℝ) * (θ * m / 4) := by
      calc _ ≤ ∑ b ∈ B.filter (fun b => ¬ θ * m / 4 ≤ ((leftNbhd A' E b).card : ℝ)),
               θ * m / 4 := Finset.sum_le_sum (fun b hb =>
                 (not_le.mp (Finset.mem_filter.mp hb).2).le)
           _ = ((B.filter (fun b => ¬ θ * m / 4 ≤ ((leftNbhd A' E b).card : ℝ))).card : ℝ) *
               (θ * m / 4) := by simp
           _ ≤ (B.card : ℝ) * (θ * m / 4) := by
             apply mul_le_mul_of_nonneg_right _ (by positivity)
             exact_mod_cast Finset.card_filter_le B _
    have htotal' : (2 * m / 3) * (θ * (B.card : ℝ) / 2) ≤
        ∑ b ∈ B, ((leftNbhd A' E b).card : ℝ) :=
      (mul_le_mul_of_nonneg_right hA'card (by positivity)).trans htotal
    rw [hedges_sum]
    change (∑ b ∈ B', ((leftNbhd A' E b).card : ℝ)) + _ = _ at hsplit
    linarith
  have hB'card : θ * (B.card : ℝ) / 12 ≤ (B'.card : ℝ) := by
    have hbound : ((E ∩ A' ×ˢ B').card : ℝ) ≤ (B'.card : ℝ) * m := by
      rw [hedges_sum]
      calc ∑ b ∈ B', ((leftNbhd A' E b).card : ℝ) ≤ ∑ b ∈ B', m := by
             apply Finset.sum_le_sum
             intro b hb
             change ((leftNbhd A' E b).card : ℝ) ≤ (U.card : ℝ)
             exact_mod_cast Finset.card_le_card ((Finset.filter_subset _ _).trans hA'U)
           _ = (B'.card : ℝ) * m := by simp
    have hc : (θ * (B.card : ℝ) / 12) * m ≤ (B'.card : ℝ) * m := by
      nlinarith only [hedges, hbound]
    exact le_of_mul_le_mul_right hc hm
  refine ⟨A', hA'U.trans hUA, B', hB'B, ?_, hB'card, ?_, ?_⟩
  · change θ * (A.card : ℝ) / 3 ≤ m at hUcard
    linarith
  · have hh := mul_le_mul_of_nonneg_left hUcard (by positivity : 0 ≤ θ * (B.card : ℝ) / 12)
    dsimp [m] at hedges
    nlinarith only [hh, hedges]
  · intro a ha b hb
    let D := (leftNbhd A' E b).filter (fun z => ¬ ((commonNbhd B E a z).card : ℝ) < t)
    have hDcard : θ * m / 16 ≤ (D.card : ℝ) := by
      have hpartition : (((leftNbhd A' E b).filter
          (fun z => ((commonNbhd B E a z).card : ℝ) < t)).card : ℝ) + (D.card : ℝ) =
          ((leftNbhd A' E b).card : ℝ) := by
        exact_mod_cast Finset.card_filter_add_card_filter_not (s := leftNbhd A' E b)
          (p := fun z => ((commonNbhd B E a z).card : ℝ) < t)
      have hsub : (leftNbhd A' E b).filter (fun z => ((commonNbhd B E a z).card : ℝ) < t) ⊆ bad a :=
        Finset.filter_subset_filter _ ((Finset.filter_subset _ _).trans hA'U)
      have hc : (((leftNbhd A' E b).filter
          (fun z => ((commonNbhd B E a z).card : ℝ) < t)).card : ℝ) ≤ ((bad a).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      have hbdeg := hB'deg b hb
      have habad := hA'bad a ha
      linarith
    have hwalks : (D.card : ℝ) * t ≤ ((pathSet A B E a b).card : ℝ) := by
      have hsub : (D ×ˢ B).filter (fun p => (a, p.2) ∈ E ∧ p ∈ E) ⊆ pathSet A B E a b := by
        intro p hp
        obtain ⟨hpDB, hap, hpE⟩ := Finset.mem_filter.mp hp
        obtain ⟨hpD, hpB⟩ := Finset.mem_product.mp hpDB
        have hpN := (Finset.mem_filter.mp hpD).1
        obtain ⟨hpA', hpb⟩ := Finset.mem_filter.mp hpN
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hUA (hA'U hpA'), hpB⟩, hap, hpE, hpb⟩
      calc (D.card : ℝ) * t = ∑ z ∈ D, t := by simp
           _ ≤ ∑ z ∈ D, ((commonNbhd B E a z).card : ℝ) :=
             Finset.sum_le_sum (fun z hz => not_lt.mp (Finset.mem_filter.mp hz).2)
           _ = (((D ×ˢ B).filter (fun p => (a, p.2) ∈ E ∧ p ∈ E)).card : ℝ) := by
             rw [card_filter_product_eq_sum]
             push_cast
             rfl
           _ ≤ ((pathSet A B E a b).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    have h1 := mul_le_mul_of_nonneg_right hDcard ht.le
    have h2 := mul_le_mul_of_nonneg_left hUcard (by positivity : 0 ≤ θ / 16 * t)
    dsimp [m, t] at h1 h2 hwalks
    nlinarith only [h1, h2, hwalks]

end Submission.Obl.k4_graph_bsg
