-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_cover_refinement.Selection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_separated_cover_refinement

open Finset
open scoped Classical

/-- A symmetric relation of bounded degree has a coloring with a fixed palette. -/
theorem color_relation {I : Type*} [Fintype I] {K : ℕ} (hK : 0 < K)
    (R : I → I → Prop) (hR : ∀ {i j}, R i j → R j i)
    (hb : ∀ i, (univ.filter (R i)).card < K) :
    ∃ c : I → Fin K, ∀ i j, i ≠ j → R i j → c i ≠ c j := by
  classical
  have aux : ∀ s : Finset I, ∃ c : I → Fin K,
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j → R i j → c i ≠ c j := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨fun _ => ⟨0, hK⟩, by simp⟩
    | @insert a s ha ih =>
      obtain ⟨c, hc⟩ := ih
      let forbidden := (s.filter (R a)).image c
      have hcard : forbidden.card < (univ : Finset (Fin K)).card := by
        simp only [card_univ, Fintype.card_fin]
        exact (card_image_le.trans (card_le_card (filter_subset_filter _ (subset_univ s)))).trans_lt (hb a)
      obtain ⟨b, _, hb⟩ := exists_mem_notMem_of_card_lt_card hcard
      refine ⟨Function.update c a b, ?_⟩
      intro i hi j hj hij hrij
      rcases mem_insert.mp hi with hi | hi
      · subst i
        have hja : j ≠ a := Ne.symm hij
        have hjs : j ∈ s := (mem_insert.mp hj).resolve_left hja
        simp only [Function.update_self, Function.update_of_ne hja]
        intro he
        exact hb (mem_image.mpr ⟨j, mem_filter.mpr ⟨hjs, hrij⟩, he.symm⟩)
      · rcases mem_insert.mp hj with hj | hj
        · subst j
          have hia : i ≠ a := hij
          simp only [Function.update_self, Function.update_of_ne hia]
          intro he
          exact hb (mem_image.mpr ⟨i, mem_filter.mpr ⟨hi, hR hrij⟩, he⟩)
        · have hia : i ≠ a := ne_of_mem_of_not_mem hi ha
          have hja : j ≠ a := ne_of_mem_of_not_mem hj ha
          simpa only [Function.update_of_ne hia, Function.update_of_ne hja] using hc i hi j hj hij hrij
  obtain ⟨c, hc⟩ := aux univ
  exact ⟨c, fun i j => hc i (mem_univ _) j (mem_univ _)⟩

/-- One fibre of a finite map carries at least the mean weight. -/
theorem heavy_fibre {I J : Type*} [Fintype I] [Fintype J] [Nonempty J]
    (f : I → J) (w : I → ℝ) :
    ∃ j, (∑ i, w i) ≤ (Fintype.card J : ℝ) * ∑ i ∈ univ.filter (fun i => f i = j), w i := by
  classical
  let mass : J → ℝ := fun j => ∑ i ∈ univ.filter (fun i => f i = j), w i
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image univ mass univ_nonempty
  refine ⟨j, ?_⟩
  have hsum : ∑ j, mass j = ∑ i, w i := by
    dsimp [mass]
    exact sum_fiberwise_of_maps_to (fun _ _ => mem_univ _) _
  rw [← hsum]
  calc ∑ b, mass b ≤ ∑ _b : J, mass j :=
      sum_le_sum fun b hb => hmax b hb
    _ = (Fintype.card J : ℝ) * mass j := by simp

/-- Simultaneous pruning for an arbitrary finite collection of fibres.

Maximizing mass minus the cost of occupied fibres avoids an iterative deletion
construction. The bound records the full cost of the original fibres. -/
theorem prune_fibres {I J : Type*} [Fintype I] [Fintype J]
    (P : Finset I) (F : J → Finset I) (w : I → ℝ) {M t : ℝ}
    (hM : 0 < M) (ht : 0 < t) (hw : ∀ i, w i ≤ M) :
    ∃ Q : Finset I, Q ⊆ P ∧
      (∀ j, (Q ∩ F j).Nonempty → t * ((F j).card : ℝ) ≤ ((Q ∩ F j).card : ℝ)) ∧
      (∑ i ∈ P, w i) - M * t * (∑ j, ((F j).card : ℝ)) ≤ ∑ i ∈ Q, w i := by
  classical
  let active : Finset I → Finset J := fun Q => univ.filter fun j => (Q ∩ F j).Nonempty
  let cost : Finset I → ℝ := fun Q => ∑ j ∈ active Q, ((F j).card : ℝ)
  let mass : Finset I → ℝ := fun Q => ∑ i ∈ Q, w i
  let potential : Finset I → ℝ := fun Q => mass Q - M * t * cost Q
  obtain ⟨Q, hQP, hmax⟩ := Finset.exists_max_image P.powerset potential
    ⟨∅, by simp⟩
  have hQP' : Q ⊆ P := mem_powerset.mp hQP
  have hcost0 : ∀ S, 0 ≤ cost S := fun S => sum_nonneg (fun j _ => Nat.cast_nonneg _)
  have hcostle : ∀ S, cost S ≤ ∑ j, ((F j).card : ℝ) := fun S =>
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.cast_nonneg _)
  refine ⟨Q, hQP', ?_, ?_⟩
  · intro j hj
    by_contra hsmall
    have hsmall' : ((Q ∩ F j).card : ℝ) < t * ((F j).card : ℝ) := lt_of_not_ge hsmall
    let D := Q \ F j
    have hDP : D ⊆ P := (sdiff_subset).trans hQP'
    have hactive : active D ⊆ (active Q).erase j := by
      intro b hb
      obtain ⟨i, hi⟩ := (mem_filter.mp hb).2
      obtain ⟨hiD, hiF⟩ := mem_inter.mp hi
      obtain ⟨hiQ, hijnot⟩ := mem_sdiff.mp hiD
      refine mem_erase.mpr ⟨?_, mem_filter.mpr ⟨mem_univ _, ⟨i, mem_inter.mpr ⟨hiQ, hiF⟩⟩⟩⟩
      intro hbj
      exact hijnot (hbj ▸ hiF)
    have hjactive : j ∈ active Q := mem_filter.mpr ⟨mem_univ _, hj⟩
    have hcost : cost D + ((F j).card : ℝ) ≤ cost Q := by
      have hle : cost D ≤ ∑ b ∈ (active Q).erase j, ((F b).card : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hactive (fun _ _ _ => Nat.cast_nonneg _)
      have he := sum_erase_add (active Q) (fun b => ((F b).card : ℝ)) hjactive
      dsimp [cost] at *
      linarith
    have hsplit : mass D + (∑ i ∈ Q ∩ F j, w i) = mass Q := by
      dsimp [mass, D]
      rw [← sum_union (disjoint_sdiff_inter Q (F j)), sdiff_union_inter]
    have hremoved : (∑ i ∈ Q ∩ F j, w i) < M * t * ((F j).card : ℝ) := by
      calc ∑ i ∈ Q ∩ F j, w i ≤ ∑ _i ∈ Q ∩ F j, M :=
          sum_le_sum fun i _ => hw i
        _ = M * ((Q ∩ F j).card : ℝ) := by simp [mul_comm]
        _ < M * (t * ((F j).card : ℝ)) := mul_lt_mul_of_pos_left hsmall' hM
        _ = _ := by ring
    have hbound := hmax D (mem_powerset.mpr hDP)
    dsimp [potential] at hbound
    have hcostmul := mul_le_mul_of_nonneg_left hcost (show 0 ≤ M * t by positivity)
    nlinarith
  · have hmaxP := hmax P (mem_powerset.mpr Subset.rfl)
    dsimp [potential] at hmaxP
    have hle := mul_le_mul_of_nonneg_left (hcostle P) (show 0 ≤ M * t by positivity)
    have hnonneg := mul_nonneg (show 0 ≤ M * t by positivity) (hcost0 Q)
    dsimp [mass] at *
    linarith

/-- Select a common color pattern, then prune all its fibres simultaneously. -/
theorem select_regular {I L : Type*} [Fintype I] [Fintype L]
    (J : L → Type*) [∀ l, Fintype (J l)] [∀ l, DecidableEq (J l)]
    (f : ∀ l, I → J l) {K : ℕ} (hK : 0 < K) (c : ∀ l, J l → Fin K)
    (w : I → ℝ) {M t : ℝ} (hM : 0 < M) (ht : 0 < t) (hw : ∀ i, w i ≤ M) :
    ∃ Q : Finset I,
      (∀ l j, (Q.filter (fun i => f l i = j)).Nonempty →
        t * ((univ.filter (fun i => f l i = j)).card : ℝ) ≤
          ((Q.filter (fun i => f l i = j)).card : ℝ)) ∧
      (∀ l, ∀ i ∈ Q, ∀ i' ∈ Q, c l (f l i) = c l (f l i')) ∧
      (∑ i, w i) / (K : ℝ) ^ Fintype.card L -
        M * t * ((Fintype.card L : ℝ) * Fintype.card I) ≤ ∑ i ∈ Q, w i := by
  classical
  let : NeZero K := ⟨Nat.ne_of_gt hK⟩
  let color : I → (L → Fin K) := fun i l => c l (f l i)
  obtain ⟨a, ha⟩ := heavy_fibre color w
  let P := univ.filter (fun i => color i = a)
  let F : (Σ l, J l) → Finset I := fun j => univ.filter (fun i => f j.1 i = j.2)
  obtain ⟨Q, hQP, hQfib, hmass⟩ := prune_fibres P F w hM ht hw
  have hfib : ∀ l, ∑ j : J l, ((univ.filter (fun i => f l i = j)).card : ℝ) =
      Fintype.card I := by
    intro l
    have h := sum_card_fiberwise_eq_card_filter (univ : Finset I) (univ : Finset (J l)) (f l)
    exact_mod_cast (by simpa using h : (∑ j, (univ.filter (fun i => f l i = j)).card) = Fintype.card I)
  have hsum : ∑ j, ((F j).card : ℝ) = (Fintype.card L : ℝ) * Fintype.card I := by
    rw [Fintype.sum_sigma]
    dsimp [F]
    simp_rw [hfib]
    simp
  have he : ∀ l j, Q ∩ F ⟨l, j⟩ = Q.filter (fun i => f l i = j) := by
    intro l j
    ext i
    simp [F]
  refine ⟨Q, ?_, ?_, ?_⟩
  · intro l j hj
    have h := hQfib ⟨l, j⟩ (by rwa [he])
    simpa only [he] using h
  · intro l i hi i' hi'
    have hi := (mem_filter.mp (hQP hi)).2
    have hi' := (mem_filter.mp (hQP hi')).2
    exact congrFun (hi.trans hi'.symm) l
  · have hc : (Fintype.card (L → Fin K) : ℝ) = (K : ℝ) ^ Fintype.card L := by
      simp
    rw [hc] at ha
    have hP : (∑ i, w i) / (K : ℝ) ^ Fintype.card L ≤ ∑ i ∈ P, w i := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < (K : ℝ) ^ Fintype.card L)).mpr
      change (∑ i, w i) ≤ (∑ i ∈ P, w i) * (K : ℝ) ^ Fintype.card L
      rw [mul_comm]
      convert ha using 1
      congr 1
      apply Finset.sum_congr
      · ext i
        simp [P]
      · intro i _
        rfl
    rw [hsum] at hmass
    linarith

end WangZahlLot.Obl.wz_separated_cover_refinement
