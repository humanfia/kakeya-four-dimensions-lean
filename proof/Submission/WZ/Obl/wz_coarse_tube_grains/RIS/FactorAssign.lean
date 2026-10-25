-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.FactorAssign.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

/-!
# From an almost partitioning cover to a balanced assignment

Given a finite family `U` covered by sets indexed by `Fin L`, every element lying in between `1`
and `K` of them and every set containing between `M/K` and `M` elements of `U`, assign each element
to one set containing it and keep only the sets receiving at least `M/(2K²)` elements: at least half
of `U` survives and the assignment fibres lie in `[M/(2K²), M]`. This turns the output of WZ
Proposition 4.6 into the balanced assignment required by Proposition 5.2.
-/

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Factor

open Finset

theorem balanced_assignment {α : Type*} [DecidableEq α] {L : ℕ} (hL : 0 < L) (U : Finset α)
    (I : α → Fin L → Prop) [∀ k i, Decidable (I k i)] {K M : ℝ} (hK : 1 ≤ K) (hM : 0 < M)
    (hcov : ∀ k ∈ U, 1 ≤ (univ.filter fun i => I k i).card ∧
      ((univ.filter fun i => I k i).card : ℝ) ≤ K)
    (hrich : ∀ i, M / K ≤ ((U.filter fun k => I k i).card : ℝ) ∧
      ((U.filter fun k => I k i).card : ℝ) ≤ M) :
    ∃ (U' : Finset α) (G : Finset (Fin L)) (g : α → Fin L), U' ⊆ U ∧
      (U.card : ℝ) ≤ 2 * U'.card ∧ (∀ k ∈ U', I k (g k) ∧ g k ∈ G) ∧
      (∀ i ∈ G, M / (2 * K ^ 2) ≤ ((U'.filter fun k => g k = i).card : ℝ) ∧
        ((U'.filter fun k => g k = i).card : ℝ) ≤ M) := by
  classical
  have hex : ∀ k ∈ U, ∃ i : Fin L, I k i := fun k hk => by
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (hcov k hk).1
    exact ⟨i, (Finset.mem_filter.mp hi).2⟩
  let g : α → Fin L := fun k => if h : k ∈ U then Classical.choose (hex k h) else ⟨0, hL⟩
  have hg : ∀ k ∈ U, I k (g k) := fun k hk => by
    simp only [g, dif_pos hk]; exact Classical.choose_spec (hex k hk)
  let Fb : Fin L → Finset α := fun i => U.filter fun k => g k = i
  let G : Finset (Fin L) := univ.filter fun i => M / (2 * K ^ 2) ≤ ((Fb i).card : ℝ)
  let U' : Finset α := U.filter fun k => g k ∈ G
  have hK0 : 0 < K := by linarith
  -- the number of sets is at most `K² #U / M`
  have hdouble : (L : ℝ) * (M / K) ≤ K * U.card := by
    have h1 : ∑ i : Fin L, ((U.filter fun k => I k i).card : ℝ) =
        ∑ k ∈ U, ((univ.filter fun i => I k i).card : ℝ) := by
      simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      exact Finset.sum_comm
    calc (L : ℝ) * (M / K) = ∑ _i : Fin L, M / K := by simp
      _ ≤ ∑ i : Fin L, ((U.filter fun k => I k i).card : ℝ) :=
          Finset.sum_le_sum fun i _ => (hrich i).1
      _ = ∑ k ∈ U, ((univ.filter fun i => I k i).card : ℝ) := h1
      _ ≤ ∑ _k ∈ U, K := Finset.sum_le_sum fun k hk => (hcov k hk).2
      _ = K * U.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  refine ⟨U', G, g, Finset.filter_subset _ _, ?_, ?_, ?_⟩
  · -- at least half survives
    have hsplit := Finset.card_filter_add_card_filter_not (s := U) (fun k => g k ∈ G)
    have hbad : ((U.filter fun k => ¬ g k ∈ G).card : ℝ) ≤ U.card / 2 := by
      have hfib := Finset.card_eq_sum_card_fiberwise (f := g)
        (s := U.filter fun k => ¬ g k ∈ G) (t := univ.filter fun i => ¬ i ∈ G)
        (fun k hk => by
          simp only [Finset.coe_filter, Set.mem_setOf_eq] at hk
          simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and]
          exact hk.2)
      have hfib' : ((U.filter fun k => ¬ g k ∈ G).card : ℝ) =
          ∑ i ∈ univ.filter (fun i => ¬ i ∈ G), ((Fb i).card : ℝ) := by
        rw [hfib]
        push_cast
        apply Finset.sum_congr rfl
        intro i hi
        congr 2
        ext k
        simp only [Finset.mem_filter, Fb]
        constructor
        · rintro ⟨⟨hkU, _⟩, hki⟩; exact ⟨hkU, hki⟩
        · rintro ⟨hkU, hki⟩
          refine ⟨⟨hkU, ?_⟩, hki⟩
          rw [hki]; exact (Finset.mem_filter.mp hi).2
      rw [hfib']
      calc ∑ i ∈ univ.filter (fun i => ¬ i ∈ G), ((Fb i).card : ℝ)
          ≤ ∑ _i ∈ univ.filter (fun i => ¬ i ∈ G), M / (2 * K ^ 2) := by
            apply Finset.sum_le_sum
            intro i hi
            have hnot := (Finset.mem_filter.mp hi).2
            simp only [G, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hnot
            exact hnot.le
        _ ≤ ∑ _i : Fin L, M / (2 * K ^ 2) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun _ _ _ => by positivity)
        _ = (L : ℝ) * (M / K) / (2 * K) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            field_simp
        _ ≤ K * U.card / (2 * K) := by gcongr
        _ = U.card / 2 := by field_simp
    have hsplit' : ((U'.card : ℕ) : ℝ) + ((U.filter fun k => ¬ g k ∈ G).card : ℝ) = U.card := by
      exact_mod_cast hsplit
    linarith
  · intro k hk
    obtain ⟨hkU, hkG⟩ := Finset.mem_filter.mp hk
    exact ⟨hg k hkU, hkG⟩
  · intro i hi
    have heq : (U'.filter fun k => g k = i) = Fb i := by
      ext k
      simp only [U', Fb, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hkU, _⟩, hki⟩; exact ⟨hkU, hki⟩
      · rintro ⟨hkU, hki⟩; exact ⟨⟨hkU, hki ▸ hi⟩, hki⟩
    rw [heq]
    refine ⟨(Finset.mem_filter.mp hi).2, ?_⟩
    refine le_trans ?_ (hrich i).2
    exact_mod_cast Finset.card_le_card fun k hk => by
      obtain ⟨hkU, hki⟩ := Finset.mem_filter.mp hk
      exact Finset.mem_filter.mpr ⟨hkU, hki ▸ hg k hkU⟩

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Factor
