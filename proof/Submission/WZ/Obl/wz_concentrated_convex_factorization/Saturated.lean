-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_concentrated_convex_factorization.Saturated.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_concentrated_convex_factorization.Enclosure

namespace WangZahlLot.Obl.wz_concentrated_convex_factorization

open Set MeasureTheory Metric
open scoped ENNReal

noncomputable section

/-- Extract a nonempty block with a prism saturating its own coefficient up to an absolute constant. -/
theorem saturated_block {ι : Type*} [DecidableEq ι] {δ m : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hm : 1 ≤ m)
    (x v : ι → Space) (S : Finset ι) (hS : S.Nonempty)
    (hv : ∀ i ∈ S, ‖v i‖ = 1) (hball : ∀ i ∈ S, Tube δ (x i) (v i) ⊆ ball 0 1)
    (hupper : Upper (fun i => Tube δ (x i) (v i)) (δ ^ 2) S m) :
    ∃ P : Finset ι, P ⊆ S ∧ P.Nonempty ∧
      ∃ (b : Frame) (z : Space) (a c : ℝ), δ ≤ a ∧ a ≤ c ∧ c ≤ 2 ∧
        (∀ i ∈ P, Tube δ (x i) (v i) ⊆ prism b z a c) ∧
        coefficient (fun i => Tube δ (x i) (v i)) (δ ^ 2) S * a * c ≤
          1024 * (P.card : ℝ) * δ ^ 2 := by
  classical
  let T := fun i => Tube δ (x i) (v i)
  let C := coefficient T (δ ^ 2) S
  have hC : 1 ≤ C := one_le_coefficient hm hupper
  by_cases hsmall : C ≤ 2
  · obtain ⟨i, hi⟩ := hS
    obtain ⟨b, hb⟩ := tube_prism hδ1 (x i) (hv i hi)
    refine ⟨{i}, Finset.singleton_subset_iff.mpr hi, Finset.singleton_nonempty _,
      b, x i, δ, δ, le_rfl, le_rfl, by linarith, ?_, ?_⟩
    · intro j hj
      simpa only [Finset.mem_singleton.mp hj] using hb
    · change C * δ * δ ≤ 1024 * (({i} : Finset ι).card : ℝ) * δ ^ 2
      simp only [Finset.card_singleton, Nat.cast_one, mul_one]
      nlinarith [sq_nonneg δ, mul_le_mul_of_nonneg_right hsmall (sq_nonneg δ)]
  · obtain ⟨U, hU, hfin, hdense⟩ := exists_dense_test (sq_nonneg δ) hm hupper (lt_of_not_ge hsmall)
    let P := S.filter fun i => T i ⊆ U
    have hP : P.Nonempty := by
      apply Finset.card_pos.mp
      have hc : 0 < (P.card : ℝ) * δ ^ 2 :=
        lt_of_le_of_lt (mul_nonneg (by dsimp [C] at hC ⊢; linarith) ENNReal.toReal_nonneg) hdense
      have : 0 < (P.card : ℝ) := (mul_pos_iff.mp hc).elim (fun h => h.1)
        (fun h => (not_lt_of_ge (sq_nonneg δ) h.2).elim)
      exact_mod_cast this
    obtain ⟨i, hi⟩ := hP
    have hiS := (Finset.mem_filter.mp hi).1
    have hTi := (Finset.mem_filter.mp hi).2
    obtain ⟨b, a, c, hδa, hac, hc2, hcover, harea⟩ := enclose_convex hδ
      (by linarith) hU hfin (hv i hiS) (Set.subset_inter hTi (hball i hiS))
    refine ⟨P, Finset.filter_subset _ _, ⟨i, hi⟩, b, x i, a, c, hδa, hac, hc2, ?_, ?_⟩
    · intro j hj
      obtain ⟨hjS, hjU⟩ := Finset.mem_filter.mp hj
      exact (Set.subset_inter hjU (hball j hjS)).trans hcover
    · have hC0 : 0 ≤ C := by linarith
      have h := mul_le_mul_of_nonneg_left harea hC0
      change C / 2 * (volume U).toReal < (P.card : ℝ) * δ ^ 2 at hdense
      change C * a * c ≤ 1024 * (P.card : ℝ) * δ ^ 2
      nlinarith

end
end WangZahlLot.Obl.wz_concentrated_convex_factorization
