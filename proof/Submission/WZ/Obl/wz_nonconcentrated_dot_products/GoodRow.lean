-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonconcentrated_dot_products.GoodRow.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic

namespace WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Deleting a small exceptional set of pairs leaves one row carrying at
least the expected remaining mass. -/
theorem exists_good_row {I J : Type*} [Fintype I] [Nonempty I] [Fintype J]
    (n : I → J → ℝ) (R : I → J → Prop) {M c d : ℝ} (hM : 0 ≤ M)
    (hn : ∀ i j, 0 ≤ n i j ∧ n i j ≤ M)
    (hbad : ((Finset.univ.filter (fun p : I × J => ¬R p.1 p.2)).card : ℝ) ≤
      c * (Fintype.card I : ℝ) * (Fintype.card J : ℝ))
    (hdensity : d * (Fintype.card I : ℝ) * (Fintype.card J : ℝ) * M ≤ ∑ i, ∑ j, n i j) :
    ∃ i, (d - c) * (Fintype.card J : ℝ) * M ≤ ∑ j, if R i j then n i j else 0 := by
  classical
  let B : Finset (I × J) := Finset.univ.filter (fun p => ¬R p.1 p.2)
  have hbad_eq : ∑ p ∈ B, n p.1 p.2 = ∑ i, ∑ j, if R i j then 0 else n i j := by
    simp only [B, Finset.sum_filter, Fintype.sum_prod_type, ite_not]
  have hbad_mass : (∑ i, ∑ j, if R i j then 0 else n i j) ≤
      c * (Fintype.card I : ℝ) * (Fintype.card J : ℝ) * M := by
    rw [← hbad_eq]
    calc ∑ p ∈ B, n p.1 p.2 ≤ ∑ _p ∈ B, M :=
          Finset.sum_le_sum (fun p hp => (hn p.1 p.2).2)
      _ = (B.card : ℝ) * M := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hbad hM
  have hsplit : (∑ i, ∑ j, n i j) =
      (∑ i, ∑ j, if R i j then n i j else 0) + (∑ i, ∑ j, if R i j then 0 else n i j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> ring
  have hgood : (d - c) * (Fintype.card I : ℝ) * (Fintype.card J : ℝ) * M ≤
      ∑ i, ∑ j, if R i j then n i j else 0 := by
    nlinarith [hdensity, hbad_mass, hsplit]
  obtain ⟨i, hi, hmax⟩ := Finset.univ.exists_max_image
    (fun i => ∑ j, if R i j then n i j else 0) Finset.univ_nonempty
  refine ⟨i, ?_⟩
  have hIpos : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  apply (mul_le_mul_iff_right₀ hIpos).mp
  calc (Fintype.card I : ℝ) * ((d - c) * (Fintype.card J : ℝ) * M) =
        (d - c) * (Fintype.card I : ℝ) * (Fintype.card J : ℝ) * M := by ring
    _ ≤ ∑ i, ∑ j, if R i j then n i j else 0 := hgood
    _ ≤ ∑ _k : I, ∑ j, if R i j then n i j else 0 := Finset.sum_le_sum (fun k hk => hmax k hk)
    _ = _ := by simp

theorem indexed_pair_filter_card (S T : Finset Plane) (P : Plane × Plane → Prop) :
    (Finset.univ.filter (fun p : S × T => P (p.1.val, p.2.val))).card =
      ((S ×ˢ T).filter P).card := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type,
    Finset.sum_product]
  rw [Finset.sum_coe_sort S (fun x => ∑ y : T, if P (x, y) then (1 : ℕ) else 0)]
  apply Finset.sum_congr rfl
  intro x hx
  exact Finset.sum_coe_sort T (fun y => if P (x, y) then (1 : ℕ) else 0)

end WangZahlLot.Obl.wz_nonconcentrated_dot_products
