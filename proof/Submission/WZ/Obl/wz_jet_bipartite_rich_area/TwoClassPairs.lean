-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.TwoClassPairs.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_kaufman_projection_count.Collision

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Finset
open WangZahlLot.Obl.wz_kaufman_projection_count (equalPairs card_sq_le_card_mul_equalPairs)

/-- Among distinct ordered pairs in a two-class partition, at least half
lie in the same class, up to one half of the number of elements. -/
theorem card_offDiag_le_two_mul_same_class_add_card {α : Type*} [Fintype α]
    (color : α → Bool) :
    (((Finset.univ : Finset α).offDiag).card : ℝ) ≤
      2*((((Finset.univ : Finset α).offDiag).filter
        (fun p => color p.1=color p.2)).card : ℝ)+(Fintype.card α:ℝ) := by
  classical
  let P := ((Finset.univ : Finset α).offDiag).filter
    (fun p => color p.1=color p.2)
  have hsplit : equalPairs color=(Finset.univ : Finset α).diag ∪ P := by
    ext p
    simp only [equalPairs, P, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_diag, Finset.mem_offDiag]
    by_cases hp : p.1=p.2
    · simp [hp]
    · simp [hp]
  have hdisj : Disjoint (Finset.univ : Finset α).diag P :=
    (Finset.disjoint_diag_offDiag (s := (Finset.univ : Finset α))).mono_right
      (Finset.filter_subset _ _)
  have hcard : (equalPairs color).card=Fintype.card α+P.card := by
    rw [hsplit, Finset.card_union_of_disjoint hdisj]
    simp only [Finset.diag, Finset.card_map, Finset.card_univ]
  have hfull : (Fintype.card α)^2=Fintype.card α+
      ((Finset.univ : Finset α).offDiag).card := by
    have h := Finset.card_union_of_disjoint
      (Finset.disjoint_diag_offDiag (s := (Finset.univ : Finset α)))
    rw [Finset.diag_union_offDiag] at h
    simpa only [Finset.card_product, Finset.diag, Finset.card_map, Finset.card_univ,
      pow_two] using h
  have hCS := card_sq_le_card_mul_equalPairs color
  simp only [Fintype.card_bool, Nat.cast_ofNat, hcard, Nat.cast_add] at hCS
  have hfull' : (Fintype.card α:ℝ)^2=(Fintype.card α:ℝ)+
      (((Finset.univ : Finset α).offDiag).card : ℝ) := by exact_mod_cast hfull
  change _ ≤ 2*(P.card:ℝ)+(Fintype.card α:ℝ)
  linarith

/-- A fixed-fraction version of the two-class count has an absolute error
of two, independent of the size of the neighbor set. -/
theorem card_offDiag_le_four_mul_same_class_add_two {α : Type*} [Fintype α]
    (color : α → Bool) :
    (((Finset.univ : Finset α).offDiag).card : ℝ) ≤
      4*((((Finset.univ : Finset α).offDiag).filter
        (fun p => color p.1=color p.2)).card : ℝ)+2 := by
  classical
  have h := card_offDiag_le_two_mul_same_class_add_card color
  have hfull : (Fintype.card α:ℝ)^2=(Fintype.card α:ℝ)+
      (((Finset.univ : Finset α).offDiag).card : ℝ) := by
    have hh := Finset.card_union_of_disjoint
      (Finset.disjoint_diag_offDiag (s := (Finset.univ : Finset α)))
    rw [Finset.diag_union_offDiag] at hh
    have hh' : (Fintype.card α)^2=Fintype.card α+
        ((Finset.univ : Finset α).offDiag).card := by
      simpa only [Finset.card_product, Finset.diag, Finset.card_map, Finset.card_univ,
        pow_two] using hh
    exact_mod_cast hh'
  have ht : 0 ≤ (Fintype.card α:ℝ) := Nat.cast_nonneg _
  have hsame : 0 ≤ (((Finset.univ : Finset α).offDiag).filter
      (fun p => color p.1=color p.2)).card := Nat.zero_le _
  have hsame' : 0 ≤ ((((Finset.univ : Finset α).offDiag).filter
      (fun p => color p.1=color p.2)).card : ℝ) := by exact_mod_cast hsame
  by_cases hsmall : Fintype.card α ≤ 2
  · have ht2 : (Fintype.card α:ℝ) ≤ 2 := by exact_mod_cast hsmall
    have hprod := mul_nonneg ht (sub_nonneg.mpr ht2)
    nlinarith
  · have ht3 : (3:ℝ) ≤ Fintype.card α := by exact_mod_cast (by omega : 3 ≤ Fintype.card α)
    have hprod := mul_nonneg ht (sub_nonneg.mpr ht3)
    nlinarith

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
