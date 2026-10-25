-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.SlopeWindow.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open scoped Classical

/-- Few cross pairs with a large slope gap put at least half the required
mass of each color in one common slope window. The center belongs to the
first color; no point-dependent choice has yet been made. -/
theorem exists_bipartite_slope_window {α β : Type*} (A : Finset α) (B : Finset β)
    (s : α → ℝ) (t : β → ℝ) {η μ : ℝ} (hμ : 0 < μ)
    (hA : μ ≤ (A.card : ℝ)) (hB : μ ≤ (B.card : ℝ))
    (hbad : ((((A ×ˢ B).filter fun ij => η ≤ |s ij.1 - t ij.2|).card : ℕ) : ℝ) <
      μ ^ 2 / 4) :
    ∃ a ∈ A, μ / 2 ≤ ((A.filter fun i => |s i - s a| ≤ 2 * η).card : ℝ) ∧
      μ / 2 ≤ ((B.filter fun j => |s a - t j| < η).card : ℝ) := by
  classical
  let E := (A ×ˢ B).filter fun ij => η ≤ |s ij.1 - t ij.2|
  have hsum : (E.card : ℝ) =
      ∑ i ∈ A, ((B.filter fun j => η ≤ |s i - t j|).card : ℝ) := by
    simp only [E, Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum,
      Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.sum_product]
  have hrow : ∃ a ∈ A, μ / 2 ≤ ((B.filter fun j => |s a - t j| < η).card : ℝ) := by
    by_contra hn
    push Not at hn
    have hrowbad : ∀ i ∈ A,
        μ / 2 ≤ ((B.filter fun j => η ≤ |s i - t j|).card : ℝ) := by
      intro i hi
      have hsplit := Finset.card_filter_add_card_filter_not (s := B)
        (fun j => |s i - t j| < η)
      simp only [not_lt] at hsplit
      have hsplit' : ((B.filter fun j => |s i - t j| < η).card : ℝ) +
          ((B.filter fun j => η ≤ |s i - t j|).card : ℝ) = B.card := by
        exact_mod_cast hsplit
      linarith [hn i hi]
    have hb : (A.card : ℝ) * (μ / 2) ≤ (E.card : ℝ) := by
      rw [hsum]
      simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hrowbad
    have hm := mul_le_mul_of_nonneg_right hA (by positivity : 0 ≤ μ / 2)
    change (E.card : ℝ) < μ ^ 2 / 4 at hbad
    nlinarith [sq_pos_of_pos hμ]
  obtain ⟨a, ha, hnearB⟩ := hrow
  refine ⟨a, ha, ?_, hnearB⟩
  by_contra hn
  have hsmall : ((A.filter fun i => |s i - s a| ≤ 2 * η).card : ℝ) < μ / 2 :=
    lt_of_not_ge hn
  let C := A.filter fun i => ¬ |s i - s a| ≤ 2 * η
  let W := B.filter fun j => |s a - t j| < η
  have hsplit := Finset.card_filter_add_card_filter_not (s := A)
    (fun i => |s i - s a| ≤ 2 * η)
  have hsplit' : ((A.filter fun i => |s i - s a| ≤ 2 * η).card : ℝ) +
      (C.card : ℝ) = A.card := by exact_mod_cast hsplit
  have hC : μ / 2 ≤ (C.card : ℝ) := by linarith
  have hsub : C ×ˢ W ⊆ E := by
    intro ij hij
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp hij
    obtain ⟨hiA, hiFar⟩ := Finset.mem_filter.mp hi
    obtain ⟨hjB, hjNear⟩ := Finset.mem_filter.mp hj
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hiA, hjB⟩, ?_⟩
    have htriangle := abs_sub_le (s ij.1) (t ij.2) (s a)
    rw [abs_sub_comm (t ij.2) (s a)] at htriangle
    push Not at hiFar
    linarith
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_product] at hcard
  have hcard' : (C.card : ℝ) * (W.card : ℝ) ≤ (E.card : ℝ) := by exact_mod_cast hcard
  have hprod := mul_le_mul hC hnearB (by positivity : 0 ≤ μ / 2) (Nat.cast_nonneg C.card)
  change (E.card : ℝ) < μ ^ 2 / 4 at hbad
  change μ / 2 * (μ / 2) ≤ (C.card : ℝ) * (W.card : ℝ) at hprod
  nlinarith

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
