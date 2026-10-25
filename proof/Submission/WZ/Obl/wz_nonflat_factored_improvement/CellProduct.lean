-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonflat_factored_improvement.CellProduct.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_nonflat_factored_improvement

open MeasureTheory Set

/-- A common lower volume fraction in disjoint cells multiplies the coarse union volume. -/
theorem cell_union_product {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {q : ℕ} (C : Fin q → Set X) (S : Set X) (r : ENNReal)
    (hS : MeasurableSet S) (hC : ∀ j, MeasurableSet (C j))
    (hdisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hlocal : ∀ j, r * μ (C j) ≤ μ (S ∩ C j)) :
    r * μ (⋃ j, C j) ≤ μ S := by
  have hinter : Pairwise (fun i j => Disjoint (S ∩ C i) (S ∩ C j)) := by
    intro i j hij
    exact (hdisj hij).mono Set.inter_subset_right Set.inter_subset_right
  calc
    r * μ (⋃ j, C j) = r * ∑ j, μ (C j) := by
      rw [measure_iUnion hdisj hC, tsum_fintype]
    _ = ∑ j, r * μ (C j) := Finset.mul_sum _ _ _
    _ ≤ ∑ j, μ (S ∩ C j) := Finset.sum_le_sum fun j _ => hlocal j
    _ = μ (⋃ j, S ∩ C j) := by
      rw [measure_iUnion hinter (fun j => hS.inter (hC j)), tsum_fintype]
    _ ≤ μ S := measure_mono (Set.iUnion_subset fun _ => Set.inter_subset_left)

/-- The real-valued lower estimates may be multiplied without any finiteness assumption on `μ S`. -/
theorem cell_union_lower_bound {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {q : ℕ} (C : Fin q → Set X) (S : Set X) {A B : ℝ} (hA : 0 ≤ A)
    (hS : MeasurableSet S) (hC : ∀ j, MeasurableSet (C j))
    (hdisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hcoarse : ENNReal.ofReal A ≤ μ (⋃ j, C j))
    (hfine : ∀ j, ENNReal.ofReal B * μ (C j) ≤ μ (S ∩ C j)) :
    ENNReal.ofReal (A * B) ≤ μ S := by
  calc
    _ = ENNReal.ofReal B * ENNReal.ofReal A := by rw [ENNReal.ofReal_mul hA, mul_comm]
    _ ≤ ENNReal.ofReal B * μ (⋃ j, C j) := mul_le_mul_right hcoarse _
    _ ≤ μ S := cell_union_product μ C S (ENNReal.ofReal B) hS hC hdisj hfine

end WangZahlLot.Obl.wz_nonflat_factored_improvement
