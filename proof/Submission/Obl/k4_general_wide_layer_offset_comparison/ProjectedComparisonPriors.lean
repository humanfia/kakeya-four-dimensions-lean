import Submission.Obl.k4_general_wide_layer_offset_comparison.ActiveProjectedSlices
import Submission.Lib.K4OriginalStatePreparation.Numerics

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/ProjectedComparisonPriors.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The common original key records both major bins and the actual domain. -/
abbrev ComparisonCode := (Fin 2 → ℤ) × (ℤ × ℤ × ℤ)

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- Complete the key weight positively on unused null keys. Active original
keys keep exactly their original physical Jacobian and palette mass. -/
def comparisonCodeWeight (k : ℕ) (m h b : ℝ) : Option ComparisonCode → ℝ
  | none => 1
  | some c =>
    let w := p.N k ^ (-m) * h * b *
      (p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = c.1 0}).toReal
    if 0 < w then w else 1

def comparisonPrior (k : ℕ) (s m h b : ℝ) (c : Option ComparisonCode) : ℝ :=
  p.comparisonCodeWeight k m h b c * (p.N k ^ (-s)) ^ p.d

theorem comparisonCodeWeight_pos (k : ℕ) (m h b : ℝ) (c : Option ComparisonCode) :
    0 < p.comparisonCodeWeight k m h b c := by
  cases c with
  | none => exact zero_lt_one
  | some c => dsimp [comparisonCodeWeight]; split_ifs with hw <;> positivity

theorem comparisonPrior_pos {k : ℕ} {s m h b : ℝ} (hN : 0 < p.N k)
    (c : Option ComparisonCode) : 0 < p.comparisonPrior k s m h b c :=
  mul_pos (p.comparisonCodeWeight_pos k m h b c)
    (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hN _) _)

/-- One copy count works simultaneously for every original key, including
the null-key completion. Its cost is at most twice the coarse prior. -/
theorem comparisonPrior_copy_count {k : ℕ} {t : ℝ} (hN : 1 ≤ p.N k)
    (hd : 0 ≤ p.d) (ht : 0 ≤ t) (s m h b : ℝ) :
    ∃ n : ℕ, 0 < n ∧ ∀ c : Option ComparisonCode,
      p.comparisonPrior k s m h b c ≤ (n : ℝ) * p.comparisonPrior k (s + t) m h b c ∧
      (n : ℝ) * p.comparisonPrior k (s + t) m h b c ≤ 2 * p.comparisonPrior k s m h b c := by
  obtain ⟨n, hn, hc⟩ := Submission.Lib.K4OriginalStatePreparation.layer_copy_count hN hd ht s
  refine ⟨n, hn, ?_⟩
  intro c
  simpa only [comparisonPrior, neg_add, sub_eq_add_neg] using
    hc (p.comparisonCodeWeight k m h b c) (p.comparisonCodeWeight_pos k m h b c).le

end Parent

namespace ProjectedLayer

variable {α : Type} [MeasurableSpace α]

def sliceComparisonCode (L : ProjectedLayer α)
    {D : Fin L.count → Finset (ℤ × ℤ × ℤ)} (e : SliceIndex D) : ComparisonCode :=
  (L.tag e.1, e.2.val)

/-- The completed prior equals the unchanged sliced reference on every
positive original palette key. -/
theorem comparisonPrior_slice_eq (L : ProjectedLayer α) (p : Parent α) (hbase : p.Basic)
    {k : ℕ} {s m h b : ℝ} (hN : 0 < p.N k) (hh : 0 < h) (hb : 0 < b)
    {D : Fin L.count → Finset (ℤ × ℤ × ℤ)} (e : SliceIndex D)
    (hπ : 0 < p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = L.tag e.1 0}) :
    p.comparisonPrior k s m h b (some (L.sliceComparisonCode e)) =
      L.slicedWeight p k s m h b e.1 := by
  letI := (hbase k).2.2.1
  have hπr := ENNReal.toReal_pos hπ.ne' (measure_ne_top (p.π k) _)
  have hn := Real.rpow_pos_of_pos hN (-m)
  have ha := Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hN (-s)) p.d
  dsimp only [Parent.comparisonPrior, Parent.comparisonCodeWeight, sliceComparisonCode]
  rw [if_pos (by positivity)]
  unfold slicedWeight unscaledWeight
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (mul_nonneg hh.le hb.le),
    ENNReal.toReal_ofReal (mul_nonneg hn.le ha.le)]
  ring

/-- Adding the null off-cover index costs at most one unit of reference;
the actual active sources keep their entire original sliced budget. -/
theorem comparisonPrior_active_budget (L : ProjectedLayer α) (p : Parent α) (hbase : p.Basic)
    {k : ℕ} {s m H h g b : ℝ} (hN : 1 ≤ p.N k) (hs : 0 ≤ s) (hd : 0 ≤ p.d)
    (hh : 0 < h) (hb : 0 < b)
    (D : Fin L.count → Finset (ℤ × ℤ × ℤ)) (σ : Measure (α × ℝ))
    (hπ : ∀ e : L.ActiveSlice p k h g b D σ,
      0 < p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = L.tag e.val.1 0})
    (hbudget : (∑ e : SliceIndex D, L.slicedWeight p k s m h b e.1) ≤ 240 * H ^ 3) :
    (∑ e : Option (L.ActiveSlice p k h g b D σ),
      p.comparisonPrior k s m h b (e.map (fun e => L.sliceComparisonCode e.val))) ≤
        1 + 240 * H ^ 3 := by
  classical
  rw [Fintype.sum_option]
  have hsum : (∑ e : L.ActiveSlice p k h g b D σ,
      p.comparisonPrior k s m h b ((some e).map (fun e => L.sliceComparisonCode e.val))) =
      ∑ e : L.ActiveSlice p k h g b D σ, L.slicedWeight p k s m h b e.val.1 := by
    apply Finset.sum_congr rfl
    intro e _
    exact L.comparisonPrior_slice_eq p hbase (zero_lt_one.trans_le hN) hh hb e.val (hπ e)
  rw [hsum]
  have hsmall : (p.N k ^ (-s)) ^ p.d ≤ 1 :=
    Real.rpow_le_one (Real.rpow_nonneg (zero_le_one.trans hN) _)
      (Real.rpow_le_one_of_one_le_of_nonpos hN (neg_nonpos.mpr hs)) hd
  have hactive := L.activeSlice_reference_budget p (g := g) D σ hbudget
  change 1 * (p.N k ^ (-s)) ^ p.d + _ ≤ _
  linarith

end ProjectedLayer
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
