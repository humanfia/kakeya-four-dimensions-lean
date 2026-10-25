import Submission.Obl.k4_quadratic_finite_greedy_cover.Coverage

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/OriginalListCounts.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Count original witnesses, rather than their intersections with the
current pair law. The common palette weight cancels from the count. -/
theorem card_le_from_original_witnesses
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (μ : Measure Ω) (U : Set Ω) (E : ι → Set Ω) (S : Finset ι)
    {a C : ℝ} (ha : 0 < a) (hC : 0 < C)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hwtop : w ≠ ⊤)
    (hcap : μ U ≤ ENNReal.ofReal C * w)
    (hE : ∀ i ∈ S, MeasurableSet (E i) ∧ E i ⊆ U)
    (hdisj : (S : Set ι).PairwiseDisjoint E)
    (hfloor : ∀ i ∈ S, ENNReal.ofReal a * w ≤ μ (E i)) :
    (S.card : ℝ) ≤ C / a := by
  by_cases hS : S.Nonempty
  · obtain ⟨i₀, hi₀⟩ := hS
    have hUfin : μ U ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) hcap
    have hUpos : 0 < μ U := by
      have hp : 0 < ENNReal.ofReal a * w :=
        pos_iff_ne_zero.mpr (mul_ne_zero (ENNReal.ofReal_pos.mpr ha).ne' hw)
      exact hp.trans_le ((hfloor i₀ hi₀).trans (measure_mono (hE i₀ hi₀).2))
    have hf (i : ι) (hi : i ∈ S) : ENNReal.ofReal (a / C) * μ U ≤ μ (E i) := by
      calc
        _ ≤ ENNReal.ofReal (a / C) * (ENNReal.ofReal C * w) := mul_le_mul_right hcap _
        _ = ENNReal.ofReal a * w := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (div_nonneg ha.le hC.le),
            div_mul_cancel₀ a hC.ne']
        _ ≤ _ := hfloor i hi
    have hcount := Submission.Obl.k4_quadratic_finite_greedy_cover.card_le_inv_relative_floor
      μ U E S (div_pos ha hC) (ENNReal.toReal_pos hUpos.ne' hUfin) hUfin hE hdisj hf
    simpa only [inv_div] using hcount
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
    simp only [Finset.card_empty, Nat.cast_zero]
    exact div_nonneg hC.le ha.le

/-- The native source Jacobian and original palette factor both cancel
against the stored marginal floor. -/
theorem projected_source_list_count
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (μ : Measure Ω) (U : Set Ω) (E : ι → Set Ω) (S : Finset ι)
    {N d fine coarse J K H : ℝ}
    (hN : 0 < N) (hJ : 0 < J) (hK : 0 < K) (hH : 0 < H)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hwtop : w ≠ ⊤)
    (hcap : μ U ≤ ENNReal.ofReal (K * J * N ^ (-d * coarse)) * w)
    (hE : ∀ i ∈ S, MeasurableSet (E i) ∧ E i ⊆ U)
    (hdisj : (S : Set ι).PairwiseDisjoint E)
    (hfloor : ∀ i ∈ S, ENNReal.ofReal (J * N ^ (-d * fine) / H) * w ≤ μ (E i)) :
    (S.card : ℝ) ≤ K * H * N ^ (d * (fine - coarse)) := by
  have hc := card_le_from_original_witnesses μ U E S
    (by positivity : 0 < J * N ^ (-d * fine) / H)
    (by positivity : 0 < K * J * N ^ (-d * coarse)) w hw hwtop hcap hE hdisj hfloor
  apply hc.trans_eq
  calc
    _ = K * H * (N ^ (-d * coarse) / N ^ (-d * fine)) := by
      field_simp
    _ = _ := by
      rw [← Real.rpow_sub hN]
      congr 2
      ring

end
end Submission.Obl.k4_general_wide_layer_offset_comparison
