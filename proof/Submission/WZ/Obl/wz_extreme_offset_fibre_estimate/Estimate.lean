-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extreme_offset_fibre_estimate.Estimate.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extreme_offset_fibre_estimate.Geometry

namespace WangZahlLot.Obl.wz_extreme_offset_fibre_estimate

open MeasureTheory Set Metric

noncomputable section

/-- The outer volume bound obtained by enclosing the projection in a measurable hull. -/
lemma shading_volume_le {δ : ℝ} (hδ : 0 < δ) {x v : Space}
    (hv : ‖v‖ = 1) (ht : (1 / 2 : ℝ) ≤ |v 2|)
    (hball : thickening δ (segment ℝ x (x + v)) ⊆ ball (0 : Space) 1)
    {Y E : Set Space} (hY : Y ⊆ thickening δ (segment ℝ x (x + v))) (hYE : Y ⊆ E)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hd : ∀ z ∈ Icc (-1 : ℝ) 1, |deriv f z| ≤ 2) (hoff : 2 + 6 / δ ≤ |f 0|) :
    volume Y ≤ volume ((fun p => (chart f p).1) '' E) * ENNReal.ofReal (δ ^ 2) := by
  let A : Set (ℝ × ℝ) := toMeasurable volume ((fun p => (chart f p).1) '' E)
  have hA : MeasurableSet A := measurableSet_toMeasurable _ _
  have hsub : Y ⊆ centeredChart f (axis x v) ⁻¹'
      (A ×ˢ Icc (-(δ ^ 2 / 2)) (δ ^ 2 / 2)) := by
    intro p hp
    constructor
    · exact subset_toMeasurable _ _ ⟨p, hYE hp, rfl⟩
    · exact abs_le.mp (centeredChart_fibre_bound hδ
        (slope_value_lower hf hd hoff (height_mem_Icc (hball (hY hp))))
        (tube_horizontal_width hv ht (hY hp)))
  calc
    volume Y ≤ volume (centeredChart f (axis x v) ⁻¹'
        (A ×ˢ Icc (-(δ ^ 2 / 2)) (δ ^ 2 / 2))) := measure_mono hsub
    _ = volume (A ×ˢ Icc (-(δ ^ 2 / 2)) (δ ^ 2 / 2)) :=
      (measurePreserving_centeredChart f (axis x v) hf.continuous.measurable
        (measurable_axis x v)).measure_preimage (hA.prod measurableSet_Icc).nullMeasurableSet
    _ = volume A * ENNReal.ofReal (δ ^ 2) := by
      rw [Measure.volume_eq_prod (ℝ × ℝ) ℝ, Measure.prod_prod, Real.volume_Icc]
      congr 2
      ring
    _ = volume ((fun p => (chart f p).1) '' E) * ENNReal.ofReal (δ ^ 2) := by
      rw [measure_toMeasurable]

lemma family_projection_estimate {η δ : ℝ} (hδ : 0 < δ)
    {n : ℕ} (hn : 0 < n) (x v : Fin n → Space) (Y : Fin n → Set Space)
    (hv : ∀ i, ‖v i‖ = 1) (ht : ∀ i, (1 / 2 : ℝ) ≤ |v i 2|)
    (hball : ∀ i, thickening δ (segment ℝ (x i) (x i + v i)) ⊆ ball (0 : Space) 1)
    (hY : ∀ i, Y i ⊆ thickening δ (segment ℝ (x i) (x i + v i)))
    (hmass : ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) ≤ ∑ i, volume (Y i))
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hd : ∀ z ∈ Icc (-1 : ℝ) 1, |deriv f z| ≤ 2) (hoff : 2 + 6 / δ ≤ |f 0|) :
    ENNReal.ofReal (δ ^ η) ≤ volume ((fun p => (chart f p).1) '' ⋃ i, Y i) := by
  have hpos : 0 < (n : ℝ) * δ ^ 2 := mul_pos (Nat.cast_pos.mpr hn) (sq_pos_of_pos hδ)
  apply (ENNReal.mul_le_mul_iff_left (ENNReal.ofReal_pos.mpr hpos).ne'
    ENNReal.ofReal_ne_top).mp
  calc
    ENNReal.ofReal (δ ^ η) * ENNReal.ofReal ((n : ℝ) * δ ^ 2) =
        ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le η), mul_assoc]
    _ ≤ ∑ i, volume (Y i) := hmass
    _ ≤ ∑ i : Fin n, volume ((fun p => (chart f p).1) '' ⋃ i, Y i) *
        ENNReal.ofReal (δ ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      exact shading_volume_le hδ (hv i) (ht i) (hball i) (hY i) (subset_iUnion Y i)
        hf hd hoff
    _ = volume ((fun p => (chart f p).1) '' ⋃ i, Y i) *
        ENNReal.ofReal ((n : ℝ) * δ ^ 2) := by
      simp [ENNReal.ofReal_mul (Nat.cast_nonneg n), nsmul_eq_mul, mul_comm, mul_assoc]

end

end WangZahlLot.Obl.wz_extreme_offset_fibre_estimate
