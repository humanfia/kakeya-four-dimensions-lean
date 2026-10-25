import Submission.Obl.k4_general_wide_layer_offset_comparison.ProjectedSliceCellCaps
import Submission.Obl.k4_general_wide_layer_offset_comparison.MatchingMeshCoupling

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/ProjectedSliceDensities.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- Common density constant for both actual projected colors. The exact
physical Jacobian and original palette are in the separate layer priors. -/
def projectedComparisonDensity (k : ℕ) (H : ℝ) : ℝ :=
  34406400 * p.K k ^ 2 * H ^ p.d

end Parent

namespace ProjectedLayer

variable {α : Type} [MeasurableSpace α]

/-- The factor four of the matching dummy coordinate and the two chart
scales are fixed constants. Original layer and palette weights are unchanged. -/
theorem comparison_density_factor (A : ProjectedLayer α) (p : Parent α) (hbase : p.Basic)
    {k : ℕ} {s m H h b : ℝ} (hN : 0 < p.N k) (hH : 0 ≤ H)
    (hh : 0 < h) (hb : 0 < b)
    {D : Fin A.count → Finset (ℤ × ℤ × ℤ)} (e : SliceIndex D)
    (hπ : 0 < p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = A.tag e.1 0}) :
    (4 : ℝ≥0∞) *
      (ENNReal.ofReal (8400 * p.K k ^ 2 * p.N k ^ (-m) *
        (32 * h) * (32 * b) * (H * p.N k ^ (-s)) ^ p.d) *
        p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = A.tag e.1 0}) =
      ENNReal.ofReal (p.projectedComparisonDensity k H *
        p.comparisonPrior k s m h b (some (A.sliceComparisonCode e))) := by
  letI := (hbase k).2.2.1
  have hn := Real.rpow_pos_of_pos hN (-m)
  have ha := Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hN (-s)) p.d
  have hC : 0 ≤ p.projectedComparisonDensity k H := by
    dsimp [Parent.projectedComparisonDensity]
    positivity
  have hW : ENNReal.ofReal (h * b) * A.unscaledWeight p k s m e.1 ≠ ⊤ := by
    unfold unscaledWeight
    finiteness
  dsimp only [unscaledWeight] at hW
  rw [A.comparisonPrior_slice_eq p hbase hN hh hb e hπ]
  unfold slicedWeight unscaledWeight
  rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_toReal hW]
  calc
    _ = ENNReal.ofReal (4 *
          (8400 * p.K k ^ 2 * p.N k ^ (-m) * (32 * h) * (32 * b) *
            (H * p.N k ^ (-s)) ^ p.d)) *
          p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = A.tag e.1 0} := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
      ring
    _ = (ENNReal.ofReal (p.projectedComparisonDensity k H) * ENNReal.ofReal (h * b) *
          ENNReal.ofReal (p.N k ^ (-m) * (p.N k ^ (-s)) ^ p.d)) *
          p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = A.tag e.1 0} := by
      congr 1
      rw [← ENNReal.ofReal_mul hC,
        ← ENNReal.ofReal_mul (mul_nonneg hC (mul_nonneg hh.le hb.le))]
      congr 1
      rw [Real.mul_rpow hH (Real.rpow_nonneg hN.le _)]
      dsimp [Parent.projectedComparisonDensity]
      ring
    _ = _ := by ring

/-- Actual eventwise mesh ceilings give the selected original index/base
ceiling after smoothing, with the exact original comparison prior. -/
theorem activeSlice_matching_density (A : ProjectedLayer α) (p : Parent α) (hbase : p.Basic)
    {k : ℕ} {s m H h g b δ : ℝ} (hN : 0 < p.N k) (hH : 0 ≤ H)
    (hh : 0 < h) (hb : 0 < b) (hδ : 0 < δ)
    (D : Fin A.count → Finset (ℤ × ℤ × ℤ)) (σ : Measure (α × ℝ)) [IsFiniteMeasure σ]
    (hd : Pairwise (fun e f =>
      Disjoint (A.goodSliceEvent p k h g b D e) (A.goodSliceEvent p k h g b D f)))
    (hE : ∀ e, MeasurableSet (A.goodSliceEvent p k h g b D e))
    (Q : Finset (Fin 2 → ℤ)) (e : A.ActiveSlice p k h g b D σ)
    (hπ : 0 < p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = A.tag e.val.1 0})
    (hcap : ∀ cell ∈ Q,
      σ {ω | meshCode2 δ (p.normalizedDomainBase k h g b ω) = cell ∧
        ω ∈ A.goodSliceEvent p k h g b D e.val} ≤
        (ENNReal.ofReal (8400 * p.K k ^ 2 * p.N k ^ (-m) *
          (32 * h) * (32 * b) * (H * p.N k ^ (-s)) ^ p.d) *
          p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = A.tag e.val.1 0}) *
            ENNReal.ofReal (δ ^ 2))
    (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : MeasurableSet U) :
    matchingMeshCoupling σ (p.normalizedDomainBase k h g b) δ Q
      {z | A.selectedSlice p k h g b D σ z.1 = some e ∧ z.2 ∈ U} ≤
        ENNReal.ofReal (p.projectedComparisonDensity k H *
          p.comparisonPrior k s m h b (some (A.sliceComparisonCode e.val))) * volume U := by
  have heq : {z : (α × ℝ) × EuclideanSpace ℝ (Fin 3) |
      A.selectedSlice p k h g b D σ z.1 = some e ∧ z.2 ∈ U} =
      A.goodSliceEvent p k h g b D e.val ×ˢ U := by
    ext z
    exact and_congr (A.selectedSlice_some_iff p D σ hd z.1 e) Iff.rfl
  rw [heq]
  have hc := matchingMeshCoupling_density σ (p.normalizedDomainBase k h g b) hδ Q
    (A.goodSliceEvent p k h g b D e.val) (hE e.val) hcap U hU
  rwa [A.comparison_density_factor p hbase hN hH hh hb e.val hπ] at hc

end ProjectedLayer
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
