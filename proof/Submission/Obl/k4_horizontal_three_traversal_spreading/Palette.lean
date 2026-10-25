import Submission.Obl.k4_horizontal_three_traversal_spreading.Approximation

namespace Submission.Obl.k4_horizontal_three_traversal_spreading

open Set MeasureTheory Finset
open scoped ENNReal
open Discretize

noncomputable section
namespace Law

variable {α : Type} [MeasurableSpace α] (D : Law α)

theorem measurableSet_palette_cell (z : ℤ) : MeasurableSet {w : ℝ | ⌊w / D.h⌋ = z} :=
  (Int.measurable_floor.comp (measurable_id.div_const D.h)) (measurableSet_singleton z)

theorem palette_cells_disjoint (z z' : D.palSet) (hne : z ≠ z') :
    Disjoint {w : ℝ | ⌊w / D.h⌋ = z.val} {w : ℝ | ⌊w / D.h⌋ = z'.val} := by
  rw [Set.disjoint_left]
  intro w hw hw'
  exact hne (Subtype.ext (hw.symm.trans hw'))

theorem palette_sum_le_one (hD : D.Valid) : ∑ z : D.palSet, D.palMass z.val ≤ 1 := by
  letI := hD.prob_π
  unfold palMass
  rw [sum_toReal_measure_eq D.π Finset.univ _
    (fun z => D.measurableSet_palette_cell z.val)
    (fun z _ z' _ hne => D.palette_cells_disjoint z z' hne)]
  exact (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.subset_univ _))).trans_eq
    (by simp)

/-- The fine palette bins near a control lie in one original palette interval. -/
theorem palette_interval (hD : D.Valid) {K V : ℝ} (hK : 0 < K)
    (hfine : D.h ≤ K⁻¹) (hV : 0 ≤ V)
    (hcap : ∀ v : ℝ, D.π (Icc (v - 2 / K) (v + 2 / K)) ≤ ENNReal.ofReal V) (v : ℝ) :
    (∑ z ∈ Finset.univ.filter (fun z : D.palSet => |D.velocity z - v| ≤ K⁻¹),
      D.palMass z.val) ≤ V := by
  letI := hD.prob_π
  unfold palMass
  rw [sum_toReal_measure_eq D.π _ _ (fun z => D.measurableSet_palette_cell z.val)
    (fun z _ z' _ hne => D.palette_cells_disjoint z z' hne)]
  have hsub : (⋃ z ∈ Finset.univ.filter (fun z : D.palSet => |D.velocity z - v| ≤ K⁻¹),
      {w : ℝ | ⌊w / D.h⌋ = z.val}) ⊆ Icc (v - 2 / K) (v + 2 / K) := by
    intro w hw
    simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and,
      exists_prop] at hw
    obtain ⟨z, hz, hw⟩ := hw
    have hr := abs_sub_floor_center (x := w) hD.h_pos
    rw [hw] at hr
    have ha : |w - v| ≤ 2 / K := by
      calc
        |w - v| ≤ |w - D.velocity z| + |D.velocity z - v| := abs_sub_le _ _ _
        _ ≤ D.h / 2 + K⁻¹ := add_le_add hr hz
        _ ≤ 2 / K := by rw [div_eq_mul_inv (2 : ℝ) K]; linarith [inv_pos.mpr hK]
    exact ⟨by linarith [(abs_le.mp ha).1], by linarith [(abs_le.mp ha).2]⟩
  have hle := (measure_mono hsub).trans (hcap v)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  simpa only [ENNReal.toReal_ofReal hV] using hreal

end Law
end
end Submission.Obl.k4_horizontal_three_traversal_spreading
