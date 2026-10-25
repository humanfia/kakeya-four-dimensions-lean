-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.ExactContainment.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.Endpoints

-- Copied from session x0318 (x0210 lineage) (o070 branch, commit 7b9811e, file ExactContainment.lean), namespace renamed.
namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open Set

/-- Controlling the midpoint and the full unit-axis vector gives exact unit-length
containment.  No longitudinal enlargement is hidden in this criterion. -/
theorem tube_subset_of_center_axis_bound {δ ρ : ℝ} {x v z w : Space}
    (hbudget : δ + (‖center x v - center z w‖ + (1 / 2 : ℝ) * ‖v - w‖) ≤ ρ) :
    Tube δ x v ⊆ Tube ρ z w := by
  intro y hy
  obtain ⟨p, hp, hyp⟩ := Metric.mem_thickening_iff.mp hy
  rw [segment_eq_image'] at hp
  obtain ⟨t, ht, rfl⟩ := hp
  simp only [add_sub_cancel_left] at hyp
  apply Metric.mem_thickening_iff.mpr
  refine ⟨z + t • w, ?_, ?_⟩
  · rw [segment_eq_image']
    exact ⟨t, ht, by simp⟩
  · have ht' : |t - 1 / 2| ≤ (1 / 2 : ℝ) := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    have he : (x + t • v) - (z + t • w) =
        (center x v - center z w) + (t - 1 / 2) • (v - w) := by
      dsimp [center]
      module
    have hdist : dist (x + t • v) (z + t • w) ≤
        ‖center x v - center z w‖ + (1 / 2 : ℝ) * ‖v - w‖ := by
      rw [dist_eq_norm, he]
      calc
        _ ≤ ‖center x v - center z w‖ + ‖(t - 1 / 2) • (v - w)‖ := norm_add_le _ _
        _ = ‖center x v - center z w‖ + |t - 1 / 2| * ‖v - w‖ := by
          rw [norm_smul, Real.norm_eq_abs]
        _ ≤ _ := by gcongr
    exact (dist_triangle y (x + t • v) (z + t • w)).trans_lt (by linarith)

/-- A midpoint-axis ball of radius r is covered by the corresponding tube of
radius delta+2r, with its original unit segment retained. -/
theorem tube_subset_of_center_axis_near {δ r : ℝ} {x v z w : Space}
    (hc : ‖center x v - center z w‖ ≤ r) (hv : ‖v - w‖ ≤ 2 * r) :
    Tube δ x v ⊆ Tube (δ + 2 * r) z w := by
  apply tube_subset_of_center_axis_bound
  linarith

lemma tube_reverse (δ : ℝ) (x v : Space) : Tube δ (x + v) (-v) = Tube δ x v := by
  unfold Tube
  rw [add_neg_cancel_right, segment_symm]

/-- The same criterion may choose either orientation of the parent axis. -/
theorem tube_subset_of_center_unoriented_axis_near {δ r : ℝ} {x v z w : Space}
    (hc : ‖center x v - center z w‖ ≤ r)
    (hv : ‖v - w‖ ≤ 2 * r ∨ ‖v + w‖ ≤ 2 * r) :
    Tube δ x v ⊆ Tube (δ + 2 * r) z w := by
  rcases hv with hv | hv
  · exact tube_subset_of_center_axis_near hc hv
  · have hcenter : center (z + w) (-w) = center z w := by
      dsimp [center]
      module
    rw [← tube_reverse (δ + 2 * r) z w]
    apply tube_subset_of_center_axis_near
    · simpa only [hcenter] using hc
    · simpa only [sub_neg_eq_add] using hv

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
