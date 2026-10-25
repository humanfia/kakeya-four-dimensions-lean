import Submission.Obl.k4_finite_row_graph_assembly.Selected

-- Relocated from this LOT tree, o072, x0245/3b29ff1,
-- Submission/Obl/k4_row_incidence_graph_construction/GraphBounds.lean.

namespace Submission.Obl.k4_finite_row_graph_assembly

noncomputable def realSumIndex (h k : ℝ) (e : RealEdge) : ℤ × ℤ :=
  (⌊(e.1.1 + k * e.2.1) / h⌋, ⌊(e.1.2 + k * e.2.2) / h⌋)

namespace SelectedCells

variable {h K R s : ℝ} {f : FiniteIncidenceData h K R s} (c : SelectedCells f)

theorem left_grid (a : ℝ × ℝ) (ha : a ∈ c.left) :
    ∃ i j : ℤ, a = (h * i, h * j) := by
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp ha
  exact ⟨(roundedProjection (f.velocity c.first) p).1,
    (roundedProjection (f.velocity c.first) p).2, rfl⟩

theorem right_grid (a : ℝ × ℝ) (ha : a ∈ c.right) :
    ∃ i j : ℤ, a = (h * i, h * j) := by
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp ha
  exact ⟨(roundedProjection (f.velocity c.second) p).1,
    (roundedProjection (f.velocity c.second) p).2, rfl⟩

theorem left_bound (hh : 0 ≤ h) (a : ℝ × ℝ) (ha : a ∈ c.left) :
    |a.1| ≤ K + K ^ 2 + h ∧ |a.2| ≤ K + K ^ 2 + h := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
  exact projection_bound hh (f.velocity_bound c.first c.first_mem)
    (f.center_bound p (Finset.mem_filter.mp hp).1)

theorem right_bound (hh : 0 ≤ h) (a : ℝ × ℝ) (ha : a ∈ c.right) :
    |a.1| ≤ K + K ^ 2 + h ∧ |a.2| ≤ K + K ^ 2 + h := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
  exact projection_bound hh (f.velocity_bound c.second c.second_mem)
    (f.center_bound p (Finset.mem_filter.mp hp).1)

theorem realSumIndex_edgeMap (hh : h ≠ 0) (d : ℤ) (p : Point) :
    realSumIndex h (ratio (f.velocity c.first) (f.velocity c.second) (f.velocity d))
      (c.edgeMap p) = sumIndex (f.velocity c.first) (f.velocity c.second) (f.velocity d) p := by
  apply Prod.ext <;>
    simp only [realSumIndex, edgeMap, meshEdge, meshVertex, projectionPair, sumIndex]
  · congr 1
    field_simp
  · congr 1
    field_simp

theorem sum_card (hh : 0 < h) (hR : 2 ≤ R) (hKR : K ≤ R) (hK : 0 ≤ K)
    (d : ℤ) (hd : d ∈ c.directions) :
    (((c.graph d).image (realSumIndex h
      (ratio (f.velocity c.first) (f.velocity c.second) (f.velocity d)))).card : ℝ) ≤
      K * (10 + 6 * R ^ 3) ^ 2 / h := by
  classical
  have hRpos : 0 < R := by linarith
  have hden : f.velocity c.second - f.velocity d ≠ 0 := by
    apply sub_ne_zero.mpr
    exact (sub_ne_zero.mp (abs_pos.mp
      ((one_div_pos.mpr hRpos).trans_le (c.separated d hd).2))).symm
  have hb := ratio_bounds hR
    ((f.velocity_bound c.first c.first_mem).trans hKR)
    ((f.velocity_bound c.second c.second_mem).trans hKR)
    ((f.velocity_bound d (c.directions_subset hd)).trans hKR)
    (c.separated d hd).1 (by simpa only [abs_sub_comm] using (c.separated d hd).2)
  have hcover : (((c.cells d).image (roundedProjection (f.velocity d))).card : ℝ) ≤ K / h := by
    apply (Nat.cast_le.mpr (Finset.card_le_card
      (Finset.image_subset_image (show c.cells d ⊆ f.points.filter (fun p => 0 < f.mass p d) from
        fun p hp => Finset.mem_filter.mpr
          ⟨c.cells_subset d hd hp, c.third_positive d hd p hp⟩)))).trans
        (f.projection_cover d (c.directions_subset hd))
  have heq : (c.graph d).image (realSumIndex h
      (ratio (f.velocity c.first) (f.velocity c.second) (f.velocity d))) =
      (c.cells d).image (sumIndex (f.velocity c.first) (f.velocity c.second) (f.velocity d)) := by
    dsimp only [graph]
    rw [Finset.image_image]
    apply Finset.image_congr
    intro p hp
    exact c.realSumIndex_edgeMap hh.ne' d p
  rw [heq]
  calc
    _ ≤ (((c.cells d).image (roundedProjection (f.velocity d))).card : ℝ) *
        (2 * (4 + 2 * |ratio (f.velocity c.first) (f.velocity c.second) (f.velocity d)| +
          |projectionFactor (f.velocity c.first) (f.velocity c.second) (f.velocity d)|) + 2) ^ 2 :=
      sumIndex_card _ hden
    _ ≤ (K / h) * (10 + 6 * R ^ 3) ^ 2 := by
      apply mul_le_mul hcover _ (by positivity) (div_nonneg hK hh.le)
      apply pow_le_pow_left₀ (by positivity)
      nlinarith [hb.2.1, hb.2.2]
    _ = _ := by ring

theorem rectangle_card (hh : 0 < h) (hK : 0 ≤ K) (hR : 1 ≤ R) (hKR : K ≤ R)
    (d : ℤ) (hd : d ∈ c.directions) (x y : ℝ) :
    (((c.graph d).filter (fun e => e.1.1 ∈ Set.Ico x (x + h) ∧
      e.2.1 ∈ Set.Ico y (y + h))).card : ℝ) ≤ (6 * R ^ 2 + 2) ^ 2 * K := by
  classical
  dsimp only [graph]
  rw [Finset.filter_image]
  apply (Nat.cast_le.mpr (Finset.card_image_le)).trans
  apply (Nat.cast_le.mpr (Finset.card_le_card
    (Finset.filter_subset_filter _ (c.cells_subset d hd)))).trans
  exact rectangle_points_card f.points hh hK hR
    ((f.velocity_bound c.first c.first_mem).trans hKR)
    ((f.velocity_bound c.second c.second_mem).trans hKR) c.separation f.position_fiber x y

theorem endpoint_lower_bounds (hh : 0 < h) (hK : 0 < K) (hR : 1 ≤ R) (hKR : K ≤ R) :
    1 / (K * graphDenominator K R * h) ≤ (c.left.card : ℝ) ∧
    1 / (K * graphDenominator K R * h) ≤ (c.right.card : ℝ) := by
  obtain ⟨d, hd⟩ := c.directions_nonempty
  have hG := c.graph_card hh hR hKR hK d hd
  have hsub : ((c.graph d).card : ℝ) ≤ (c.left.card : ℝ) * c.right.card := by
    exact_mod_cast (Finset.card_le_card (c.graph_subset d hd)).trans_eq
      (Finset.card_product _ _)
  have hleft := c.left_card hh.ne'
  have hright := c.right_card hh.ne'
  have heq : (1 / (graphDenominator K R * h ^ 2)) / (K / h) =
      1 / (K * graphDenominator K R * h) := by field_simp
  constructor
  · rw [← heq, div_le_iff₀ (div_pos hK hh)]
    exact hG.trans (hsub.trans (mul_le_mul_of_nonneg_left hright (Nat.cast_nonneg _)))
  · rw [← heq, div_le_iff₀ (div_pos hK hh)]
    exact hG.trans (hsub.trans (by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hleft (Nat.cast_nonneg c.right.card)))

end SelectedCells
end Submission.Obl.k4_finite_row_graph_assembly
