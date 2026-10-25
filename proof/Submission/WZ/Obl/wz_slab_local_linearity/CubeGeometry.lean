-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.CubeGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_slab_local_linearity.CubeVolume

namespace WangZahlLot.Obl.wz_slab_local_linearity

open Set Metric

lemma gridCube_dist_lt {ρ : ℝ} (hρ : 0 < ρ) {k : Fin 3 → ℤ} {p q : Space3}
    (hp : p ∈ gridCube ρ k) (hq : q ∈ gridCube ρ k) : dist p q < 2 * ρ := by
  rw [gridCube_eq_gridCell] at hp hq
  exact wz_nonflat_factored_improvement.gridCell_dist_lt hρ hp hq

lemma gridCube_subset_ball {ρ r : ℝ} (hρ : 0 < ρ) {k : Fin 3 → ℤ} {p : Space3}
    (hcorner : dist (gridCorner ρ k) p + 2 * ρ ≤ r) : gridCube ρ k ⊆ ball p r := by
  intro q hq
  have hdist := gridCube_dist_lt hρ hq (gridCorner_mem hρ k)
  have htri := dist_triangle q (gridCorner ρ k) p
  change dist q p < r
  linarith

/-- Centering the projections removes the large translation term when their
normal vectors change. -/
lemma centered_projection_error {u v p q : Space3} {L R : ℝ}
    (hL : ‖u - v‖ ≤ L) (hR : ‖q - p‖ ≤ R) :
    |inner ℝ u q - (inner ℝ v q + inner ℝ (u - v) p)| ≤ L * R := by
  have he : inner ℝ u q - (inner ℝ v q + inner ℝ (u - v) p) =
      inner ℝ (u - v) (q - p) := by
    simp only [inner_sub_left, inner_sub_right]
    ring
  rw [he]
  calc |inner ℝ (u - v) (q - p)| ≤ ‖u - v‖ * ‖q - p‖ := abs_real_inner_le_norm _ _
    _ ≤ L * R := mul_le_mul hL hR (norm_nonneg _) ((norm_nonneg _).trans hL)

end WangZahlLot.Obl.wz_slab_local_linearity
