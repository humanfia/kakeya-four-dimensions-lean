-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.PacketContainment.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.CoarseNormals
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.OrthogonalBox

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open WangZahlLot.Obl.wz_flat_factored_improvement (Space diagonalMap_norm_le)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (unit)
open WangZahlLot.Obl.wz_regular_transverse_affine_cells (orthogonalBox)

lemma dualLinear_norm_le {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (p : Space) :
    ‖dualLinear θ p‖ ≤ ‖p‖ := by
  have hh : ‖dualLinear θ p‖ ≤ 1 * ‖p‖ := by
    apply diagonalMap_norm_le (by norm_num)
    intro j
    fin_cases j <;> simp [abs_of_pos hθ, hθ1]
  simpa only [one_mul] using hh

lemma norm_le_coarseLinear {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (p : Space) :
    ‖p‖ ≤ ‖coarseLinear θ p‖ := by
  have hh := dualLinear_norm_le hθ hθ1 (coarseLinear θ p)
  rwa [dual_coarse hθ] at hh

/-- A small angular cell and a small spatial cell in coarse coordinates
give the two transverse physical confinement scales, including the factor
`theta` in the short width. -/
theorem physical_packet_enclosure {θ a c s : ℝ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hc : 0 < c) (hs : 0 < s)
    (ha : a ≤ θ * s * c) (z z₀ ν : Space)
    (u : OrthonormalBasis (Fin 3) ℝ Space) (U : Set Space)
    (hD0 : ‖dualLinear θ (u 0)‖ ≤ 25 * θ)
    (hD1 : ‖dualLinear θ (u 1)‖ ≤ 25 * θ)
    (hangle : ‖ν - unit (dualLinear θ (u 0))‖ ≤ s)
    (hcenter : ‖coarseLinear θ (z - z₀)‖ ≤ c / 100)
    (hshortcenter : |inner ℝ (unit (dualLinear θ (u 0))) (coarseLinear θ (z - z₀))| ≤ s * c / 100)
    (hnorm : ∀ p ∈ U, ‖p - z‖ ≤ c)
    (hcoarse : ∀ p ∈ U, ‖coarseLinear θ (p - z)‖ ≤ 25 * c)
    (hshort : ∀ p ∈ U, |inner ℝ ν (coarseLinear θ (p - z))| ≤ a / θ) :
    U ⊆ orthogonalBox ![2500 * θ * s * c, 2500 * θ * c, 2 * c] z₀ u := by
  have hu0 : u 0 ≠ 0 := by intro he; have hh := u.norm_eq_one 0; simp [he] at hh
  have hac : a / θ ≤ s * c := (div_le_iff₀ hθ).mpr (by nlinarith [ha])
  have hcenter' : ‖z - z₀‖ ≤ c / 100 :=
    (norm_le_coarseLinear hθ hθ1 _).trans hcenter
  intro p hp j
  have he : p - z₀ = (p - z) + (z - z₀) := by abel
  have hT : ‖coarseLinear θ (p - z₀)‖ ≤ 26 * c := by
    rw [he, map_add]
    exact (norm_add_le _ _).trans (by linarith [hcoarse p hp])
  have hn : ‖p - z₀‖ ≤ 2 * c := by
    rw [he]
    exact (norm_add_le _ _).trans (by linarith [hnorm p hp])
  have hν : |inner ℝ (unit (dualLinear θ (u 0))) (coarseLinear θ (p - z₀))| ≤
      27 * s * c := by
    have hh := abs_inner_le_projective (unit (dualLinear θ (u 0))) ν
      (coarseLinear θ (p - z))
    have hang : min ‖unit (dualLinear θ (u 0)) - ν‖
        ‖unit (dualLinear θ (u 0)) + ν‖ ≤ s := by
      apply (min_le_left _ _).trans
      simpa only [norm_sub_rev] using hangle
    have hm := mul_le_mul hang (hcoarse p hp) (norm_nonneg _) hs.le
    have hlocal : |inner ℝ (unit (dualLinear θ (u 0))) (coarseLinear θ (p - z))| ≤
        26 * s * c := by nlinarith [hshort p hp]
    rw [he, map_add, inner_add_right]
    apply (abs_add_le _ _).trans
    nlinarith [hshortcenter, mul_pos hs hc]
  fin_cases j
  · change |inner ℝ (u 0) (p - z₀)| ≤ 2500 * θ * s * c
    rw [normal_transport_coordinate hθ hθ1 hu0, abs_mul, abs_norm]
    have hh := mul_le_mul hD0 hν (abs_nonneg _) (by positivity : 0 ≤ 25 * θ)
    nlinarith [mul_pos (mul_pos hθ hs) hc]
  · change |inner ℝ (u 1) (p - z₀)| ≤ 2500 * θ * c
    rw [← dual_inner_coarse hθ]
    have hh := (abs_real_inner_le_norm (dualLinear θ (u 1)) (coarseLinear θ (p - z₀))).trans
      (mul_le_mul hD1 hT (norm_nonneg _) (by positivity : 0 ≤ 25 * θ))
    nlinarith [mul_pos hθ hc]
  · change |inner ℝ (u 2) (p - z₀)| ≤ 2 * c
    have hh := abs_real_inner_le_norm (u 2) (p - z₀)
    rw [u.norm_eq_one, one_mul] at hh
    exact hh.trans hn

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
