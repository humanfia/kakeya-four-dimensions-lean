-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonflat_factored_improvement.GridGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Grid

namespace WangZahlLot.Obl.wz_nonflat_factored_improvement

open MeasureTheory Set Metric

theorem tube_gridCell_volume {b : ℝ} (hb : 0 < b) (δ : ℝ) (x v : Space)
    (hv : ‖v‖ = 1) (z : Fin 3 → ℤ) :
    volume (tube δ x v ∩ gridCell b z) ≤ ENNReal.ofReal (16 * b * δ ^ 2) := by
  rcases (tube δ x v ∩ gridCell b z).eq_empty_or_nonempty with he | ⟨p, hpT, hpC⟩
  · simp [he]
  obtain ⟨u, hu⟩ := WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.exists_basis_first hv
  have hperp (i : Fin 3) (hi : i ≠ 0) : inner ℝ (u i) v = 0 := by
    rw [← hu, orthonormal_iff_ite.mp u.orthonormal]
    simp [hi]
  have htrans (i : Fin 3) (hi : i ≠ 0) (q : Space) (hq : q ∈ tube δ x v) :
      |inner ℝ (u i) (q - x)| ≤ δ := by
    have h := WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.tube_subset_slab
      (u.norm_eq_one i) (hperp i hi) x δ hq
    simpa only [Set.mem_ofPred_eq, inner_sub_right] using h
  have h := WangZahlLot.Obl.wz_transverse_cell_weighted_cover.volume_le_of_coords
    u.orthonormal ![p, x, x] ![2 * b, δ, δ] (tube δ x v ∩ gridCell b z) (by
      intro q hq i
      fin_cases i
      · change |inner ℝ (u 0) (q - p)| ≤ 2 * b
        have hd := gridCell_dist_lt hb hq.2 hpC
        have hn := abs_real_inner_le_norm (u 0) (q - p)
        rw [u.norm_eq_one, one_mul, ← dist_eq_norm] at hn
        exact hn.trans hd.le
      · exact htrans 1 (by decide) q hq.1
      · exact htrans 2 (by decide) q hq.1)
  change volume _ ≤ ENNReal.ofReal (8 * (2 * b * δ * δ)) at h
  convert h using 1
  congr 1
  ring

end WangZahlLot.Obl.wz_nonflat_factored_improvement
