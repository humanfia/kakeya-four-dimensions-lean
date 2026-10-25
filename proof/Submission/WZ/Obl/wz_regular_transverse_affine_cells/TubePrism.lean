-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.TubePrism.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.QuantitativeNormalization
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.TubeBodies

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

open Module MeasureTheory Set
open scoped ENNReal

/-- A normalized whole tube fits a prism of the required fixed long width, with
uniform volume loss and polynomially controlled short widths. -/
lemma normalized_tube_prism {δ S : ℝ} (hδ : 0 < δ) (hSlarge : 1000000000 ≤ S)
    (f : E ≃ᵃ[ℝ] E) (x v : E) (hv : ‖v‖ = 1)
    (htube : tube δ x v ⊆ Metric.ball (0 : E) 1)
    (hsmall : f ⁻¹' closedTube δ x v ⊆ Metric.closedBall (0 : E) (2 / S))
    (hLip : ∀ p q, dist (f p) (f q) ≤ (6 * S) * dist p q) :
    ∃ (a b : ℝ) (u : OrthonormalBasis (Fin 3) ℝ E),
      δ / (12 * S) ≤ a ∧ 0 < a ∧ a ≤ b ∧ b ≤ 24 / S ∧ b ≤ 1 / 1000000 ∧
      prism a b (f.symm x) u ⊆ Metric.ball (0 : E) (1 / 100) ∧
      tube δ x v ⊆ f '' prism a b (f.symm x) u ∧
      volume (prism a b (f.symm x) u) ≤ ENNReal.ofReal (100000 * S) *
        volume (f ⁻¹' closedTube δ x v) := by
  have hS : 0 < S := by linarith
  let U := f ⁻¹' closedTube δ x v
  have hUc : IsCompact U :=
    f.toContinuousAffineEquiv.toHomeomorph.isCompact_preimage.mpr (closedTube_compact htube)
  have hUconv : Convex ℝ U := (closedTube_convex δ x v).affine_preimage f.toAffineMap
  have hball : Metric.ball (f.symm x) (δ / (6 * S)) ⊆ U :=
    (ball_subset_affine_preimage f (by positivity : 0 < 6 * S) hLip x).trans
      (preimage_mono ((ball_subset_tube x v).trans (tube_subset_closedTube δ x v)))
  obtain ⟨u, w, hwpos, hwanti, hwidth, hcover, hvolume⟩ :=
    exists_comparable_orthogonal_box hUc hUconv (by positivity : 0 < δ / (6 * S)) hball hsmall
  have hwmax : ∀ i, w i ≤ 24 / S := by
    intro i
    calc w i ≤ 12 * (2 / S) := (hwidth i).2
      _ = 24 / S := by ring
  have hshort : 24 / S ≤ (1 / 1000000 : ℝ) := by
    rw [div_le_iff₀ hS]
    linarith
  have hlong : 1 ≤ 12 * S * w 0 := by
    let q := f.symm (x + v)
    have hqU : q ∈ U := by simpa only [U, q, mem_preimage, f.apply_symm_apply] using (closedTube_endpoints hδ x v).2
    have hcoords : ∀ i, |u.repr (q - f.symm x) i| ≤ w 0 := by
      intro i
      rw [OrthonormalBasis.repr_apply_apply]
      exact (hcover hqU i).trans (hwanti (Fin.zero_le i))
    have hnorm := WangZahlLot.Obl.wz_balanced_cluster_cover.norm_le_of_forall_abs_le
      (hwpos 0).le hcoords
    rw [u.repr.norm_map] at hnorm
    have hdist := hLip q (f.symm x)
    have hleft : dist (f q) (f (f.symm x)) = 1 := by
      simp [q, dist_eq_norm, hv]
    rw [hleft, dist_eq_norm] at hdist
    nlinarith [mul_le_mul_of_nonneg_left hnorm (by positivity : 0 ≤ 6 * S)]
  let u' := u.reindex (Fin.revPerm : Equiv.Perm (Fin 3))
  have hu0 : u' 0 = u 2 := by simp [u', OrthonormalBasis.reindex_apply, Fin.revPerm]
  have hu1 : u' 1 = u 1 := by simp [u', OrthonormalBasis.reindex_apply, Fin.revPerm]
  have hu2 : u' 2 = u 0 := by simp [u', OrthonormalBasis.reindex_apply, Fin.revPerm]
  have hPcover : U ⊆ prism (w 2) (w 1) (f.symm x) u' := by
    intro p hp
    change |inner ℝ (u' 0) (p - f.symm x)| ≤ w 2 ∧
      |inner ℝ (u' 1) (p - f.symm x)| ≤ w 1 ∧
      |inner ℝ (u' 2) (p - f.symm x)| ≤ 1 / 1000
    rw [hu0, hu1, hu2]
    exact ⟨hcover hp 2, hcover hp 1,
      (hcover hp 0).trans ((hwmax 0).trans (hshort.trans (by norm_num)))⟩
  have hxsmall : ‖f.symm x‖ ≤ 2 / S := by
    have hxU : f.symm x ∈ U := by simpa only [U, mem_preimage, f.apply_symm_apply] using (closedTube_endpoints hδ x v).1
    simpa using hsmall hxU
  have hPx : prism (w 2) (w 1) (f.symm x) u' ⊆ Metric.ball (0 : E) (1 / 100) := by
    rw [prism_eq_orthogonalBox]
    apply orthogonalBox_subset_ball _ _ _ (by norm_num : (0 : ℝ) ≤ 1 / 1000)
    · intro i
      fin_cases i
      · exact (hwmax 2).trans (hshort.trans (by norm_num))
      · exact (hwmax 1).trans (hshort.trans (by norm_num))
      · exact le_rfl
    · have hxbound : 2 / S ≤ (1 / 1000000 : ℝ) := by
        rw [div_le_iff₀ hS]
        linarith
      linarith
  refine ⟨w 2, w 1, u', ?_, hwpos 2, hwanti (by decide : (1 : Fin 3) ≤ 2),
    hwmax 1, (hwmax 1).trans hshort, hPx, ?_, ?_⟩
  · have he : δ / (12 * S) = (δ / (6 * S)) / 2 := by ring
    rw [he]
    exact (hwidth 2).1
  · intro p hp
    exact ⟨f.symm p, hPcover (by simpa [U] using tube_subset_closedTube δ x v hp), f.apply_symm_apply p⟩
  · have hPvol : volume (prism (w 2) (w 1) (f.symm x) u') ≤
        ENNReal.ofReal (12 * S) * volume (orthogonalBox w (f.symm x) u) := by
      rw [volume_prism _ _ (hwpos 2).le (hwpos 1).le, volume_orthogonalBox _ (fun i => (hwpos i).le),
        ← ENNReal.ofReal_mul (by positivity), Fin.prod_univ_three]
      apply ENNReal.ofReal_le_ofReal
      have hp : 0 ≤ 8 * w 2 * w 1 :=
        mul_nonneg (mul_nonneg (by norm_num) (hwpos 2).le) (hwpos 1).le
      calc 8 * w 2 * w 1 / 1000 ≤ 8 * w 2 * w 1 := div_le_self hp (by norm_num)
        _ ≤ (8 * w 2 * w 1) * (12 * S * w 0) := by
          nlinarith [mul_le_mul_of_nonneg_left hlong hp]
        _ = _ := by ring
    have hboxvol : volume (orthogonalBox w (f.symm x) u) ≤ 4096 * volume U := by
      calc volume (orthogonalBox w (f.symm x) u)
          = 4096 * (ENNReal.ofReal (1 / 4096 : ℝ) * volume (orthogonalBox w (f.symm x) u)) := by
            rw [← mul_assoc, ENNReal.ofReal_div_of_pos (by norm_num)]
            norm_num
            rw [ENNReal.mul_inv_cancel (by norm_num : (4096 : ℝ≥0∞) ≠ 0) (by norm_num), one_mul]
        _ ≤ 4096 * volume U := mul_le_mul_right hvolume _
    calc volume (prism (w 2) (w 1) (f.symm x) u')
        ≤ ENNReal.ofReal (12 * S) * volume (orthogonalBox w (f.symm x) u) := hPvol
      _ ≤ ENNReal.ofReal (12 * S) * (4096 * volume U) := mul_le_mul_right hboxvol _
      _ = ENNReal.ofReal (49152 * S) * volume U := by
        rw [← mul_assoc, ← ENNReal.ofReal_ofNat 4096, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring
      _ ≤ ENNReal.ofReal (100000 * S) * volume U :=
        mul_le_mul_left (ENNReal.ofReal_le_ofReal (by linarith)) _

end WangZahlLot.Obl.wz_regular_transverse_affine_cells
