-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_factored_improvement.BodyNormalization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_factored_improvement.Width
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.QuantitativeNormalization

namespace WangZahlLot.Obl.wz_flat_factored_improvement

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_regular_transverse_affine_cells
  (orthogonalBox exists_comparable_orthogonal_box volume_orthogonalBox
    prism prism_eq_orthogonalBox orthogonalBox_subset_ball volume_prism
    ball_subset_affine_preimage)

/-- Normalize a general convex body to a prism, preserving the original middle width.
The source only needs an interior ball, a fixed lower diameter and a wide section. -/
theorem normalized_convex_prism {U : Set Space} (hUc : IsCompact U)
    (hUconv : Convex ℝ U) {x : Space} {δ b₀ S : ℝ}
    (hδ : 0 < δ) (hSlarge : 1000000000 ≤ S)
    (hball : ball x δ ⊆ U)
    (hdiam : ∃ p ∈ U, ∃ q ∈ U, (1 / 16 : ℝ) ≤ dist p q)
    (hwide : WideSection U b₀) (f : Space ≃ᵃ[ℝ] Space)
    (hsmall : f ⁻¹' U ⊆ closedBall (0 : Space) (2 / S))
    (hLip : ∀ p q, dist (f p) (f q) ≤ (6 * S) * dist p q) :
    ∃ (a b : ℝ) (u : OrthonormalBasis (Fin 3) ℝ Space),
      δ / (12 * S) ≤ a ∧ 0 < a ∧ a ≤ b ∧ b₀ / (24 * S) ≤ b ∧
      b ≤ 24 / S ∧ b ≤ 1 / 1000000 ∧
      prism a b (f.symm x) u ⊆ ball (0 : Space) (1 / 100) ∧
      U ⊆ f '' prism a b (f.symm x) u ∧
      volume (prism a b (f.symm x) u) ≤
        ENNReal.ofReal (2000 * S) * volume (f ⁻¹' U) := by
  have hS : 0 < S := by linarith
  have hL : 0 < 6 * S := by positivity
  have hpreball : ball (f.symm x) (δ / (6 * S)) ⊆ f ⁻¹' U :=
    (ball_subset_affine_preimage f hL hLip x).trans (preimage_mono hball)
  obtain ⟨u, w, hw, horder, hwidth, hbox, hvol⟩ := exists_comparable_orthogonal_box
    (f.toContinuousAffineEquiv.toHomeomorph.isCompact_preimage.mpr hUc)
    (hUconv.affine_preimage f.toAffineMap) (by positivity : 0 < δ / (6 * S)) hpreball hsmall
  have hmid := middle_width_lower (hwide.preimage f hL hLip) w (f.symm x) u
    (fun i => (hw i).le) horder hbox
  have hmiddle : b₀ / (24 * S) ≤ w 1 := by
    rw [div_le_iff₀ (by positivity : 0 < 24 * S)]
    have hh := (div_le_iff₀ hL).mp hmid
    nlinarith only [hh]
  have hlong : 1 ≤ 384 * S * w 0 := by
    obtain ⟨p, hp, q, hq, hd⟩ := hdiam
    have hp' := hbox (show f.symm p ∈ f ⁻¹' U by simpa)
    have hq' := hbox (show f.symm q ∈ f ⁻¹' U by simpa)
    have hc (i : Fin 3) : |u.repr (f.symm p - f.symm q) i| ≤ 2 * w 0 := by
      rw [OrthonormalBasis.repr_apply_apply]
      have he : f.symm p - f.symm q =
          (f.symm p - f.symm x) - (f.symm q - f.symm x) := by abel
      rw [he, inner_sub_right]
      exact (abs_sub _ _).trans (by linarith [hp' i, hq' i, horder (Fin.zero_le i)])
    have hn := WangZahlLot.Obl.wz_balanced_cluster_cover.norm_le_of_forall_abs_le
      (mul_nonneg (by norm_num) (hw 0).le) hc
    rw [u.repr.norm_map] at hn
    have hh := hLip (f.symm p) (f.symm q)
    simp only [f.apply_symm_apply, dist_eq_norm] at hh
    rw [dist_eq_norm] at hd
    nlinarith only [hd, hh, mul_le_mul_of_nonneg_left hn hL.le]
  let v := u.reindex (Fin.revPerm : Equiv.Perm (Fin 3))
  have hv0 : v 0 = u 2 := by simp [v, OrthonormalBasis.reindex_apply, Fin.revPerm]
  have hv1 : v 1 = u 1 := by simp [v, OrthonormalBasis.reindex_apply, Fin.revPerm]
  have hv2 : v 2 = u 0 := by simp [v, OrthonormalBasis.reindex_apply, Fin.revPerm]
  have hupper (i : Fin 3) : w i ≤ 24 / S := by
    calc w i ≤ 12 * (2 / S) := (hwidth i).2
      _ = _ := by ring
  have hshort : 24 / S ≤ (1 / 1000000 : ℝ) := by
    rw [div_le_iff₀ hS]
    linarith
  have hpre : f ⁻¹' U ⊆ prism (w 2) (w 1) (f.symm x) v := by
    intro p hp
    have hh := hbox hp
    change |inner ℝ (v 0) (p - f.symm x)| ≤ w 2 ∧
      |inner ℝ (v 1) (p - f.symm x)| ≤ w 1 ∧
      |inner ℝ (v 2) (p - f.symm x)| ≤ 1 / 1000
    rw [hv0, hv1, hv2]
    exact ⟨hh 2, hh 1, (hh 0).trans ((hupper 0).trans (hshort.trans (by norm_num)))⟩
  have hcentral : ‖f.symm x‖ ≤ 2 / S := by
    have hx := hball (mem_ball_self hδ)
    have hfx : f.symm x ∈ f ⁻¹' U := by simpa
    simpa using hsmall hfx
  have hPsmall : prism (w 2) (w 1) (f.symm x) v ⊆ ball (0 : Space) (1 / 100) := by
    rw [prism_eq_orthogonalBox]
    apply orthogonalBox_subset_ball _ _ _ (by norm_num : (0 : ℝ) ≤ 1 / 1000)
    · intro i
      fin_cases i
      · exact (hupper 2).trans (hshort.trans (by norm_num))
      · exact (hupper 1).trans (hshort.trans (by norm_num))
      · exact le_rfl
    · have hh : 2 / S ≤ (1 / 1000000 : ℝ) := by
        rw [div_le_iff₀ hS]
        linarith
      linarith
  refine ⟨w 2, w 1, v, ?_, hw 2, horder (by decide : (1 : Fin 3) ≤ 2),
    hmiddle, hupper 1, (hupper 1).trans hshort, hPsmall, ?_, ?_⟩
  · convert (hwidth 2).1 using 1 <;> ring
  · intro p hp
    exact ⟨f.symm p, hpre (by simpa), f.apply_symm_apply p⟩
  · have hboxvol : volume (orthogonalBox w (f.symm x) u) ≤ 4096 * volume (f ⁻¹' U) := by
      calc
        _ = 4096 * (ENNReal.ofReal (1 / 4096 : ℝ) *
            volume (orthogonalBox w (f.symm x) u)) := by
          rw [← mul_assoc, ENNReal.ofReal_div_of_pos (by norm_num)]
          norm_num
          rw [ENNReal.mul_inv_cancel (by norm_num : (4096 : ℝ≥0∞) ≠ 0) (by norm_num), one_mul]
        _ ≤ _ := mul_le_mul' le_rfl hvol
    have hPvol : volume (prism (w 2) (w 1) (f.symm x) v) ≤
        ENNReal.ofReal (384 * S / 1000) * volume (orthogonalBox w (f.symm x) u) := by
      rw [volume_prism _ _ (hw 2).le (hw 1).le,
        volume_orthogonalBox _ (fun i => (hw i).le),
        ← ENNReal.ofReal_mul (by positivity), Fin.prod_univ_three]
      apply ENNReal.ofReal_le_ofReal
      have hh := mul_le_mul_of_nonneg_left hlong
        (show 0 ≤ 8 * w 2 * w 1 / 1000 from
          div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hw 2).le) (hw 1).le) (by norm_num))
      nlinarith only [hh, mul_nonneg (hw 2).le (hw 1).le]
    calc
      _ ≤ ENNReal.ofReal (384 * S / 1000) * (4096 * volume (f ⁻¹' U)) :=
        hPvol.trans (mul_le_mul' le_rfl hboxvol)
      _ = ENNReal.ofReal (1572864 * S / 1000) * volume (f ⁻¹' U) := by
        rw [← mul_assoc, ← ENNReal.ofReal_ofNat 4096,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring
      _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl

end WangZahlLot.Obl.wz_flat_factored_improvement
