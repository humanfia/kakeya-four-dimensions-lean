-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_scales_gain.OuterNet.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_scales_gain.MiddleEstimate

namespace WangZahlLot.Obl.wz_separated_scales_gain

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_nonflat_factored_improvement

noncomputable def outerAffine : AffineEquiv ℝ Space Space :=
  (LinearEquiv.smulOfNeZero ℝ Space fineContraction (by norm_num)).toAffineEquiv

theorem outerAffine_apply (p : Space) : outerAffine p = fineContraction • p := rfl

theorem outerAffine_volume (U : Set Space) :
    volume (outerAffine '' U) = ENNReal.ofReal (fineContraction ^ 3) * volume U :=
  volume_smul_image (by norm_num) U

theorem outerAffine_dist (p q : Space) :
    dist (outerAffine p) (outerAffine q) = fineContraction * dist p q := by
  rw [outerAffine_apply, outerAffine_apply, dist_eq_norm, ← smul_sub, norm_smul,
    Real.norm_eq_abs, abs_of_pos (by norm_num : 0 < fineContraction), dist_eq_norm]

/-- Normalize a bounded family of parent tubes without assuming that the parents
are contained in the original unit ball. -/
theorem outer_tube_net {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {n : ℕ} (hn : 0 < n) (x v : Fin n → Space)
    (hv : ∀ i, ‖v i‖ = 1) (hball : ∀ i, tube δ (x i) (v i) ⊆ ball (0 : Space) 5)
    (hover : ∀ i j, i ≠ j → volume (tube δ (x i) (v i) ∩ tube δ (x j) (v j)) ≤
      (1 / 2 : ENNReal) * volume (tube δ (x i) (v i))) :
    ∃ (M : ℕ) (j : Fin M → Fin n) (z w : Fin M → Space),
      0 < M ∧ Function.Injective j ∧ (∀ i, ‖w i‖ = 1) ∧
      (∀ i, tube (fineRadius δ 1) (z i) (w i) ⊆ unitBall) ∧
      (∀ i k, i ≠ k → volume (tube (fineRadius δ 1) (z i) (w i) ∩
        tube (fineRadius δ 1) (z k) (w k)) ≤
          (1 / 2 : ENNReal) * volume (tube (fineRadius δ 1) (z i) (w i))) ∧
      (∀ i, outerAffine '' tube δ (x (j i)) (v (j i)) ⊆
        tube (fineRadius δ 1) (z i) (w i)) ∧ retainedFraction * n ≤ M := by
  have hκ : 0 < fineContraction := by norm_num
  let c : Fin n → Space := fun i => outerAffine (x i + (1 / 2 : ℝ) • v i)
  have hc (i : Fin n) : ‖c i‖ < 1 / 100 := by
    have hm : x i + (1 / 2 : ℝ) • v i ∈ tube δ (x i) (v i) := by
      apply self_subset_thickening hδ
      rw [segment_eq_image']
      exact ⟨1 / 2, by norm_num, by simp⟩
    have hh := mem_ball_zero_iff.mp (hball i hm)
    dsimp [c]
    rw [outerAffine_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hκ]
    dsimp [fineContraction]
    linarith
  have hrad : fineContraction * δ ≤ 1 / 1000000 := by
    dsimp [fineContraction]
    linarith
  have hdata (i : Fin n) : ∃ u : Fin 3 → Space, Orthonormal ℝ u ∧
      outerAffine '' tube δ (x i) (v i) ⊆
        WangZahlLot.Obl.wz_transverse_cell_weighted_cover.prism
          (fineContraction * δ) (fineContraction * δ) (c i) u := by
    apply affine_tube_prism outerAffine hκ hrad (fun p q => (outerAffine_dist p q).le) (x i) (v i) (hv i)
    change ‖fineContraction • v i‖ ≤ 1 / 1000000
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hκ, hv i]
    norm_num
  choose u hu hprism using hdata
  have hpre (z w : Space) (hw : ‖w‖ = 1) :
      volume (outerAffine ⁻¹' tube (4 * (fineContraction * δ)) z w) ≤
        ENNReal.ofReal (fineFiberVolume * δ ^ 2) := by
    rw [affine_volume_preimage outerAffine (by positivity : 0 < fineContraction ^ 3) outerAffine_volume]
    have hr1 : 4 * (fineContraction * δ) ≤ 1 := by dsimp [fineContraction]; linarith
    calc
      _ ≤ ENNReal.ofReal ((fineContraction ^ 3)⁻¹) *
          ENNReal.ofReal (56 * (4 * (fineContraction * δ)) ^ 2) :=
        mul_le_mul' le_rfl (tube_volume_upper (by positivity) hr1 z w hw)
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        dsimp [fineFiberVolume, fineContraction]
        ring
  obtain ⟨M, j, z, w, hM, hj, hw, hB, hsep, hcover, hmass⟩ :=
    affine_tube_net hδ (mul_pos hκ hδ) hrad (by norm_num : 0 ≤ fineFiberVolume)
      hn x v outerAffine c u hu hc hv hover hprism hpre
  have hr : fineRadius δ 1 = 4 * (fineContraction * δ) := by simp [fineRadius]
  refine ⟨M, j, z, w, hM, hj, hw, by simpa only [hr] using hB,
    by simpa only [hr] using hsep, by simpa only [hr] using hcover, ?_⟩
  have hfrac : fineRetainedFraction * (n : ℝ) ≤ M := by
    rw [fineRetainedFraction, div_mul_eq_mul_div]
    exact (div_le_iff₀ (by norm_num : 0 < fineFiberBound)).mpr hmass
  exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg n)).trans hfrac

end WangZahlLot.Obl.wz_separated_scales_gain
