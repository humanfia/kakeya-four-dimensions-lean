-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.BoxEnclosure.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/BoxEnclosure.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Core
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PrismGeometry
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.ConvexBox
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.CoarseTranslation

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (frozen_prism_norm)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Factor (box_approx_general)

noncomputable section

/-- A bounded convex container with a long segment can be enclosed by a
prism of prescribed long dimension, with volume controlled by its aspect
ratio bound. This works for grain bodies as well as round tubes. -/
theorem convex_enclosure_fixed_length_closed {W : Set V} {p : V} {r R ℓ : ℝ}
    (hW : Convex ℝ W) (hfin : μ W ≠ ⊤) (hr : 0 < r) (hR : 0 < R) (hℓ : 0 < ℓ)
    (hball : ball p r ⊆ W) (hbound : W ⊆ closedBall p R)
    (hlong : ∃ x ∈ W, ∃ y ∈ W, ℓ ≤ dist x y) :
    ∃ (a b : ℝ) (e : V ≃ₗᵢ[ℝ] V),
      0 < a ∧ a ≤ b ∧ b ≤ 2 * R ∧
      W ⊆ P a b (2 * R) p e ∧
      a * b * (2 * R) ≤ (6912 * R / ℓ) * (μ W).toReal := by
  let τ : V ≃ᵃ[ℝ] V := AffineEquiv.vaddConst ℝ (-p)
  have hτ (x : V) : τ x = x - p := by simp [τ, sub_eq_add_neg]
  have hτball : ball (0 : V) r ⊆ τ '' W := by
    intro x hx
    refine ⟨x + p, hball ?_, ?_⟩
    · simpa only [mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hx
    · rw [hτ]; abel
  have hτbound : τ '' W ⊆ ball (0 : V) (R + 1) := by
    rintro _ ⟨x, hx, rfl⟩
    have hh : ‖x - p‖ ≤ R := hbound hx
    simpa only [hτ, mem_ball, dist_eq_norm, sub_zero] using
      (show ‖x - p‖ < R + 1 by linarith)
  obtain ⟨A, B, C, e, hA, hAB, hBC, hbox, hvol⟩ := box_approx_general
    (hW.affine_image τ.toAffineMap) hr hτball hτbound
  have hbox' : W ⊆ P A B C p e := by
    intro x hx
    have hm := hbox ⟨x, hx, rfl⟩
    change τ x ∈ P A B C 0 e at hm
    simpa only [P, mem_ofPred_eq, hτ, sub_zero] using hm
  have hB : 0 < B := hA.trans_le hAB
  have hC : 0 < C := hA.trans_le (hAB.trans hBC)
  have hCℓ : ℓ ≤ 2 * C := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hlong
    have hxC := frozen_prism_norm hA.le hAB hBC p e (hbox' hx)
    have hyC := frozen_prism_norm hA.le hAB hBC p e (hbox' hy)
    have hh := norm_sub_le (x - p) (y - p)
    rw [sub_sub_sub_cancel_right] at hh
    rw [dist_eq_norm] at hxy
    linarith
  have htranslate : μ (τ '' W) = μ W := by
    simpa only [τ, AffineEquiv.vaddConst_apply, vadd_eq_add] using
      WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.volume_image_translation W (-p)
  have hvolR : A * B * C ≤ 1728 * (μ W).toReal := by
    change O (A * B * C) ≤ 1728 * μ (τ '' W) at hvol
    rw [htranslate, ← ENNReal.ofReal_toReal hfin,
      ← ENNReal.ofReal_ofNat 1728, ← ENNReal.ofReal_mul (by norm_num)] at hvol
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hvol
  refine ⟨min A (2 * R), min B (2 * R), e, lt_min hA (by positivity),
    min_le_min_right _ hAB, min_le_right _ _, ?_, ?_⟩
  · intro x hx
    have hb := hbox' hx
    have hnorm : ‖x - p‖ ≤ R := hbound hx
    have hcoord (j : Fin 3) : |e (x - p) j| ≤ R := by
      have hh := PiLp.norm_apply_le (e (x - p)) j
      rw [Real.norm_eq_abs, e.norm_map] at hh
      exact hh.trans hnorm
    refine ⟨?_, ?_, ?_⟩
    · rw [← min_div_div_right (by norm_num : (0 : ℝ) ≤ 2)]
      exact le_min hb.1 (by linarith [hcoord 0])
    · rw [← min_div_div_right (by norm_num : (0 : ℝ) ≤ 2)]
      exact le_min hb.2.1 (by linarith [hcoord 1])
    · linarith [hcoord 2]
  · rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hℓ).mpr
    have hsmall : min A (2 * R) * min B (2 * R) ≤ A * B :=
      mul_le_mul (min_le_left _ _) (min_le_left _ _) (by positivity) hA.le
    have h1 := mul_le_mul_of_nonneg_left hCℓ (mul_nonneg (mul_nonneg hA.le
      (hA.le.trans hAB)) (by positivity : 0 ≤ 2 * R))
    have h2 := mul_le_mul_of_nonneg_right hvolR (by positivity : 0 ≤ 4 * R)
    nlinarith [mul_le_mul_of_nonneg_right hsmall (by positivity : 0 ≤ 2 * R * ℓ)]

/-- The open-ball version of the enclosure interface. -/
theorem convex_enclosure_fixed_length {W : Set V} {p : V} {r R ℓ : ℝ}
    (hW : Convex ℝ W) (hfin : μ W ≠ ⊤) (hr : 0 < r) (hR : 0 < R) (hℓ : 0 < ℓ)
    (hball : ball p r ⊆ W) (hbound : W ⊆ ball p R)
    (hlong : ∃ x ∈ W, ∃ y ∈ W, ℓ ≤ dist x y) :
    ∃ (a b : ℝ) (e : V ≃ₗᵢ[ℝ] V),
      0 < a ∧ a ≤ b ∧ b ≤ 2 * R ∧
      W ⊆ P a b (2 * R) p e ∧
      a * b * (2 * R) ≤ (6912 * R / ℓ) * (μ W).toReal :=
  convex_enclosure_fixed_length_closed hW hfin hr hR hℓ hball
    (hbound.trans ball_subset_closedBall) hlong

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
