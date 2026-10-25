-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.SharpPrismNormalization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/SharpPrismNormalization.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.RoundPrismWidth

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_flat_factored_improvement (BodyGeometry)

noncomputable section

theorem sharp_prism_body_normalization {a b r d w : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 4) (hr : 0 < r) (hd : d ≤ r / 4)
    (hw : 0 < w) {n : ℕ} (U : Fin n → Set V) (x : Fin n → V)
    (hcompact : ∀ i, IsCompact (U i)) (hconvex : ∀ i, Convex ℝ (U i))
    (hball : ∀ i, ball (x i) r ⊆ U i)
    (hlong : ∀ i, ∃ p ∈ U i, ∃ q ∈ U i, (1 / 4 : ℝ) ≤ dist p q)
    (hvolume : ∀ i, μ (U i) = O w)
    (z : V) (e : V ≃ₗᵢ[ℝ] V) (hbox : ∀ i, U i ⊆ P a b 4 z e) :
    ∃ f : V ≃ᵃ[ℝ] V,
      (∀ W, μ (f '' W) = O (1 / (4 * a * b)) * μ W) ∧
      (∀ i, f '' U i ⊆ ball (0 : V) 1) ∧
      BodyGeometry (fun i => f '' U i) (fun i => f (x i)) d
        (r / (8192 * a)) (w / (4 * a * b)) := by
  obtain ⟨f, hvol, hunit, hdist, hcoord⟩ := fixed_prism_normalization_coordinates ha hab hb z e
  have hbpos : 0 < b := ha.trans_le hab
  have hbound i : f '' U i ⊆ ball (0 : V) 1 := (image_mono (hbox i)).trans hunit
  have hint i : ball (f (x i)) (r / 4) ⊆ f '' U i := by
    intro p hp
    refine ⟨f.symm p, hball i ?_, f.apply_symm_apply p⟩
    have hh := hdist (f.symm p) (x i)
    rw [f.apply_symm_apply] at hh
    rw [mem_ball] at hp ⊢
    linarith
  have hcompact' i : IsCompact (f '' U i) :=
    (hcompact i).image f.toContinuousAffineEquiv.continuous
  have hconvex' i : Convex ℝ (f '' U i) := (hconvex i).affine_image f.toAffineMap
  have hvol' i : μ (f '' U i) = O (w / (4 * a * b)) := by
    rw [hvol, hvolume, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (4 * a * b))]
    congr 1
    ring
  refine ⟨f, hvol, hbound, hcompact', hconvex', fun i => (hbound i).trans ball_subset_closedBall,
    fun i => (ball_subset_ball hd).trans (hint i), ?_, ?_, ?_⟩
  · intro i
    obtain ⟨p, hp, q, hq, hpq⟩ := hlong i
    refine ⟨f p, mem_image_of_mem f hp, f q, mem_image_of_mem f hq, ?_⟩
    linarith [hdist p q]
  · intro i
    exact normalized_round_convex_width ha hab hb hr (hconvex i) (x i) z e f
      hcoord hdist (hball i) (hbox i) (hlong i)
  · intro i
    change O (w / (4 * a * b)) ≤ μ (f '' U i) ∧
      μ (f '' U i) ≤ O (384 * (w / (4 * a * b)))
    rw [hvol' i]
    exact ⟨le_rfl, ENNReal.ofReal_le_ofReal (by nlinarith [div_pos hw (by positivity : 0 < 4 * a * b)])⟩


end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
