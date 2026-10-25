-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.RoundPrismWidth.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/RoundPrismWidth.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.ConvexWidth
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PrismBodyNormalization
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.SlabSelection

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_flat_factored_improvement (WideSection wideSection_of_diamond)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (boxAxis boxAxis_norm inner_boxAxis)
open WangZahlLot.Obl.wz_regular_transverse_affine_cells (half_radius_le_slab_width)

theorem ball_radius_le_prism_short {U : Set V} {a b c r : ℝ}
    {x z : V} {e : V ≃ₗᵢ[ℝ] V} (hr : 0 < r)
    (hball : ball x r ⊆ U) (hbox : U ⊆ P a b c z e) : r ≤ a := by
  have hh := half_radius_le_slab_width (boxAxis_norm e 0) hr
    (s := inner ℝ (boxAxis e 0) z) (r := a / 2) (by
      intro p hp
      change |inner ℝ (boxAxis e 0) p - inner ℝ (boxAxis e 0) z| ≤ a / 2
      rw [← inner_sub_right, inner_boxAxis]
      exact (hbox (hball hp)).1)
  linarith

theorem ball_wideSection {r : ℝ} (hr : 0 < r) (x : V) :
    WideSection (ball x r) (r / 4) := by
  have hh := wideSection_of_diamond (by positivity : 0 ≤ r / 2) x
    (EuclideanSpace.basisFun (Fin 3) ℝ 0) (EuclideanSpace.basisFun (Fin 3) ℝ 1)
    (by simp) (by simp)
    (by simpa using (EuclideanSpace.basisFun (Fin 3) ℝ).orthonormal.2 (by decide : (0 : Fin 3) ≠ 1)) (by
      intro s t hst
      rw [mem_ball, dist_eq_norm]
      have he : x + s • EuclideanSpace.basisFun (Fin 3) ℝ 0 +
          t • EuclideanSpace.basisFun (Fin 3) ℝ 1 - x =
          s • EuclideanSpace.basisFun (Fin 3) ℝ 0 + t • EuclideanSpace.basisFun (Fin 3) ℝ 1 := by abel
      rw [he]
      have hn := norm_add_le (s • EuclideanSpace.basisFun (Fin 3) ℝ 0)
        (t • EuclideanSpace.basisFun (Fin 3) ℝ 1)
      simp only [norm_smul, Real.norm_eq_abs, OrthonormalBasis.norm_eq_one, mul_one] at hn
      linarith)
  convert hh using 1 <;> ring

/-- The sharp width bound extends to thick enclosing prisms by using the
interior ball directly. -/
theorem normalized_round_convex_width {U : Set V} {a b r : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 4) (hr : 0 < r) (hU : Convex ℝ U)
    (x z : V) (e : V ≃ₗᵢ[ℝ] V) (f : V ≃ᵃ[ℝ] V)
    (hf : ∀ p i, f p i = (![a⁻¹, b⁻¹, 1 / 4] : Fin 3 → ℝ) i * e (p - z) i)
    (hdist : ∀ p q, dist p q / 4 ≤ dist (f p) (f q))
    (hball : ball x r ⊆ U) (hbox : U ⊆ P a b 4 z e)
    (hlong : ∃ p ∈ U, ∃ q ∈ U, (1 / 4 : ℝ) ≤ dist p q) :
    WideSection (f '' U) (r / (8192 * a)) := by
  by_cases haSmall : a ≤ 1 / 64
  · exact normalized_convex_width ha hab hb haSmall hr
      (ball_radius_le_prism_short hr hball hbox) hU x z e f hf hball hbox hlong
  have hint : ball (f x) (r / 4) ⊆ f '' U := by
    intro p hp
    refine ⟨f.symm p, hball ?_, f.apply_symm_apply p⟩
    have hh := hdist (f.symm p) x
    rw [f.apply_symm_apply] at hh
    rw [mem_ball] at hp ⊢
    linarith
  have hw := (ball_wideSection (by positivity : 0 < r / 4) (f x)).mono hint
  intro ℓ
  obtain ⟨p, hp, q, hq, he, hd⟩ := hw ℓ
  refine ⟨p, hp, q, hq, he, ?_⟩
  apply le_trans _ hd
  have hh : 16 ≤ 8192 * a := by linarith
  have hdiv := div_le_div_of_nonneg_left hr.le (by norm_num : (0 : ℝ) < 16) hh
  convert hdiv using 1 <;> ring

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
