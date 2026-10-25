-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.RoundBlockEnclosure.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/RoundBlockEnclosure.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.BoxEnclosure

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric

noncomputable section

/-- A convex container of normalized long bodies has a volume-controlled
prism enclosure with long dimension four. -/
theorem normalized_block_enclosure {n : ℕ} (hn : 0 < n)
    (U : Fin n → Set V) (x : Fin n → V) {r : ℝ} (hr : 0 < r)
    (hball : ∀ i, ball (x i) r ⊆ U i)
    (hbounded : ∀ i, U i ⊆ closedBall (0 : V) 1)
    (hlong : ∀ i, ∃ p ∈ U i, ∃ q ∈ U i, (1 / 4 : ℝ) ≤ dist p q)
    {W : Set V} (hW : Convex ℝ W) (hfin : μ W ≠ ⊤) (hcover : ∀ i, U i ⊆ W) :
    ∃ (a b : ℝ) (z : V) (e : V ≃ₗᵢ[ℝ] V),
      0 < a ∧ a ≤ b ∧ b ≤ 4 ∧
      (∀ i, U i ⊆ P a b 4 z e) ∧ 4 * a * b ≤ 55296 * (μ W).toReal := by
  let i₀ : Fin n := ⟨0, hn⟩
  let W' := W ∩ closedBall (0 : V) 1
  have hUW i : U i ⊆ W' := subset_inter (hcover i) (hbounded i)
  have hx : x i₀ ∈ W' := hUW i₀ (hball i₀ (mem_ball_self hr))
  have hb : W' ⊆ closedBall (x i₀) 2 := by
    intro p hp
    have hh := dist_triangle p 0 (x i₀)
    have hp1 : dist p 0 ≤ 1 := hp.2
    have hx1 : dist 0 (x i₀) ≤ 1 := by simpa only [mem_closedBall, dist_comm] using hx.2
    exact mem_closedBall.mpr (by linarith)
  have hlongW : ∃ p ∈ W', ∃ q ∈ W', (1 / 4 : ℝ) ≤ dist p q := by
    obtain ⟨p, hp, q, hq, hd⟩ := hlong i₀
    exact ⟨p, hUW i₀ hp, q, hUW i₀ hq, hd⟩
  obtain ⟨a, b, e, ha, hab, hb4, hbox, hvol⟩ :=
    convex_enclosure_fixed_length_closed (hW.inter (convex_closedBall (0 : V) 1))
      (ne_top_of_le_ne_top hfin (measure_mono inter_subset_left)) hr
      (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 1 / 4)
      ((hball i₀).trans (hUW i₀)) hb hlongW
  norm_num at hb4 hbox hvol
  refine ⟨a, b, x i₀, e, ha, hab, hb4, fun i => (hUW i).trans hbox, ?_⟩
  have hm := ENNReal.toReal_mono hfin (measure_mono (show W' ⊆ W from inter_subset_left))
  nlinarith

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
