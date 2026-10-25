-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.PacketRounding.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/PacketRounding.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0641, commit 707550d, PacketRounding.lean
   (x0670 first-filling chain, building on x0551 geometry). -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.FlatPrismFrames
import Submission.WZ.Obl.wz_tower_depth_step.DoubleSlabGeometry

noncomputable section
namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set Metric MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (boxAxis boxAxis_norm inner_boxAxis)

/-- The interior ball in a normalized old body bounds the short width of every
containing prism, independently of the prism's center. -/
theorem ball_in_prism_short_width {r a b c : ℝ} (hr : 0 < r)
    (x z : V) (e : V ≃ₗᵢ[ℝ] V) (hsub : ball x r ⊆ P a b c z e) : 2 * r ≤ a := by
  have hslab : ball x r ⊆ WangZahlLot.Obl.wz_tower_depth_step.Slab
      (boxAxis e 0) (inner ℝ (boxAxis e 0) z) (a / 2) := by
    intro p hp
    change |inner ℝ (boxAxis e 0) p - inner ℝ (boxAxis e 0) z| ≤ a / 2
    rw [← inner_sub_right, inner_boxAxis]
    exact (hsub hp).1
  obtain ⟨hlo, hhi⟩ := WangZahlLot.Obl.wz_tower_depth_step.ball_slab_projection_bounds
    hr (boxAxis_norm e 0) hslab
  linarith

/-- Rounding the packet short width up to the tube radius costs a fixed factor
relative to the original flat-block short side. -/
theorem rounded_packet_widths {r a θ : ℝ} (ha : 0 ≤ a) (hθ : 0 ≤ θ)
    (hrθ : r ≤ θ) (hθ1 : θ ≤ 1) (hra : r ≤ 100 * a) :
    let b := min (80 * θ) 4
    let A := max r (min (36 * a) b)
    r ≤ A ∧ A ≤ b ∧ A ≤ 100 * a ∧ 4 * θ ≤ b ∧ b ≤ 80 * θ ∧ b ≤ 4 := by
  dsimp only
  have hθb : θ ≤ min (80 * θ) 4 := le_min (by linarith) (by linarith)
  refine ⟨le_max_left _ _, max_le (hrθ.trans hθb) (min_le_right _ _),
    max_le hra ((min_le_left _ _).trans (by linarith)), ?_, min_le_left _ _, min_le_right _ _⟩
  exact le_min (by linarith) (by linarith)

/-- Enlarging only the short width preserves the packet's full-body enclosure. -/
theorem packet_prism_subset_rounded {r a θ : ℝ} (z : V) (e : V ≃ₗᵢ[ℝ] V) :
    P (min (36 * a) (min (80 * θ) 4)) (min (80 * θ) 4) 4 z e ⊆
      P (max r (min (36 * a) (min (80 * θ) 4))) (min (80 * θ) 4) 4 z e := by
  intro p hp
  exact ⟨hp.1.trans (div_le_div_of_nonneg_right (le_max_right _ _) (by norm_num)), hp.2⟩

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
