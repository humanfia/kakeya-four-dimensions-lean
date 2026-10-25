-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.PacketPrismGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/PacketPrismGeometry.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Core
import Submission.WZ.Obl.wz_flat_cluster_slab_filling.Geometry
import Submission.WZ.Obl.wz_broad_grains_initialization.PacketLabels

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_flat_cluster_slab_filling (adapted_frame frame_coord_le_angle tube_point')
open WangZahlLot.Obl.wz_broad_grains_initialization (PacketRefinement PacketLabel packetPiece)

noncomputable section

/-- Intersecting a round carrier with a thin slab preserves both useful
widths. The frame stays adapted to a genuine body direction. -/
theorem slab_carrier_prism {U : Set V} {a θ t : ℝ} {u v w z p₀ : V}
    (ha : 0 ≤ a) (hθ : 0 ≤ θ) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hsmall : |inner ℝ u v| ≤ 1 / 2) (hflat : |inner ℝ u v| ≤ 4 * a)
    (hdir : min ‖v - w‖ ‖v + w‖ ≤ 4 * θ)
    (hp₀ : p₀ ∈ U) (hball : U ⊆ ball (0 : V) 1)
    (hslab : U ⊆ {p | |inner ℝ u p - t| ≤ a / 2})
    (hcar : U ⊆ T (8 * θ) z ((6 : ℝ) • w)) :
    ∃ g : V ≃ₗᵢ[ℝ] V,
      (∀ p, g p 2 = inner ℝ v p) ∧
      (∀ q, |g q 0| ≤ 2 * (|inner ℝ u q| + |inner ℝ u v| * ‖q‖)) ∧
      U ⊆ P (min (36 * a) (min (80 * θ) 4)) (min (80 * θ) 4) 4 p₀ g := by
  obtain ⟨g, hg₂, hg₀⟩ := adapted_frame hu hv hsmall
  refine ⟨g, hg₂, hg₀, ?_⟩
  have hcoord (q : V) (j : Fin 3) : |g q j| ≤ ‖q‖ := by
    simpa only [Real.norm_eq_abs, g.norm_map] using PiLp.norm_apply_le (g q) j
  have hwcoord (j : Fin 3) (hj : j ≠ 2) : |g w j| ≤ 4 * θ := by
    have hh := frame_coord_le_angle hv hg₂ w j hj
    have he : min ‖w - v‖ ‖w + v‖ = min ‖v - w‖ ‖v + w‖ := by
      rw [norm_sub_rev, add_comm w v]
    exact hh.trans (by change min ‖w - v‖ ‖w + v‖ ≤ _; rw [he]; exact hdir)
  intro p hp
  have hn : ‖p - p₀‖ ≤ 2 := by
    have hp1 : ‖p‖ < 1 := by simpa using hball hp
    have hq1 : ‖p₀‖ < 1 := by simpa using hball hp₀
    exact (norm_sub_le _ _).trans (by linarith)
  have hnormal : |inner ℝ u (p - p₀)| ≤ a := by
    have hh := abs_sub (inner ℝ u p - t) (inner ℝ u p₀ - t)
    rw [sub_sub_sub_cancel_right, ← inner_sub_right] at hh
    have hp' : |inner ℝ u p - t| ≤ a / 2 := hslab hp
    have hp₀' : |inner ℝ u p₀ - t| ≤ a / 2 := hslab hp₀
    exact hh.trans (by linarith)
  have hthin : |g (p - p₀) 0| ≤ 18 * a := by
    have hh := hg₀ (p - p₀)
    have hm := mul_le_mul hflat hn (norm_nonneg _) (by positivity : 0 ≤ 4 * a)
    linarith
  have hround (j : Fin 3) (hj : j ≠ 2) : |g (p - p₀) j| ≤ 40 * θ := by
    obtain ⟨s, hs, hps⟩ := tube_point' (hcar hp)
    obtain ⟨s₀, hs₀, hp₀s⟩ := tube_point' (hcar hp₀)
    have hsabs : |s - s₀| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1, hs₀.2], by linarith [hs.2, hs₀.1]⟩
    have he : p - p₀ = (p - (z + s • ((6 : ℝ) • w))) -
        (p₀ - (z + s₀ • ((6 : ℝ) • w))) + ((s - s₀) * 6) • w := by module
    have hec : g (p - p₀) j = g (p - (z + s • ((6 : ℝ) • w))) j -
        g (p₀ - (z + s₀ • ((6 : ℝ) • w))) j + ((s - s₀) * 6) * g w j := by
      rw [he, map_add, map_sub, map_smul]
      simp
    rw [hec]
    calc
      _ ≤ |g (p - (z + s • ((6 : ℝ) • w))) j| +
          |g (p₀ - (z + s₀ • ((6 : ℝ) • w))) j| +
          |((s - s₀) * 6) * g w j| := (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ 8 * θ + 8 * θ + 6 * (4 * θ) := by
        apply add_le_add
        · exact add_le_add ((hcoord _ _).trans hps.le) ((hcoord _ _).trans hp₀s.le)
        · rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
          exact mul_le_mul (by nlinarith : |s - s₀| * 6 ≤ 6) (hwcoord j hj)
            (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  have hzero : |g (p - p₀) 0| ≤ min (36 * a) (min (80 * θ) 4) / 2 := by
    rw [← min_div_div_right (by norm_num : (0 : ℝ) ≤ 2),
      ← min_div_div_right (by norm_num : (0 : ℝ) ≤ 2)]
    exact le_min (by linarith) (le_min (by linarith [hround 0 (by decide)])
      (by linarith [(hcoord (p - p₀) 0).trans hn]))
  have hone : |g (p - p₀) 1| ≤ min (80 * θ) 4 / 2 := by
    rw [← min_div_div_right (by norm_num : (0 : ℝ) ≤ 2)]
    exact le_min (by linarith [hround 1 (by decide)])
      (by linarith [(hcoord (p - p₀) 1).trans hn])
  exact ⟨hzero, hone, by linarith [(hcoord (p - p₀) 2).trans hn]⟩

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
