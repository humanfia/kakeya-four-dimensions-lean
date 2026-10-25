-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.PrismOverlap.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/PrismOverlap.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Core
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PrismGeometry
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.ConvexSlab

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (boxAxis inner_boxAxis)

noncomputable section

/-- A positive share of a convex body's volume in a prism places the whole
body in a fixed dilation, by the accepted convex slab concentration lemma. -/
theorem convex_subset_prism_of_overlap {U : Set V} (hconv : Convex ℝ U)
    (hpos : 0 < μ U) (hfin : μ U ≠ ⊤) {a b c τ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hτ : 0 < τ)
    (z : V) (e : V ≃ₗᵢ[ℝ] V)
    (hover : O τ * μ U ≤ μ (U ∩ P a b c z e)) :
    U ⊆ P ((48 / τ) * a) ((48 / τ) * b) ((48 / τ) * c) z e := by
  have hcoord (j : Fin 3) (s : ℝ) (hs : 0 < s)
      (hP : ∀ p ∈ P a b c z e, |e (p - z) j| ≤ s / 2) :
      ∀ p ∈ U, |e (p - z) j| ≤ ((48 / τ) * s) / 2 := by
    have hconc : O τ * μ U ≤ μ (U ∩
        WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.ConvexSlab.slab
          (boxAxis e j) (inner ℝ (boxAxis e j) z) (s / 2)) := by
      apply hover.trans (measure_mono ?_)
      rintro p ⟨hpU, hpP⟩
      refine ⟨hpU, ?_⟩
      change |inner ℝ (boxAxis e j) p - inner ℝ (boxAxis e j) z| ≤ s / 2
      rw [← inner_sub_right, inner_boxAxis]
      exact hP p hpP
    have hh := WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.ConvexSlab.subset_slab
      hconv hpos hfin (by positivity : 0 < s / 2) hτ hconc
    intro p hp
    have hp' := hh hp
    change |inner ℝ (boxAxis e j) p - inner ℝ (boxAxis e j) z| ≤ 48 * (s / 2) / τ at hp'
    rw [← inner_sub_right, inner_boxAxis] at hp'
    convert hp' using 1 <;> ring
  intro p hp
  exact ⟨hcoord 0 a ha (fun _ h => h.1) p hp,
    hcoord 1 b hb (fun _ h => h.2.1) p hp,
    hcoord 2 c hc (fun _ h => h.2.2) p hp⟩

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
