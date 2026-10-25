-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.ClippedPacketGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/ClippedPacketGeometry.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0708 commit 170d089, ClippedPacketGeometry.lean. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.ClippedCarrier
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PacketAffineGeometry

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set Metric MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (boxAxis boxAxis_norm)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (unit norm_unit)
open WangZahlLot.Obl.wz_broad_grains_initialization (PacketRefinement PacketLabel)

/-- Actual old grains in one physically thin localized carrier supply all
the whole-body geometric hypotheses for the second packet enclosure. -/
theorem clipped_packet_prism {n : ℕ} {a ρ c A B C δ β θ : ℝ}
    (ha : 0 ≤ a) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hc : 0 < c)
    (hac : a ≤ ρ*c) (hA : 0 < A) (hδρ : δ ≤ 2*ρ) (hρθ : 2*ρ ≤ θ)
    (hα : ρ*A/(4*min A (ρ*c)) ≤ 1/8)
    (z : Fin n → V) (e : Fin n → V ≃ₗᵢ[ℝ] V)
    (z₀ z' : V) (g : V ≃ₗᵢ[ℝ] V) :
    let f := carrierAffine (lt_min hA (mul_pos hρ hc)) hc hρ z₀ z' g
    let ν := fun j => unit (f.linear (boxAxis (e j) 2))
    let α := ρ*A/(4*min A (ρ*c))
    ∀ (Y Z : Fin n → Set V) (packets : V → Finset (Finset (Fin n)))
      (center : V → Finset (Fin n) → Fin n),
      PacketRefinement β δ θ ν Y Z packets center →
      (∀ j, Y j ⊆ P a (ρ*c) c (z j) (e j)) →
      (∀ j, (Y j).Nonempty →
        P a (ρ*c) c (z j) (e j) ⊆ P A B C z' g ∩ ball z₀ (2*c)) →
      ∀ label : PacketLabel,
        (∃ j, (affinePacketPiece f θ ν Z packets center label j).Nonempty) →
        ∃ (p : V) (E : V ≃ₗᵢ[ℝ] V),
          (∀ j, (affinePacketPiece f θ ν Z packets center label j).Nonempty →
            f '' P a (ρ*c) c (z j) (e j) ⊆
              P (min (36*α) (min (80*θ) 4)) (min (80*θ) 4) 4 p E) ∧
          μ (P (min (36*α) (min (80*θ) 4)) (min (80*θ) 4) 4 p E) ≤ O (11520*α*θ) := by
  dsimp only
  let f := carrierAffine (lt_min hA (mul_pos hρ hc)) hc hρ z₀ z' g
  let ν := fun j => unit (f.linear (boxAxis (e j) 2))
  let α := ρ*A/(4*min A (ρ*c))
  intro Y Z packets center href hY hbody label hne
  have hunit (j : Fin n) : ‖ν j‖ = 1 := by
    apply norm_unit
    intro hh
    have hz : boxAxis (e j) 2 = 0 := f.linear.injective (hh.trans (map_zero _).symm)
    have hn := boxAxis_norm (e j) 2
    rw [hz, norm_zero] at hn
    norm_num at hn
  have hphysical (j : Fin n) (hj : (Y j).Nonempty) :
      P a (ρ*c) c (z j) (e j) ⊆ P A B C z' g := (hbody j hj).trans inter_subset_left
  have hgeom (j : Fin n) (hj : (Y j).Nonempty) :
      f '' P a (ρ*c) c (z j) (e j) ⊆ ball (0 : V) 1 ∩ {p | |p 0| ≤ α/2} :=
    (image_mono (hbody j hj)).trans (carrierAffine_ball_and_slab _ hc hρ hα z₀ z' g)
  have hnormal (j : Fin n) (hj : (Y j).Nonempty) : |ν j 0| ≤ 4*α :=
    clipped_carrier_normal_bound ha hρ hc hA (z j) z₀ z' (e j) g (hphysical j hj)
  apply affine_packet_piece_prism (packet_refinement_mono_base href hδρ)
    (by positivity) hα ((by positivity : 0 < 2*ρ).trans_le hρθ) hρθ
    hunit hY f
    (fun j hj => (clipped_carrier_grain_tube ha hρ hρ1 hc hac hA
      (z j) z₀ z' (e j) g (hphysical j hj)).2.2.2.2)
    (fun j hj => (hgeom j hj).trans inter_subset_left)
    (EuclideanSpace.basisFun (Fin 3) ℝ 0) (by simp) (t := 0)
    (fun j hj => ?_) (fun j hj => ?_) label hne
  · simpa only [EuclideanSpace.basisFun_inner, sub_zero] using
      (hgeom j hj).trans inter_subset_right
  · simpa only [EuclideanSpace.basisFun_inner] using hnormal j hj

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
