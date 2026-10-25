-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.BlockPacketVolume.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/BlockPacketVolume.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PacketVolume

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_separated_cover_refinement (enumerate enumerate_sum)
open WangZahlLot.Obl.wz_broad_grains_initialization (packetPiece)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (unit)

noncomputable section
namespace BlockAngularData

variable {ω ζ δ ε b ρ c β τ : ℝ} {p n : ℕ} {x v : Fin n → V}
  {Y : Fin n → Set V} {D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y}
  {R : Finset (Fin D.L)} {G : D.NormalizedBlock R}

/-- The sum of union volumes over any set of actual packet labels is
controlled by the original normalized block, independent of body overlap. -/
theorem normalizedPiece_union_sum (A : BlockAngularData D R G β τ)
    (hδ : 0 < δ) (hβ : 0 ≤ β) (S : Finset (Fin A.labels.card)) :
    (∑ l ∈ S, μ (⋃ i, A.normalizedPiece l i)) ≤
      O (2 * δ ^ (-β)) * μ (⋃ i, D.normalizedShade R G.affine i) := by
  obtain ⟨_, hρ, _, _, hc1⟩ := D.dimensions hδ
  have hδρ : δ ≤ ρ := D.grains.1.trans (D.grains.2.1.trans
    (mul_le_of_le_one_right hρ.le hc1))
  have hδθ : δ ≤ A.scale := (by linarith : δ ≤ 2 * ρ).trans A.lower
  have hh := packet_union_volume_sum_at_base A.refinement hδ hδθ hβ A.labels
  have he : (∑ l : Fin A.labels.card, μ (⋃ i, A.normalizedPiece l i)) =
      ∑ l ∈ A.labels, μ (⋃ i, packetPiece A.scale (fun i => unit (A.axis i))
        A.shade A.packets A.center l i) := by
    exact enumerate_sum A.labels (fun l => μ (⋃ i, packetPiece A.scale
      (fun i => unit (A.axis i)) A.shade A.packets A.center l i))
  calc
    _ ≤ ∑ l : Fin A.labels.card, μ (⋃ i, A.normalizedPiece l i) :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ S)
    _ = _ := he
    _ ≤ _ := hh

end BlockAngularData
end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
