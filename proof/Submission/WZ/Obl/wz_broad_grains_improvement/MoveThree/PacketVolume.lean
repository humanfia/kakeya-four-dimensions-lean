-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.PacketVolume.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/PacketVolume.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0641 commit 7652d3d, PacketVolume.lean;
   the integral count is supplied by accepted o149. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.BlockPacketGeometry
import Submission.WZ.Obl.wz_terminal_grains_restoration.Basic

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open scoped ENNReal Classical
open WangZahlLot.Obl.wz_broad_grains_initialization
  (PacketRefinement PacketLabel packetPiece)

/-- Summing the union volumes of arbitrary packet labels costs only the number
of packets through a point. This bound is independent of body multiplicity. -/
theorem packet_union_volume_sum {n : ℕ} {β r θ : ℝ} {v : Fin n → V}
    {Y Z : Fin n → Set V} {packets : V → Finset (Finset (Fin n))}
    {center : V → Finset (Fin n) → Fin n}
    (href : PacketRefinement β r θ v Y Z packets center) (hθ : 0 < θ)
    (Lab : Finset PacketLabel) :
    (∑ ℓ ∈ Lab, μ (⋃ i, packetPiece θ v Z packets center ℓ i)) ≤
      O (2 * θ ^ (-β)) * μ (⋃ i, Z i) := by
  classical
  have hupper := WangZahlLot.Obl.wz_terminal_grains_restoration.sum_measure_le_of_mult_le
    volume Lab (fun ℓ => ⋃ i, packetPiece θ v Z packets center ℓ i)
    (fun ℓ _ => MeasurableSet.iUnion fun i => href.measurable_piece ℓ i)
    (2 * θ ^ (-β))
  apply (hupper ?_).trans
  · exact mul_le_mul' le_rfl (measure_mono (iUnion_subset fun ℓ => iUnion_subset fun _ =>
      iUnion_subset fun i p hp => mem_iUnion.mpr ⟨i, hp.1⟩))
  · intro p _
    let code : Finset (Fin n) → PacketLabel := fun W =>
      WangZahlLot.Obl.wz_balanced_cluster_cover.lab θ (fun q => v (center q W)) p
    have hs : {ℓ : PacketLabel | ∃ i, p ∈ packetPiece θ v Z packets center ℓ i} ⊆
        ((packets p).image code : Set PacketLabel) := by
      rintro ℓ ⟨i, _, W, hW, _, hℓ⟩
      exact Finset.mem_image.mpr ⟨W, hW, hℓ⟩
    have hfin := ((packets p).image code).finite_toSet.subset hs
    have hn := Set.ncard_le_ncard (s := {ℓ : PacketLabel |
      ℓ ∈ Lab ∧ p ∈ ⋃ i, packetPiece θ v Z packets center ℓ i})
      (t := {ℓ : PacketLabel | ∃ i, p ∈ packetPiece θ v Z packets center ℓ i})
      (fun _ h => Set.mem_iUnion.mp h.2) hfin
    have hreal : (({ℓ : PacketLabel | ℓ ∈ Lab ∧
        p ∈ ⋃ i, packetPiece θ v Z packets center ℓ i}).ncard : ℝ) ≤ 2 * θ ^ (-β) :=
      (Nat.cast_le.mpr (hn.trans (href.piece_label_count p))).trans (href.card_bound hθ p)
    have he : {ℓ : PacketLabel | ℓ ∈ Lab ∧
        p ∈ ⋃ i, packetPiece θ v Z packets center ℓ i} =
        (↑(Lab.filter (fun ℓ => p ∈ ⋃ i, packetPiece θ v Z packets center ℓ i)) : Set PacketLabel) := by
      ext ℓ
      simp
    rw [he, Set.ncard_coe_finset] at hreal
    exact hreal

/-- The same overlap budget can be charged to the shading before packet
extraction, and to any smaller common base scale. -/
theorem packet_union_volume_sum_at_base {n : ℕ} {β r θ δ : ℝ} {v : Fin n → V}
    {Y Z : Fin n → Set V} {packets : V → Finset (Finset (Fin n))}
    {center : V → Finset (Fin n) → Fin n}
    (href : PacketRefinement β r θ v Y Z packets center)
    (hδ : 0 < δ) (hδθ : δ ≤ θ) (hβ : 0 ≤ β) (Lab : Finset PacketLabel) :
    (∑ ℓ ∈ Lab, μ (⋃ i, packetPiece θ v Z packets center ℓ i)) ≤
      O (2 * δ ^ (-β)) * μ (⋃ i, Y i) := by
  have hθ : 0 < θ := hδ.trans_le hδθ
  apply (packet_union_volume_sum href hθ Lab).trans
  apply mul_le_mul'
  · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hδ hδθ (neg_nonpos.mpr hβ)) (by norm_num))
  · exact measure_mono (Set.iUnion_mono fun i => (href.1 i).2)

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
