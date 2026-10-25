-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.PacketAffineMass.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/PacketAffineMass.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0626 commit e7a7830, PacketAffineMass.lean. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PacketAffine
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.PacketLocal

noncomputable section
namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_broad_grains_initialization
  (PacketRefinement PacketLabel packetPiece packetLabelUniverse)
open WangZahlLot.Obl.wz_measurable_angular_selection (pd)

theorem affinePacketPiece_nonempty {n : ℕ} (f : V ≃ᵃ[ℝ] V) (θ : ℝ) (v : Fin n → V)
    (Z : Fin n → Set V) (packets : V → Finset (Finset (Fin n)))
    (center : V → Finset (Fin n) → Fin n) (label : PacketLabel) (i : Fin n) :
    (affinePacketPiece f θ v Z packets center label i).Nonempty ↔
      (packetPiece θ v (fun i => f '' Z i)
        (fun p => packets (f.symm p)) (fun p W => center (f.symm p) W) label i).Nonempty := by
  rw [← affinePacketPiece_image]
  exact image_nonempty.symm

/-- The normalized spatial labels partition every original retained row. -/
theorem affine_packet_piece_mass {n : ℕ} {β r θ : ℝ} {x v : Fin n → V}
    {Y Z : Fin n → Set V} {packets : V → Finset (Finset (Fin n))}
    {center : V → Finset (Fin n) → Fin n}
    (h : PacketRefinement β r θ v Y Z packets center) (f : V ≃ᵃ[ℝ] V)
    (hθ : 0 < θ) (hrθ : r ≤ θ) (hv : ∀ i, ‖v i‖ = 1)
    (hZT : ∀ i, f '' Z i ⊆ T r (x i) (v i)) :
    (∑ label ∈ packetLabelUniverse θ x v,
      ∑ i, μ (affinePacketPiece f θ v Z packets center label i)) = ∑ i, μ (Z i) := by
  classical
  let h' := packet_refinement_affine_image h f
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have hcover : (⋃ label ∈ packetLabelUniverse θ x v,
      affinePacketPiece f θ v Z packets center label i) = Z i := by
    ext p
    constructor
    · intro hp
      obtain ⟨label, _, hp⟩ := mem_iUnion₂.mp hp
      exact affinePacketPiece_subset f θ v Z packets center label i hp
    · intro hp
      have hp' : f p ∈ f '' Z i := mem_image_of_mem f hp
      rw [← h'.piece_cover i] at hp'
      obtain ⟨label, hp'⟩ := mem_iUnion.mp hp'
      have hl := h'.piece_label hθ hrθ hv hZT hp'
      exact mem_iUnion₂.mpr ⟨label, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hl⟩, hp'⟩
  rw [← hcover]
  symm
  exact measure_biUnion_finset
    (fun label _ label' _ hne => (h'.piece_disjoint i hne).preimage f)
    (fun label _ => affinePacketPiece_measurable h f label i)

/-- Each original row occupies only a fixed number of normalized labels. -/
theorem affine_packet_piece_card_sum {n : ℕ} {β r θ : ℝ} {x v : Fin n → V}
    {Y Z : Fin n → Set V} {packets : V → Finset (Finset (Fin n))}
    {center : V → Finset (Fin n) → Fin n}
    (h : PacketRefinement β r θ v Y Z packets center) (f : V ≃ᵃ[ℝ] V)
    (hθ : 0 < θ) (hrθ : r ≤ θ) (hv : ∀ i, ‖v i‖ = 1)
    (hZT : ∀ i, f '' Z i ⊆ T r (x i) (v i)) :
    (∑ label ∈ packetLabelUniverse θ x v,
      ({i | (affinePacketPiece f θ v Z packets center label i).Nonempty}.ncard : ℝ)) ≤
        (2*6^3*22^3 : ℝ)*n := by
  simpa only [affinePacketPiece_nonempty] using
    (packet_refinement_affine_image h f).piece_card_sum (x := x) hθ hrθ hv hZT

/-- Pulling a normalized label back preserves its broadness in the direction
vectors used for packet selection. -/
theorem affine_packet_piece_broad {n : ℕ} {β r₀ θ : ℝ} {v : Fin n → V}
    {Y Z : Fin n → Set V} {packets : V → Finset (Finset (Fin n))}
    {center : V → Finset (Fin n) → Fin n}
    (h : PacketRefinement β r₀ θ v Y Z packets center) (f : V ≃ᵃ[ℝ] V)
    (label : PacketLabel) (p u : V) (r : ℝ) (hr : r₀ ≤ r) :
    q n {i | p ∈ affinePacketPiece f θ v Z packets center label i ∧ pd (v i) u ≤ r} ≤
      2*(r/θ)^β*q n {i | p ∈ affinePacketPiece f θ v Z packets center label i} :=
  WangZahlLot.Obl.wz_move_two_dense_broad_prisms.packet_piece_broad
    (packet_refinement_affine_image h f) label (f p) u r hr

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
