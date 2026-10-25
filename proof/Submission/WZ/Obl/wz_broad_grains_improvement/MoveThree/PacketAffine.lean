-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.PacketAffine.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/PacketAffine.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0626 commit e7a7830, PacketAffine.lean. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.SecondPackets
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.AffineVolume

noncomputable section
namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_broad_grains_initialization
  (PacketRefinement PacketLabel packetPiece)

/-- Packet estimates remain valid if their smallest tested angular radius is
increased, for example from the original fine scale to a normalized tube radius. -/
theorem packet_refinement_mono_base {n : ℕ} {β δ r θ : ℝ} {v : Fin n → V}
    {Y Z : Fin n → Set V} {packets : V → Finset (Finset (Fin n))}
    {center : V → Finset (Fin n) → Fin n}
    (h : PacketRefinement β δ θ v Y Z packets center) (hdr : δ ≤ r) :
    PacketRefinement β r θ v Y Z packets center := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  intro p
  refine ⟨(h.2.2.2 p).1, (h.2.2.2 p).2.1, ?_⟩
  intro W hW
  obtain ⟨hne, hcap, hsize, hbroad⟩ := (h.2.2.2 p).2.2 W hW
  exact ⟨hne, hcap, hsize, fun u s hrs => hbroad u s (hdr.trans hrs)⟩

/-- Relabelling the ambient points by a measurable equivalence preserves all
packet counts and angular estimates. The direction vectors are unchanged. -/
theorem packet_refinement_image {n : ℕ} {β δ θ : ℝ} {v : Fin n → V}
    {Y Z : Fin n → Set V} {packets : V → Finset (Finset (Fin n))}
    {center : V → Finset (Fin n) → Fin n}
    (h : PacketRefinement β δ θ v Y Z packets center) (f : V ≃ᵐ V) :
    PacketRefinement β δ θ v (fun i => f '' Y i) (fun i => f '' Z i)
      (fun p => packets (f.symm p)) (fun p W => center (f.symm p) W) := by
  have hmem (p : V) (U : Set V) : p ∈ f '' U ↔ f.symm p ∈ U := by
    constructor
    · rintro ⟨q, hq, rfl⟩
      simpa only [f.symm_apply_apply] using hq
    · intro hp
      exact ⟨f.symm p, hp, f.apply_symm_apply p⟩
  refine ⟨fun i => ⟨f.measurableSet_image.mpr (h.1 i).1, image_mono (h.1 i).2⟩,
    fun W => (h.2.1 W).preimage f.symm.measurable,
    fun W j => (h.2.2.1 W j).preimage f.symm.measurable, ?_⟩
  intro p
  simpa only [hmem] using h.2.2.2 (f.symm p)

/-- Affine point transport is applied before the spatial/angular labels are
formed in normalized coordinates. -/
theorem packet_refinement_affine_image {n : ℕ} {β δ θ : ℝ} {v : Fin n → V}
    {Y Z : Fin n → Set V} {packets : V → Finset (Finset (Fin n))}
    {center : V → Finset (Fin n) → Fin n}
    (h : PacketRefinement β δ θ v Y Z packets center) (f : V ≃ᵃ[ℝ] V) :
    PacketRefinement β δ θ v (fun i => f '' Y i) (fun i => f '' Z i)
      (fun p => packets (f.symm p)) (fun p W => center (f.symm p) W) :=
  packet_refinement_image h f.toContinuousAffineEquiv.toHomeomorph.toMeasurableEquiv

/-- An affine change of variables preserves every relative incidence mass
bound, since all sets have the same Jacobian. -/
theorem affine_incidence_mass {n : ℕ} {Y Z : Fin n → Set V} {t : ENNReal}
    (h : t * ∑ i, μ (Y i) ≤ ∑ i, μ (Z i)) (f : V ≃ᵃ[ℝ] V) :
    t * ∑ i, μ (f '' Y i) ≤ ∑ i, μ (f '' Z i) := by
  have hvol (U : Set V) : μ (f '' U) =
      O |LinearMap.det (f.linear : V →ₗ[ℝ] V)| * μ U :=
    WangZahlLot.Obl.wz_regular_transverse_affine_cells.affineEquiv_volume f U
  simp only [hvol, ← Finset.mul_sum, mul_left_comm t]
  exact mul_le_mul' le_rfl h

/-- A normalized label pulled back to physical space. These sets deliberately
use the normalized point in the spatial part of the label. -/
def affinePacketPiece {n : ℕ} (f : V ≃ᵃ[ℝ] V) (θ : ℝ) (v : Fin n → V)
    (Z : Fin n → Set V) (packets : V → Finset (Finset (Fin n)))
    (center : V → Finset (Fin n) → Fin n) (label : PacketLabel) (i : Fin n) : Set V :=
  f ⁻¹' packetPiece θ v (fun i => f '' Z i)
    (fun p => packets (f.symm p)) (fun p W => center (f.symm p) W) label i

theorem affinePacketPiece_subset {n : ℕ} (f : V ≃ᵃ[ℝ] V) (θ : ℝ) (v : Fin n → V)
    (Z : Fin n → Set V) (packets : V → Finset (Finset (Fin n)))
    (center : V → Finset (Fin n) → Fin n) (label : PacketLabel) (i : Fin n) :
    affinePacketPiece f θ v Z packets center label i ⊆ Z i := by
  intro p hp
  exact f.injective.mem_set_image.mp hp.1

theorem affinePacketPiece_image {n : ℕ} (f : V ≃ᵃ[ℝ] V) (θ : ℝ) (v : Fin n → V)
    (Z : Fin n → Set V) (packets : V → Finset (Finset (Fin n)))
    (center : V → Finset (Fin n) → Fin n) (label : PacketLabel) (i : Fin n) :
    f '' affinePacketPiece f θ v Z packets center label i =
      packetPiece θ v (fun i => f '' Z i)
        (fun p => packets (f.symm p)) (fun p W => center (f.symm p) W) label i :=
  image_preimage_eq _ f.surjective

theorem affinePacketPiece_measurable {n : ℕ} {β δ θ : ℝ} {v : Fin n → V}
    {Y Z : Fin n → Set V} {packets : V → Finset (Finset (Fin n))}
    {center : V → Finset (Fin n) → Fin n}
    (h : PacketRefinement β δ θ v Y Z packets center) (f : V ≃ᵃ[ℝ] V)
    (label : PacketLabel) (i : Fin n) :
    M (affinePacketPiece f θ v Z packets center label i) :=
  ((packet_refinement_affine_image h f).measurable_piece label i).preimage
    f.toContinuousAffineEquiv.continuous.measurable

/-- An occupied normalized label still contains an entire original packet
at a physical point. This is the input needed by physical width growth. -/
theorem affine_packet_piece_contains_packet {n : ℕ} {β δ θ : ℝ} {v : Fin n → V}
    {Y Z : Fin n → Set V} {packets : V → Finset (Finset (Fin n))}
    {center : V → Finset (Fin n) → Fin n}
    (h : PacketRefinement β δ θ v Y Z packets center) (f : V ≃ᵃ[ℝ] V)
    (label : PacketLabel)
    (hne : (⋃ i, affinePacketPiece f θ v Z packets center label i).Nonempty) :
    ∃ p W, W ∈ packets p ∧
      ∀ i ∈ W, p ∈ affinePacketPiece f θ v Z packets center label i := by
  have hne' : (⋃ i, packetPiece θ v (fun i => f '' Z i)
      (fun p => packets (f.symm p)) (fun p W => center (f.symm p) W) label i).Nonempty := by
    obtain ⟨i, p, hp⟩ := nonempty_iUnion.mp hne
    exact nonempty_iUnion.mpr ⟨i, f p, hp⟩
  obtain ⟨p, W, hW, hWp⟩ := packet_piece_contains_packet
    (packet_refinement_affine_image h f) label hne'
  refine ⟨f.symm p, W, hW, ?_⟩
  intro i hi
  simpa only [affinePacketPiece, mem_preimage, f.apply_symm_apply] using hWp i hi

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
