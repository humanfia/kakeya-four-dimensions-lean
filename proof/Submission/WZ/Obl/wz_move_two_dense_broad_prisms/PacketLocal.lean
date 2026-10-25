-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.PacketLocal.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.Defs
import Submission.WZ.Obl.wz_broad_grains_initialization.PacketLabels

/-! Broadness and incidence density after assigning measurable angular packets
 to fixed spatial and direction labels. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open MeasureTheory Set
open scoped ENNReal
open wz_broad_grains_initialization (PacketRefinement PacketLabel packetPiece packetLabelUniverse)
open wz_measurable_angular_selection (pd)

/-- Any union of whole packets at a point retains their broadness. In particular,
the measurable label assignment does not incur an angular loss. -/
theorem packet_piece_broad {n : ℕ} {β d θ : ℝ} {v : Fin n → V}
    {Y Z : Fin n → Set V} {F : V → Finset (Finset (Fin n))}
    {a : V → Finset (Fin n) → Fin n}
    (h : PacketRefinement β d θ v Y Z F a) (ℓ : PacketLabel)
    (p u : V) (r : ℝ) (hr : d ≤ r) :
    q n {i | p ∈ packetPiece θ v Z F a ℓ i ∧ pd (v i) u ≤ r} ≤
      2 * (r / θ) ^ β * q n {i | p ∈ packetPiece θ v Z F a ℓ i} := by
  classical
  let Q := (F p).filter (fun W =>
    wz_balanced_cluster_cover.lab θ (fun q => v (a q W)) p = ℓ)
  have hQsub : (Q : Set (Finset (Fin n))) ⊆ F p := Finset.filter_subset _ _
  have hQdis : (Q : Set (Finset (Fin n))).Pairwise Disjoint :=
    ((h.2.2.2 p).1).mono hQsub
  have hmem (i : Fin n) : p ∈ packetPiece θ v Z F a ℓ i ↔ i ∈ Q.biUnion id := by
    constructor
    · rintro ⟨_, W, hW, hiW, hl⟩
      exact Finset.mem_biUnion.mpr ⟨W, Finset.mem_filter.mpr ⟨hW, hl⟩, hiW⟩
    · intro hi
      obtain ⟨W, hW, hiW⟩ := Finset.mem_biUnion.mp hi
      obtain ⟨hWF, hl⟩ := Finset.mem_filter.mp hW
      have hiZ : p ∈ Z i := by
        change i ∈ {i | p ∈ Z i}
        rw [← (h.2.2.2 p).2.1]
        exact Finset.mem_biUnion.mpr ⟨W, hWF, hiW⟩
      exact ⟨hiZ, W, hWF, hiW, hl⟩
  have htotal : {i | p ∈ packetPiece θ v Z F a ℓ i} = (Q.biUnion id : Set (Fin n)) :=
    Set.ext hmem
  have hcap : {i | p ∈ packetPiece θ v Z F a ℓ i ∧ pd (v i) u ≤ r} =
      ((Q.biUnion id).filter (fun i => pd (v i) u ≤ r) : Set (Fin n)) := by
    ext i
    simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter, hmem]
  change (Set.ncard _ : ℝ) ≤ _ * (Set.ncard _ : ℝ)
  rw [htotal, hcap, Set.ncard_coe_finset, Set.ncard_coe_finset]
  exact wz_broad_grains_initialization.angular_packet_union v Q hQdis
    (fun W hW u r hr => ((h.2.2.2 p).2.2 W (hQsub hW)).2.2.2 u r hr) u r hr

/-- A common measurable spatial cut of a labelled piece preserves its broadness. -/
theorem packet_piece_cut_broad {n : ℕ} {β d θ : ℝ} {v : Fin n → V}
    {Y Z : Fin n → Set V} {F : V → Finset (Finset (Fin n))}
    {a : V → Finset (Fin n) → Fin n}
    (h : PacketRefinement β d θ v Y Z F a) (ℓ : PacketLabel) (E : Set V)
    (p u : V) (r : ℝ) (hr : d ≤ r) :
    q n {i | p ∈ packetPiece θ v Z F a ℓ i ∩ E ∧ pd (v i) u ≤ r} ≤
      2 * (r / θ) ^ β * q n {i | p ∈ packetPiece θ v Z F a ℓ i ∩ E} := by
  by_cases hp : p ∈ E
  · simpa only [Set.mem_inter_iff, hp, and_true] using packet_piece_broad h ℓ p u r hr
  · simp [hp, q, wz_move_two_long_grains_gain.q]

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
