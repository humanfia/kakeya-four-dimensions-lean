-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.AngularPieces.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/AngularPieces.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PacketPrismGeometry
import Submission.WZ.Obl.wz_broad_grains_initialization.PacketClusters

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_broad_grains_initialization
  (PacketRefinement PacketLabel packetPiece angular_packet_union)
open WangZahlLot.Obl.wz_measurable_angular_selection (pd)

noncomputable section

/-- The spatial component of a packet label is the transverse cell for
its fixed labelled direction. -/
theorem packet_piece_projected_label {n : ℕ} {θ : ℝ} {v : Fin n → V}
    {Z : Fin n → Set V} {packets : V → Finset (Finset (Fin n))}
    {center : V → Finset (Fin n) → Fin n} {ℓ : PacketLabel} {i : Fin n} {p : V}
    (hp : p ∈ packetPiece θ v Z packets center ℓ i) :
    WangZahlLot.Obl.wz_balanced_cluster_cover.cell θ
      (WangZahlLot.Obl.wz_balanced_cluster_cover.proj
        (WangZahlLot.Obl.wz_balanced_cluster_cover.W θ ℓ.1) p) = ℓ.2 := by
  obtain ⟨_, W, _, _, hl⟩ := hp
  have hfirst := congrArg Prod.fst hl
  have hsecond := congrArg Prod.snd hl
  change WangZahlLot.Obl.wz_balanced_cluster_cover.cell θ
    (WangZahlLot.Obl.wz_balanced_cluster_cover.proj
      (WangZahlLot.Obl.wz_balanced_cluster_cover.W θ
        (WangZahlLot.Obl.wz_balanced_cluster_cover.cell θ (v (center p W)))) p) = ℓ.2 at hsecond
  change WangZahlLot.Obl.wz_balanced_cluster_cover.cell θ (v (center p W)) = ℓ.1 at hfirst
  rwa [hfirst] at hsecond

/-- A labelled piece is a disjoint union of broad pointwise packets, so
it retains the same broadness constant. -/
theorem packet_piece_broad {n : ℕ} {β r₀ θ : ℝ} {v : Fin n → V}
    {Y Z : Fin n → Set V} {packets : V → Finset (Finset (Fin n))}
    {center : V → Finset (Fin n) → Fin n}
    (href : PacketRefinement β r₀ θ v Y Z packets center) (ℓ : PacketLabel) :
    ∀ (p u : V) (r : ℝ), r₀ ≤ r →
      q n {i | p ∈ packetPiece θ v Z packets center ℓ i ∧ pd (v i) u ≤ r} ≤
        2 * (r / θ) ^ β * q n {i | p ∈ packetPiece θ v Z packets center ℓ i} := by
  classical
  intro p u r hr
  let C := (packets p).filter fun W =>
    WangZahlLot.Obl.wz_balanced_cluster_cover.lab θ (fun q => v (center q W)) p = ℓ
  have hdis : (C : Set (Finset (Fin n))).Pairwise Disjoint :=
    (href.2.2.2 p).1.mono (Finset.filter_subset _ _)
  have hEq : ((C.biUnion id : Finset (Fin n)) : Set (Fin n)) =
      {i | p ∈ packetPiece θ v Z packets center ℓ i} := by
    ext i
    constructor
    · intro hi
      obtain ⟨W, hW, hiW⟩ := Finset.mem_biUnion.mp hi
      obtain ⟨hWp, hl⟩ := Finset.mem_filter.mp hW
      have hpZi : p ∈ Z i := by
        change i ∈ {i | p ∈ Z i}
        rw [← (href.2.2.2 p).2.1]
        exact Finset.mem_biUnion.mpr ⟨W, hWp, hiW⟩
      exact ⟨hpZi, W, hWp, hiW, hl⟩
    · rintro ⟨_, W, hW, hiW, hl⟩
      exact Finset.mem_biUnion.mpr ⟨W, Finset.mem_filter.mpr ⟨hW, hl⟩, hiW⟩
  have hcap : (((C.biUnion id).filter fun i => pd (v i) u ≤ r : Finset (Fin n)) : Set (Fin n)) =
      {i | p ∈ packetPiece θ v Z packets center ℓ i ∧ pd (v i) u ≤ r} := by
    ext i
    simp only [Finset.mem_coe, Finset.mem_filter, mem_ofPred_eq]
    exact and_congr (show i ∈ C.biUnion id ↔ p ∈ packetPiece θ v Z packets center ℓ i by
      change i ∈ (↑(C.biUnion id) : Set (Fin n)) ↔ _; rw [hEq]; rfl) Iff.rfl
  have hh := angular_packet_union v C hdis (β := β) (δ := r₀) (θ := θ) (C := 2)
    (fun W hW u r hr => ((href.2.2.2 p).2.2 W (Finset.mem_filter.mp hW).1).2.2.2 u r hr) u r hr
  change (({i | p ∈ packetPiece θ v Z packets center ℓ i ∧ pd (v i) u ≤ r}.ncard : ℝ)) ≤
    2 * (r / θ) ^ β * ({i | p ∈ packetPiece θ v Z packets center ℓ i}.ncard : ℝ)
  rw [← hEq, ← hcap, ncard_coe_finset, ncard_coe_finset]
  exact hh

/-- Every occupied label has one common flat-prism enclosure. Both widths
are uniform in the label; only its center and frame vary. -/
theorem packet_piece_prism {n : ℕ} {β r θ a t : ℝ}
    {U Y Z : Fin n → Set V} {x v : Fin n → V}
    {packets : V → Finset (Finset (Fin n))} {center : V → Finset (Fin n) → Fin n}
    (href : PacketRefinement β r θ v Y Z packets center)
    (ha : 0 ≤ a) (ha8 : a ≤ 1 / 8) (hθ : 0 < θ) (hrθ : r ≤ θ)
    (hv : ∀ i, ‖v i‖ = 1) (hYU : ∀ i, Y i ⊆ U i)
    (hUT : ∀ i, U i ⊆ T r (x i) (v i)) (hball : ∀ i, U i ⊆ ball (0 : V) 1)
    (u : V) (hu : ‖u‖ = 1)
    (hslab : ∀ i, U i ⊆ {p | |inner ℝ u p - t| ≤ a / 2})
    (hflat : ∀ i, |inner ℝ u (v i)| ≤ 4 * a)
    (ℓ : PacketLabel) (hne : ∃ i, (packetPiece θ v Z packets center ℓ i).Nonempty) :
    ∃ (z : V) (g : V ≃ₗᵢ[ℝ] V),
      ∀ i, (packetPiece θ v Z packets center ℓ i).Nonempty →
        U i ⊆ P (min (36 * a) (min (80 * θ) 4)) (min (80 * θ) 4) 4 z g := by
  classical
  obtain ⟨i₀, p₀, hp₀⟩ := hne
  let B := ⋃ i, ⋃ (_ : (packetPiece θ v Z packets center ℓ i).Nonempty), U i
  have hBU (i : Fin n) (hi : (packetPiece θ v Z packets center ℓ i).Nonempty) : U i ⊆ B :=
    subset_iUnion_of_subset i (subset_iUnion_of_subset hi Subset.rfl)
  have hp₀B : p₀ ∈ B := hBU i₀ ⟨p₀, hp₀⟩ (hYU i₀ ((href.1 i₀).2 hp₀.1))
  let w := WangZahlLot.Obl.wz_balanced_cluster_cover.W θ ℓ.1
  let z := WangZahlLot.Obl.wz_balanced_cluster_cover.proj w p₀ - (3 : ℝ) • w
  have hw : ‖w‖ = 1 := (href.piece_direction hθ hv hp₀).1
  have hcar : B ⊆ T (8 * θ) z ((6 : ℝ) • w) := by
    apply iUnion_subset
    intro i
    apply iUnion_subset
    rintro ⟨p, hp⟩
    have hpU : p ∈ U i := hYU i ((href.1 i).2 hp.1)
    have hcell := (packet_piece_projected_label hp).trans (packet_piece_projected_label hp₀).symm
    apply (hUT i).trans
    have hh := WangZahlLot.Obl.wz_balanced_cluster_cover.tube_subset_cyl (A := 2)
      hθ hrθ hw (show ‖p‖ < 1 by simpa using hball i hpU) (hUT i hpU)
      (by simpa only [pd, w, show (2 : ℝ) + 2 = 4 by norm_num] using
        (href.piece_direction hθ hv hp).2) hcell
    simpa only [show (2 : ℝ) + 6 = 8 by norm_num] using hh
  obtain ⟨g, _, _, hBg⟩ := slab_carrier_prism ha hθ.le hu (hv i₀)
    ((hflat i₀).trans (by linarith)) (hflat i₀) ((href.piece_direction hθ hv hp₀).2)
    hp₀B (iUnion_subset fun i => iUnion_subset fun _ => hball i)
    (iUnion_subset fun i => iUnion_subset fun _ => hslab i) hcar
  exact ⟨p₀, g, fun i hi => (hBU i hi).trans hBg⟩

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
