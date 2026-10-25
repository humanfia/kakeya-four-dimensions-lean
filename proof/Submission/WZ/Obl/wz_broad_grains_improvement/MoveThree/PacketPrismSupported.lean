-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.PacketPrismSupported.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/PacketPrismSupported.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0626 e7a7830 PacketPrism.lean; reuses the original o153 helpers. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.AngularPieces
namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_broad_grains_initialization
  (PacketRefinement PacketLabel packetPiece)
open WangZahlLot.Obl.wz_measurable_angular_selection (pd)
noncomputable section
/-- Every occupied label has one common flat-prism enclosure. Both widths
are uniform in the label; only its center and frame vary. -/
theorem packet_piece_prism_supported {n : ℕ} {β r θ a t : ℝ}
    {U Y Z : Fin n → Set V} {x v : Fin n → V}
    {packets : V → Finset (Finset (Fin n))} {center : V → Finset (Fin n) → Fin n}
    (href : PacketRefinement β r θ v Y Z packets center)
    (ha : 0 ≤ a) (ha8 : a ≤ 1 / 8) (hθ : 0 < θ) (hrθ : r ≤ θ)
    (hv : ∀ i, ‖v i‖ = 1) (hYU : ∀ i, Y i ⊆ U i)
    (hUT : ∀ i, (Y i).Nonempty → U i ⊆ T r (x i) (v i))
    (hball : ∀ i, (Y i).Nonempty → U i ⊆ ball (0 : V) 1)
    (u : V) (hu : ‖u‖ = 1)
    (hslab : ∀ i, (Y i).Nonempty → U i ⊆ {p | |inner ℝ u p - t| ≤ a / 2})
    (hflat : ∀ i, (Y i).Nonempty → |inner ℝ u (v i)| ≤ 4 * a)
    (ℓ : PacketLabel) (hne : ∃ i, (packetPiece θ v Z packets center ℓ i).Nonempty) :
    ∃ (z : V) (g : V ≃ₗᵢ[ℝ] V),
      ∀ i, (packetPiece θ v Z packets center ℓ i).Nonempty →
        U i ⊆ P (min (36 * a) (min (80 * θ) 4)) (min (80 * θ) 4) 4 z g := by
  classical
  obtain ⟨i₀, p₀, hp₀⟩ := hne
  have hYne (i : Fin n) (hi : (packetPiece θ v Z packets center ℓ i).Nonempty) :
      (Y i).Nonempty := hi.mono (fun _ hp => (href.1 i).2 hp.1)
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
    apply (hUT i (hYne i ⟨p, hp⟩)).trans
    have hh := WangZahlLot.Obl.wz_balanced_cluster_cover.tube_subset_cyl (A := 2)
      hθ hrθ hw (show ‖p‖ < 1 by simpa using hball i (hYne i ⟨p, hp⟩) hpU)
      (hUT i (hYne i ⟨p, hp⟩) hpU)
      (by simpa only [pd, w, show (2 : ℝ) + 2 = 4 by norm_num] using
        (href.piece_direction hθ hv hp).2) hcell
    simpa only [show (2 : ℝ) + 6 = 8 by norm_num] using hh
  obtain ⟨g, _, _, hBg⟩ := slab_carrier_prism ha hθ.le hu (hv i₀)
    ((hflat i₀ (hYne i₀ ⟨p₀, hp₀⟩)).trans (by linarith))
    (hflat i₀ (hYne i₀ ⟨p₀, hp₀⟩)) ((href.piece_direction hθ hv hp₀).2)
    hp₀B (iUnion_subset fun i => iUnion_subset fun hi => hball i (hYne i hi))
    (iUnion_subset fun i => iUnion_subset fun hi => hslab i (hYne i hi)) hcar
  exact ⟨p₀, g, fun i hi => (hBU i hi).trans hBg⟩

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
