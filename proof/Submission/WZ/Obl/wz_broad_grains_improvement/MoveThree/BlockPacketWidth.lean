-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.BlockPacketWidth.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/BlockPacketWidth.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.ClippedCarrierFilling

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_separated_cover_refinement (enumerate enumerate_injective)

noncomputable section

/-- The old coarse geometry still counts a block's injectively indexed
grains. Thus every occupied clipped packet forces physical middle-width
growth, without asserting a full grain witness for the restricted block. -/
theorem block_clipped_packet_width_uniform {β₂ q₀ widthJump : ℝ}
    (hβ : 0 ≤ β₂) (hjump : 0 < widthJump) (hgap : β₂ + 3 * widthJump < q₀) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 ∧ ∀ δ : ℝ,
      ∀ hδ : 0 < δ, δ ≤ d₀ →
      ∀ {σ ω ζ ε b ρ c β τ den k Cnet e u t loss density jump τ₂ : ℝ}
        {p n d : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}
        {D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y}
        {R : Finset (Fin D.L)} {G : D.NormalizedBlock R}
        {A : BlockAngularData D R G β τ} {hk : 0 < k}
        {F : BlockFirstFilling A (δ ^ t / firstFillingMassConstant) den k hk}
        {N : BlockNetData (σ := σ) F Cnet e (δ ^ (-u)) (δ ^ (-ζ / 2)) d}
        {l : Fin A.labels.card} {j : Fin (N.N l)}
        {B : PhysicalCarrierBox N loss density l j}
        (Q : ClippedCarrierAngularData B hδ β₂ q₀ jump τ₂),
      ∀ (a b L : ℝ) (z : V) (frame : V ≃ₗᵢ[ℝ] V) (label : Q.labels),
        0 ≤ a → a ≤ b →
        (∀ i, (affinePacketPiece (B.map hδ) Q.scale (B.direction hδ)
          Q.shade Q.packets Q.center label i).Nonempty →
          P D.a (ρ * c) c (D.z (enumerate R i)) (D.e (enumerate R i)) ⊆ P a b L z frame) →
        (⋃ i, affinePacketPiece (B.map hδ) Q.scale (B.direction hδ)
          Q.shade Q.packets Q.center label i).Nonempty →
        δ ^ (-widthJump) * ρ * c ≤ b := by
  classical
  obtain ⟨d₀, hd₀, hd₀1, Hgrow⟩ := packet_container_width_growth hβ hjump hgap
  refine ⟨d₀, hd₀, hd₀1, ?_⟩
  intro δ hδ hδ0 σ ω ζ ε b₀ ρ c β τ den k Cnet e u t loss density jump τ₂
    p n d x v Y D R G A hk F N l j B Q a b L z frame label ha hab hbody hne
  obtain ⟨haOld, hρ, _, hc, _⟩ := D.dimensions hδ
  let S := Finset.univ.filter (fun i =>
    (affinePacketPiece (B.map hδ) Q.scale (B.direction hδ)
      Q.shade Q.packets Q.center label i).Nonempty)
  obtain ⟨q, W, hW, hWp⟩ := affine_packet_piece_contains_packet Q.refinement (B.map hδ) label hne
  exact Hgrow δ hδ hδ0 hρ haOld.le (mul_pos hρ hc).le hc ha hab Q.lower
    D.cover.2.2.1 D.cover.2.2.2.2.2.2.2.1
    (fun i => (D.grains.2.2.2.2.1 (enumerate R i)).2.1.trans
      (D.grains.2.2.2.2.1 (enumerate R i)).2.2.1)
    (fun i i' hi hh => D.grains.2.2.2.2.2.1 _ _ ((enumerate_injective R).ne hi) hh)
    (fun i => (D.grains.2.2.2.2.1 (enumerate R i)).2.2.2)
    (fun i => inter_subset_left.trans ((Q.input_subset i).trans (N.physicalPiece_subset l j i)))
    Q.high Q.refinement S z frame
    (fun i hi => hbody i (Finset.mem_filter.mp hi).2)
    ⟨q, W, hW, fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨q, hWp i hi⟩⟩⟩

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
