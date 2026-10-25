-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.FilledPacketPrisms.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/FilledPacketPrisms.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0626 5604560, FilledPacketPrisms.lean.
This is workspace collaboration code; existing local and accepted dependencies are imported. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PacketAffineGeometry
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PhysicalEnclosure

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_broad_grains_initialization (PacketRefinement PacketLabel)

/-- A dense filled label yields a physical prism containing all its original
whole grains. Its middle width grows, and its density loses only the explicit
enclosure constant. The point set used for filling may have been refined. -/
theorem HB_filled_affine_label_prism {β q₀ jump : ℝ}
    (hβ : 0 ≤ β) (hjump : 0 < jump) (hgap : β + 3 * jump < q₀) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d₀ →
      ∀ {h ρ a c b g m A₀ B₀ C₀ K D θ : ℝ} {n N L : ℕ}
        {x v : Fin n → V} {S : Finset (Fin n)} {Z : Fin n → Set V}
        {y w : Fin N → V} {f₀ : Fin n → Fin N}
        {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V}
        {Hs H Zp : Fin L → Set V} {γ : Fin L → Fin N} {ν : Fin L → V}
        {packets : V → Finset (Finset (Fin L))}
        {center : V → Finset (Fin L) → Fin L},
      0 < ρ → δ ≤ θ → (∀ k, ‖w k‖ = 1) → X ρ N y w →
      GrainWitnesses δ h n x v S Z ρ N y w f₀ a c b g L z e Hs γ m →
      (∀ j, H j ⊆ Hs j) →
      (∀ p ∈ ⋃ j, H j, δ ^ (-q₀) < q L {j | p ∈ H j}) →
      PacketRefinement β δ θ ν H Zp packets center →
      0 ≤ A₀ → A₀ ≤ B₀ → B₀ ≤ C₀ → 0 < C₀ → 0 < K → 0 ≤ D →
      ∀ (f : V ≃ᵃ[ℝ] V) (label : PacketLabel) (z₀ : V) (e₀ : V ≃ₗᵢ[ℝ] V)
        (W : Set V),
      (∀ p q, dist (f.symm p) (f.symm q) ≤ (K * c) * dist p q) →
      (∀ j, (affinePacketPiece f θ ν Zp packets center label j).Nonempty →
        f '' P a (ρ * c) c (z j) (e j) ⊆ P A₀ B₀ C₀ z₀ e₀) →
      (⋃ j, affinePacketPiece f θ ν Zp packets center label j).Nonempty →
      MeasurableSet W → W ⊆ P A₀ B₀ C₀ z₀ e₀ →
      O D * μ (P A₀ B₀ C₀ z₀ e₀) ≤ μ W →
      ∃ (A B : ℝ) (z' : V) (e' : V ≃ₗᵢ[ℝ] V),
        a ≤ A ∧ A ≤ B ∧ B ≤ 8 * K * C₀ * c ∧ δ ^ (-jump) * ρ * c ≤ B ∧
        (∀ j, (affinePacketPiece f θ ν Zp packets center label j).Nonempty →
          P a (ρ * c) c (z j) (e j) ⊆ P A B (8 * K * C₀ * c) z' e') ∧
        MeasurableSet (f.symm '' W) ∧ f.symm '' W ⊆ P A B (8 * K * C₀ * c) z' e' ∧
        O (D / (6912 * K * C₀)) * μ (P A B (8 * K * C₀ * c) z' e') ≤ μ (f.symm '' W) := by
  obtain ⟨d₀, hd₀, hd₀1, Hgrow⟩ := HB_affine_packet_piece_width_growth hβ hjump hgap
  refine ⟨d₀, hd₀, hd₀1, ?_⟩
  intro δ hδ hδd h ρ a c b g m A₀ B₀ C₀ K D θ n N L x v S Z y w f₀ z e Hs H Zp γ ν
    packets center hρ hδθ hw hX hHB hsub hhigh hpack hA₀ hAB₀ hBC₀ hC₀ hK hD
    f label z₀ e₀ W hInv hwhole hne hWm hW hden
  have ha : 0 < a := hδ.trans_le hHB.1
  obtain ⟨j₀, hj₀⟩ := nonempty_iUnion.mp hne
  obtain ⟨A, B, z', e', haA, hAB, hB, hbox, hWbox, _, hDbox⟩ :=
    inverse_dense_prism_enclosure ha hHB.2.1 hHB.2.2.1 hA₀ hAB₀ hBC₀ hC₀ hK hD
      (z j₀) z₀ (e j₀) e₀ f W hInv (hwhole j₀ hj₀) hW hden
  have hbody (j : Fin L) (hj : (affinePacketPiece f θ ν Zp packets center label j).Nonempty) :
      P a (ρ * c) c (z j) (e j) ⊆ P A B (8 * K * C₀ * c) z' e' := by
    intro p hp
    exact hbox ⟨f p, hwhole j hj (mem_image_of_mem f hp), f.symm_apply_apply p⟩
  have hgrow := Hgrow δ hδ hδd hρ (ha.le.trans haA) hAB hδθ hw hX hHB
    hsub hhigh hpack f label z' e' hbody hne
  exact ⟨A, B, z', e', haA, hAB, hB, hgrow, hbody,
    f.symm.toContinuousAffineEquiv.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr hWm,
    hWbox, hDbox⟩

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
