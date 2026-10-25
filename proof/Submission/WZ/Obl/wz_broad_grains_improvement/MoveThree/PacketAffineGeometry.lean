-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.PacketAffineGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/PacketAffineGeometry.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0626 commit e7a7830, PacketAffineGeometry.lean. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PacketAffine
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PacketPrismSupported
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PrismGeometry

noncomputable section
namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_broad_grains_initialization
  (PacketRefinement PacketLabel packetPiece)

/-- The common packet enclosure has positive ordered widths and volume
bounded by the thin slab width times the angular scale. -/
theorem packet_prism_dimensions_volume {a θ : ℝ} (ha : 0 < a) (hθ : 0 < θ)
    (z : V) (e : V ≃ₗᵢ[ℝ] V) :
    0 < min (36*a) (min (80*θ) 4) ∧
    min (36*a) (min (80*θ) 4) ≤ min (80*θ) 4 ∧ min (80*θ) 4 ≤ 4 ∧
    μ (P (min (36*a) (min (80*θ) 4)) (min (80*θ) 4) 4 z e) ≤ O (11520*a*θ) := by
  have hA : 0 < min (36*a) (min (80*θ) 4) := by positivity
  have hB : 0 < min (80*θ) 4 := by positivity
  refine ⟨hA, min_le_right _ _, min_le_right _ _, ?_⟩
  have hvol : μ (P (min (36*a) (min (80*θ) 4)) (min (80*θ) 4) 4 z e) =
      O (min (36*a) (min (80*θ) 4) * min (80*θ) 4 * 4) :=
    WangZahlLot.Obl.wz_clustered_cover_volume_gain.frozen_prism_volume
      hA.le hB.le (by norm_num) z e
  rw [hvol]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (36*a)*(80*θ)*4 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (min_le_left _ _) (min_le_left _ _) hB.le (by positivity)) (by norm_num)
    _ = _ := by ring

/-- Form labels after transporting the packet points to the first normalized
coordinates. Every whole old body with an occupied pulled-back label lies in
one common prism of volume at most `11520 a theta`. -/
theorem affine_packet_piece_prism {n : ℕ} {β r θ a t : ℝ}
    {U Y Z : Fin n → Set V} {x v : Fin n → V}
    {packets : V → Finset (Finset (Fin n))} {center : V → Finset (Fin n) → Fin n}
    (href : PacketRefinement β r θ v Y Z packets center)
    (ha : 0 < a) (ha8 : a ≤ 1/8) (hθ : 0 < θ) (hrθ : r ≤ θ)
    (hv : ∀ i, ‖v i‖ = 1) (hYU : ∀ i, Y i ⊆ U i)
    (f : V ≃ᵃ[ℝ] V)
    (hUT : ∀ i, (Y i).Nonempty → f '' U i ⊆ T r (x i) (v i))
    (hball : ∀ i, (Y i).Nonempty → f '' U i ⊆ ball (0 : V) 1)
    (u : V) (hu : ‖u‖ = 1)
    (hslab : ∀ i, (Y i).Nonempty → f '' U i ⊆ {p | |inner ℝ u p - t| ≤ a/2})
    (hflat : ∀ i, (Y i).Nonempty → |inner ℝ u (v i)| ≤ 4*a)
    (label : PacketLabel)
    (hne : ∃ i, (affinePacketPiece f θ v Z packets center label i).Nonempty) :
    ∃ (z : V) (e : V ≃ₗᵢ[ℝ] V),
      (∀ i, (affinePacketPiece f θ v Z packets center label i).Nonempty →
        f '' U i ⊆ P (min (36*a) (min (80*θ) 4)) (min (80*θ) 4) 4 z e) ∧
      μ (P (min (36*a) (min (80*θ) 4)) (min (80*θ) 4) 4 z e) ≤ O (11520*a*θ) := by
  have hne' : ∃ i, (packetPiece θ v (fun i => f '' Z i)
      (fun p => packets (f.symm p)) (fun p W => center (f.symm p) W) label i).Nonempty := by
    obtain ⟨i, p, hp⟩ := hne
    exact ⟨i, f p, hp⟩
  obtain ⟨z, e, hbox⟩ := packet_piece_prism_supported (packet_refinement_affine_image href f)
    ha.le ha8 hθ hrθ hv (fun i => image_mono (hYU i))
    (fun i hi => hUT i (image_nonempty.mp hi))
    (fun i hi => hball i (image_nonempty.mp hi)) u hu
    (fun i hi => hslab i (image_nonempty.mp hi))
    (fun i hi => hflat i (image_nonempty.mp hi)) label hne'
  refine ⟨z, e, ?_, (packet_prism_dimensions_volume ha hθ z e).2.2.2⟩
  intro i hi
  apply hbox i
  obtain ⟨p, hp⟩ := hi
  exact ⟨f p, hp⟩

/-- The physical overlap-to-width argument also applies to labels formed in
normalized coordinates. No estimate for angular distortion is used here. -/
theorem HB_affine_packet_piece_width_growth {β q₀ t : ℝ}
    (hβ : 0 ≤ β) (ht : 0 < t) (hmargin : β+3*t < q₀) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d₀ →
      ∀ {h ρ a c b g m A B ℓ θ : ℝ} {n N L : ℕ}
        {x v : Fin n → V} {S : Finset (Fin n)} {Z : Fin n → Set V}
        {y w : Fin N → V} {f₀ : Fin n → Fin N}
        {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V}
        {Hs H Z' : Fin L → Set V} {γ : Fin L → Fin N} {ν : Fin L → V}
        {packets : V → Finset (Finset (Fin L))}
        {center : V → Finset (Fin L) → Fin L},
      0 < ρ → 0 ≤ A → A ≤ B → δ ≤ θ →
      (∀ k, ‖w k‖ = 1) → X ρ N y w →
      GrainWitnesses δ h n x v S Z ρ N y w f₀ a c b g L z e Hs γ m →
      (∀ j, H j ⊆ Hs j) →
      (∀ p ∈ ⋃ j, H j, δ^(-q₀) < q L {j | p ∈ H j}) →
      PacketRefinement β δ θ ν H Z' packets center →
      ∀ (f : V ≃ᵃ[ℝ] V) (label : PacketLabel) (z' : V) (g' : V ≃ₗᵢ[ℝ] V),
        (∀ j, (affinePacketPiece f θ ν Z' packets center label j).Nonempty →
          P a (ρ*c) c (z j) (e j) ⊆ P A B ℓ z' g') →
        (⋃ j, affinePacketPiece f θ ν Z' packets center label j).Nonempty →
        δ^(-t)*ρ*c ≤ B := by
  classical
  obtain ⟨d₀, hd₀, hd₀1, Hgrow⟩ := packet_container_width_growth hβ ht hmargin
  refine ⟨d₀, hd₀, hd₀1, ?_⟩
  intro δ hδ hδd h ρ a c b g m A B ℓ θ n N L x v S Z y w f₀ z e Hs H Z' γ ν
    packets center hρ hA hAB hδθ hw hX hHB hsub hhigh hpack f label z' g' hbody hne
  have ha : 0 < a := hδ.trans_le hHB.1
  have hb : 0 < ρ*c := ha.trans_le hHB.2.1
  have hc : 0 < c := hb.trans_le hHB.2.2.1
  let Q := Finset.univ.filter
    (fun j => (affinePacketPiece f θ ν Z' packets center label j).Nonempty)
  obtain ⟨p, W, hW, hWp⟩ := affine_packet_piece_contains_packet hpack f label hne
  exact Hgrow δ hδ hδd hρ ha.le hb.le hc hA hAB hδθ hw hX
    (fun j => (hHB.2.2.2.2.1 j).2.1.trans (hHB.2.2.2.2.1 j).2.2.1)
    hHB.2.2.2.2.2.1 (fun j => (hHB.2.2.2.2.1 j).2.2.2)
    hsub hhigh hpack Q z' g'
    (fun j hj => hbody j (Finset.mem_filter.mp hj).2)
    ⟨p, W, hW, fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨p, hWp j hj⟩⟩⟩

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
