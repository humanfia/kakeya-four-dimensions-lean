-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.NormalizedPacketFilling.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/NormalizedPacketFilling.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0626 commit e7a7830, NormalizedPacketFilling.lean. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.SecondPacketFilling
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PacketAffineGeometry
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PacketAffineMass

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set Metric MeasureTheory
open WangZahlLot.Obl.wz_broad_grains_initialization
  (PacketRefinement packetPiece packetLabelUniverse)
open WangZahlLot.Obl.wz_measurable_angular_selection (pd)

/-- The whole-label slab geometry supplies every containing box required by
the second filling. The cut keeps half the complete normalized packet mass,
while each occupied output label is dense in its explicit orthogonal prism. -/
theorem normalized_packet_fillings {β t s u h ε vLoss : ℝ}
    (hβ : 0 < β) (hs : 0 < s) (hst : s ≤ t) (hhu : h < u)
    (hgap : 3 * u + s + vLoss < ε) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧ ∀ δ d θ a₀ : ℝ,
      0 < δ → δ ≤ d₀ → δ ≤ d → d ≤ 1 / 100 →
      δ ^ (-t) * d ≤ θ → θ ≤ 1 →
      0 < a₀ → a₀ ≤ 1 / 8 → a₀ ≤ δ ^ (-vLoss) * d →
      ∀ (n : ℕ) (x ν : Fin n → V) (Body Y Z : Fin n → Set V)
        (packets : V → Finset (Finset (Fin n))) (center : V → Finset (Fin n) → Fin n),
      PacketRefinement β δ θ ν Y Z packets center → (∀ i, ‖ν i‖ = 1) →
      (∀ i, Y i ⊆ Body i) → ∀ f : V ≃ᵃ[ℝ] V,
      (∀ i, (Y i).Nonempty → f '' Body i ⊆ T d (x i) (ν i)) →
      (∀ i, (Y i).Nonempty → f '' Body i ⊆ ball (0 : V) 1) →
      ∀ (normal : V) (offset : ℝ), ‖normal‖ = 1 →
      (∀ i, (Y i).Nonempty → f '' Body i ⊆ {p | |inner ℝ normal p - offset| ≤ a₀ / 2}) →
      (∀ i, (Y i).Nonempty → |inner ℝ normal (ν i)| ≤ 4 * a₀) →
      ∀ S : Finset (Fin n), (∀ i, i ∉ S → Z i = ∅) →
      O (δ ^ h * S.card * d ^ 2) ≤ ∑ i, μ (f '' Z i) →
      ∃ (z : (packetLabelUniverse θ x ν) → V)
        (e : (packetLabelUniverse θ x ν) → V ≃ₗᵢ[ℝ] V)
        (W : (packetLabelUniverse θ x ν) → Fin n → Set V),
      let A₀ := min (36 * a₀) (min (80 * θ) 4)
      let B₀ := min (80 * θ) 4
      let Piece := fun (k : packetLabelUniverse θ x ν) i =>
        packetPiece θ ν (fun i => f '' Z i) (fun p => packets (f.symm p))
          (fun p Q => center (f.symm p) Q) k i
      (∀ (k : packetLabelUniverse θ x ν) i, (affinePacketPiece f θ ν Z packets center k i).Nonempty →
        f '' Body i ⊆ P A₀ B₀ 4 (z k) (e k)) ∧
      (∀ k i, MeasurableSet (W k i) ∧ W k i ⊆ Piece k i) ∧
      (∀ k i, W k i ⊆ P A₀ B₀ 4 (z k) (e k)) ∧
      (1 / 2 : ENNReal) * (∑ i, μ (f '' Z i)) ≤ ∑ k, ∑ i, μ (W k i) ∧
      (∀ k i, (W k i).Nonempty → O (δ ^ u * d ^ 2) ≤ μ (W k i)) ∧
      (∀ k p, p ∈ ⋃ i, W k i → q n {i | p ∈ Piece k i} ≤ 4 * q n {i | p ∈ W k i}) ∧
      (∀ k p u' r, d ≤ r →
        q n {i | p ∈ W k i ∧ pd (ν i) u' ≤ r} ≤
          8 * (r / θ) ^ β * q n {i | p ∈ W k i}) ∧
      ∀ k, (⋃ i, W k i).Nonempty →
        O (δ ^ ε) * μ (P A₀ B₀ 4 (z k) (e k)) ≤ μ (⋃ i, W k i) := by
  classical
  obtain ⟨d₀, hd₀, hd₀1, Hfill⟩ := second_packet_fillings_width_uniform
    (L := 2) (C := 11520) hβ hs hst hhu hgap (by norm_num) (by norm_num)
  refine ⟨d₀, hd₀, hd₀1, ?_⟩
  intro δ d θ a₀ hδ hδ0 hδd hd1 hgrow hθ1 ha₀ ha₀8 hawidth
    n x ν Body Y Z packets center hpack hν hYBody f hBT hBB normal offset hnormal hslab hflat
    S hzero hmass
  have hd : 0 < d := hδ.trans_le hδd
  have hθ : 0 < θ := (mul_pos (Real.rpow_pos_of_pos hδ _) hd).trans_le hgrow
  have hδ1 : δ ≤ 1 := (hδ0.trans hd₀1).trans (by norm_num)
  have hdθ : d ≤ θ := by
    have hh : 1 ≤ δ ^ (-t) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
    exact (show d ≤ δ ^ (-t) * d by nlinarith).trans hgrow
  let Λ := packetLabelUniverse θ x ν
  let A₀ := min (36 * a₀) (min (80 * θ) 4)
  let B₀ := min (80 * θ) 4
  have hgeo (k : Λ) : ∃ (z : V) (e : V ≃ₗᵢ[ℝ] V),
      ∀ i, (affinePacketPiece f θ ν Z packets center k i).Nonempty →
        f '' Body i ⊆ P A₀ B₀ 4 z e := by
    by_cases hk : ∃ i, (affinePacketPiece f θ ν Z packets center k i).Nonempty
    · obtain ⟨z, e, hbox, _⟩ := affine_packet_piece_prism
        (packet_refinement_radius_mono hpack hδd) ha₀ ha₀8 hθ hdθ hν hYBody f
        hBT hBB normal hnormal hslab hflat k hk
      exact ⟨z, e, hbox⟩
    · exact ⟨0, LinearIsometryEquiv.refl ℝ V, fun i hi => (hk ⟨i, hi⟩).elim⟩
  choose z e hbox using hgeo
  have hZT (i : Fin n) : f '' Z i ⊆ T d (x i) (ν i) := by
    rintro _ ⟨p, hp, rfl⟩
    exact hBT i ⟨p, (hpack.1 i).2 hp⟩ ⟨p, hYBody i ((hpack.1 i).2 hp), rfl⟩
  have hZball (i : Fin n) : f '' Z i ⊆ ball (0 : V) 1 := by
    rintro _ ⟨p, hp, rfl⟩
    exact hBB i ⟨p, (hpack.1 i).2 hp⟩ ⟨p, hYBody i ((hpack.1 i).2 hp), rfl⟩
  let Piece := fun (k : Λ) i =>
    packetPiece θ ν (fun i => f '' Z i) (fun p => packets (f.symm p))
      (fun p Q => center (f.symm p) Q) k i
  have hPieceBody (k : Λ) (i : Fin n) : Piece k i ⊆ P A₀ B₀ 4 (z k) (e k) := by
    intro p hp
    have hne : (affinePacketPiece f θ ν Z packets center k i).Nonempty :=
      ⟨f.symm p, by simpa only [affinePacketPiece, mem_preimage, f.apply_symm_apply] using hp⟩
    have hi : p ∈ f '' Body i := (image_mono ((hpack.1 i).2.trans (hYBody i))) hp.1
    exact hbox k i hne hi
  have hvol (k : Λ) : μ (P A₀ B₀ 4 (z k) (e k)) ≤
      O (11520 * δ ^ (-vLoss) * d * θ) := by
    calc
      _ ≤ O (11520 * a₀ * θ) := (packet_prism_dimensions_volume ha₀ hθ (z k) (e k)).2.2.2
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by
        have hh := mul_le_mul_of_nonneg_right hawidth (show 0 ≤ 11520 * θ by positivity)
        nlinarith)
  obtain ⟨W, hW, hWbox, hkeep, hrows, hcounts, hbroad, hdense⟩ :=
    Hfill δ d θ hδ hδ0 hδd hd1 (by linarith) hgrow hθ1 n x ν
      (fun i => f '' Y i) (fun i => f '' Z i) (fun p => packets (f.symm p))
      (fun p Q => center (f.symm p) Q) (packet_refinement_affine_image hpack f) hν hZT
      S (fun i hi => by rw [hzero i hi, image_empty]) hmass (fun _ => 0)
      (fun k => P A₀ B₀ 4 (z k) (e k))
      (fun k i => by simpa using (show Piece k i ⊆ ball (0 : V) 1 from fun p hp => hZball i hp.1))
      hPieceBody hvol
  exact ⟨z, e, W, hbox, hW, hWbox, hkeep, hrows, hcounts, hbroad, hdense⟩

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
