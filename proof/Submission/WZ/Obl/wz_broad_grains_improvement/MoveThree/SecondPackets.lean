-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.SecondPackets.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/SecondPackets.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0626 commit be976b9, SecondPackets.lean. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.HighBlockOverlap
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.GrowingAngularPackets
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PhysicalWidth
import Submission.WZ.Obl.wz_broad_grains_initialization.PacketLabels

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_measurable_angular_selection (pd)
open WangZahlLot.Obl.wz_broad_grains_initialization (PacketRefinement packetPiece PacketLabel)

/-- An overfull carrier yields growing angular packets after one common
overlap cut. The retained mass is measured against the original components. -/
theorem high_carrier_growing_packets {C β q₀ t τ : ℝ}
    (hC : 0 < C) (hβ : 0 < β) (hβ1 : β ≤ 1) (ht : 0 < t)
    (hmargin : 0 < q₀ - β - 3 * t) (hτ : 0 < τ) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧ ∀ δ ρ : ℝ,
      0 < δ → δ ≤ d₀ → 0 < ρ →
      ∀ (n : ℕ) (v : Fin n → V) (H : Fin n → Set V) (U : Set V),
        0 < n → (∀ i, ‖v i‖ = 1) → (∀ i, MeasurableSet (H i)) →
        MeasurableSet U → (∀ i, H i ⊆ U) →
        0 < ∑ i, μ (H i) → (∑ i, μ (H i)) ≠ ⊤ →
        O (δ ^ (-q₀)) * μ U ≤ (1 / 2 : ENNReal) * ∑ i, μ (H i) →
        (∀ p u R, ρ ≤ R → q n {i | p ∈ H i ∧ pd (v i) u ≤ R} ≤ C * (R / ρ) ^ 3) →
        ∃ (D : Set V) (θ : ℝ) (Z : Fin n → Set V)
          (P : V → Finset (Finset (Fin n))) (center : V → Finset (Fin n) → Fin n),
          MeasurableSet D ∧ δ ≤ θ ∧ θ ≤ 1 ∧ δ ^ (-t) * ρ ≤ θ ∧
          PacketRefinement β δ θ v (fun i => H i ∩ D) Z P center ∧
          O (δ ^ τ / 2) * ∑ i, μ (H i) ≤ ∑ i, μ (Z i) ∧
          ∀ p ∈ ⋃ i, H i ∩ D, δ ^ (-q₀) < q n {i | p ∈ H i ∩ D} := by
  obtain ⟨d₀, hd₀, hd₀1, Hpacket⟩ :=
    measurable_growing_packets_of_cap_count hC hβ hβ1 ht hmargin hτ
  refine ⟨d₀, hd₀, hd₀1, ?_⟩
  intro δ ρ hδ hδd hρ n v H U hn hv hHm hUm hsub hpos hfin hbudget hcount
  obtain ⟨D, hDm, hmass, hhigh⟩ := high_block_overlap H U
    (Real.rpow_nonneg hδ.le _) hHm hUm hsub hfin hbudget
  have hcutpos : 0 < ∑ i, μ (H i ∩ D) :=
    (ENNReal.mul_pos (by norm_num : (1 / 2 : ENNReal) ≠ 0) hpos.ne').trans_le hmass
  have hcutcount (p u : V) (R : ℝ) (hR : ρ ≤ R) :
      q n {i | p ∈ H i ∩ D ∧ pd (v i) u ≤ R} ≤ C * (R / ρ) ^ 3 := by
    apply le_trans ?_ (hcount p u R hR)
    exact Nat.cast_le.mpr (Set.ncard_le_ncard
      (fun i hi => ⟨hi.1.1, hi.2⟩) (Set.toFinite _))
  obtain ⟨θ, Z, P, center, hδθ, hθ1, hgrow, hpack, hret⟩ :=
    Hpacket δ ρ hδ hδd hρ n v (fun i => H i ∩ D) hn hv
      (fun i => (hHm i).inter hDm) hcutpos (fun p hp => (hhigh p hp).1)
      hcutcount
  refine ⟨D, θ, Z, P, center, hDm, hδθ, hθ1, hgrow, hpack, ?_,
    fun p hp => (hhigh p hp).1⟩
  calc
    _ = O (δ ^ τ) * ((1 / 2 : ENNReal) * ∑ i, μ (H i)) := by
      dsimp only [O]
      rw [div_eq_mul_inv, ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le τ)]
      rw [ENNReal.ofReal_inv_of_pos (by norm_num : 0 < (2 : ℝ))]
      norm_num [mul_assoc]
    _ ≤ O (δ ^ τ) * ∑ i, μ (H i ∩ D) := mul_le_mul' le_rfl hmass
    _ ≤ _ := hret

/-- A dense angular packet preserves enough of the original overlap to
force growth of any physical prism containing all of its whole grains.
The packet directions may have been chosen after an affine normalization. -/
theorem packet_container_width_growth {β q₀ t : ℝ}
    (hβ : 0 ≤ β) (ht : 0 < t) (hmargin : β + 3 * t < q₀) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d₀ →
      ∀ {ρ a b c A B ℓ θ : ℝ} {N L : ℕ}
        {y w : Fin N → V} {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V}
        {Hs H Z : Fin L → Set V} {γ : Fin L → Fin N} {ν : Fin L → V}
        {packets : V → Finset (Finset (Fin L))} {center : V → Finset (Fin L) → Fin L},
      0 < ρ → 0 ≤ a → 0 ≤ b → 0 < c → 0 ≤ A → A ≤ B → δ ≤ θ →
      (∀ k, ‖w k‖ = 1) → X ρ N y w →
      (∀ j, Hs j ⊆ T ρ (y (γ j)) (w (γ j))) →
      (∀ j j', j ≠ j' → γ j = γ j' → Disjoint (Hs j) (Hs j')) →
      (∀ j, (e j (w (γ j)) 0) ^ 2 + (e j (w (γ j)) 1) ^ 2 ≤ (10 * ρ) ^ 2) →
      (∀ j, H j ⊆ Hs j) →
      (∀ p ∈ ⋃ j, H j, δ ^ (-q₀) < q L {j | p ∈ H j}) →
      PacketRefinement β δ θ ν H Z packets center →
      ∀ (Q : Finset (Fin L)) (z' : V) (g : V ≃ₗᵢ[ℝ] V),
        (∀ j ∈ Q, P a b c (z j) (e j) ⊆ P A B ℓ z' g) →
        (∃ p W, W ∈ packets p ∧ W ⊆ Q) → δ ^ (-t) * ρ * c ≤ B := by
  classical
  obtain ⟨C₀, hC₀, Hcount⟩ := grain_container_overlap_count
  obtain ⟨d, hd, Hsmall⟩ := WangZahlLot.Obl.wz_move_two_long_grains_gain.small_rpow
    (by linarith : 0 < q₀ - β - 3 * t) (K := 1 / (16 * C₀)) (by positivity)
  refine ⟨min d 1, by positivity, min_le_right _ _, ?_⟩
  intro δ hδ hδd ρ a b c A B ℓ θ N L y w z e Hs H Z γ ν packets center
    hρ ha hb hc hA hAB hδθ hw hX hHT hdisj halign hsub hhigh hpack Q z' g hbody
    ⟨p, W, hW, hWQ⟩
  have hlarge := ((hpack.2.2.2 p).2.2 W hW).2.2.1
  have hWne := ((hpack.2.2.2 p).2.2 W hW).1
  have hWH (j) (hj : j ∈ W) : p ∈ H j := by
    apply (hpack.1 j).2
    have hh : j ∈ ((packets p).biUnion id : Set (Fin L)) := Finset.mem_biUnion.mpr ⟨W, hW, hj⟩
    rwa [(hpack.2.2.2 p).2.1] at hh
  obtain ⟨j₀, hj₀⟩ := hWne
  have hpoint := hhigh p (mem_iUnion.mpr ⟨j₀, hWH j₀ hj₀⟩)
  have hWcount : (W.card : ℝ) ≤ q L {j | j ∈ Q ∧ p ∈ Hs j} := by
    change (W.card : ℝ) ≤ (({j | j ∈ Q ∧ p ∈ Hs j} : Set (Fin L)).ncard : ℝ)
    rw [← Set.ncard_coe_finset]
    exact Nat.cast_le.mpr (Set.ncard_le_ncard
      (fun j hj => ⟨hWQ hj, hsub j (hWH j hj)⟩) (Set.toFinite _))
  have hhigh' : δ ^ (-(q₀ - β)) < 2 * q L {j | j ∈ Q ∧ p ∈ Hs j} := by
    have hθβ := Real.rpow_le_rpow hδ.le hδθ hβ
    have hp : 0 < δ ^ β := Real.rpow_pos_of_pos hδ β
    have hh := mul_lt_mul_of_pos_right hpoint hp
    have hh' := mul_le_mul_of_nonneg_left hθβ
      (show 0 ≤ q L {j | p ∈ H j} / 2 by positivity)
    change (q L {j | p ∈ H j} / 2) * θ ^ β ≤ (W.card : ℝ) at hlarge
    have he : δ ^ (-q₀) * δ ^ β = δ ^ (-(q₀ - β)) := by
      rw [← Real.rpow_add hδ]
      congr 1
      ring
    rw [he] at hh
    nlinarith
  have hbudget : 8 * (2 * C₀) * δ ^ ((q₀ - β) - 3 * t) ≤ 1 := by
    have hs := Hsmall δ hδ (hδd.trans (min_le_left _ _))
    have hh := (le_div_iff₀ (by positivity : 0 < 16 * C₀)).mp hs
    nlinarith
  exact physical_width_growth_of_overlap (by positivity : 0 < 2 * C₀) hδ
    (hδd.trans (min_le_right _ _)) hρ hc (hA.trans hAB) ht.le hbudget
    (by nlinarith [Hcount hρ ha hb hc hA hAB hw hX hHT hdisj halign Q z' g hbody p]) hhigh'

/-- A nonempty labelled piece contains every incidence of one of the
selected packets at the same point. -/
theorem packet_piece_contains_packet {L : ℕ} {β δ θ : ℝ} {ν : Fin L → V}
    {H Z : Fin L → Set V} {packets : V → Finset (Finset (Fin L))}
    {center : V → Finset (Fin L) → Fin L}
    (hpack : PacketRefinement β δ θ ν H Z packets center) (label : PacketLabel)
    (hne : (⋃ j, packetPiece θ ν Z packets center label j).Nonempty) :
    ∃ p W, W ∈ packets p ∧
      ∀ j ∈ W, p ∈ packetPiece θ ν Z packets center label j := by
  obtain ⟨j₀, p, hp⟩ := Set.nonempty_iUnion.mp hne
  obtain ⟨hpZ, W, hW, hjW, hlabel⟩ := hp
  refine ⟨p, W, hW, ?_⟩
  intro i hi
  refine ⟨?_, W, hW, hi, hlabel⟩
  have hh : i ∈ ((packets p).biUnion id : Set (Fin L)) :=
    Finset.mem_biUnion.mpr ⟨W, hW, hi⟩
  rwa [(hpack.2.2.2 p).2.1] at hh

/-- Every occupied second-packet label forces a width increase for its
physical enclosure. This uses only the exact old grain geometry and the
pre-packet overlap, with no distortion bound for the packet directions. -/
theorem HB_packet_piece_width_growth {β q₀ t : ℝ}
    (hβ : 0 ≤ β) (ht : 0 < t) (hmargin : β + 3 * t < q₀) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d₀ →
      ∀ {h ρ a c b g m A B ℓ θ : ℝ} {n N L : ℕ}
        {x v : Fin n → V} {S : Finset (Fin n)} {Z : Fin n → Set V}
        {y w : Fin N → V} {f : Fin n → Fin N}
        {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V}
        {Hs H Z' : Fin L → Set V} {γ : Fin L → Fin N} {ν : Fin L → V}
        {packets : V → Finset (Finset (Fin L))}
        {center : V → Finset (Fin L) → Fin L},
      0 < ρ → 0 ≤ A → A ≤ B → δ ≤ θ →
      (∀ k, ‖w k‖ = 1) → X ρ N y w →
      GrainWitnesses δ h n x v S Z ρ N y w f a c b g L z e Hs γ m →
      (∀ j, H j ⊆ Hs j) →
      (∀ p ∈ ⋃ j, H j, δ ^ (-q₀) < q L {j | p ∈ H j}) →
      PacketRefinement β δ θ ν H Z' packets center →
      ∀ (label : PacketLabel) (z' : V) (g' : V ≃ₗᵢ[ℝ] V),
        (∀ j, (packetPiece θ ν Z' packets center label j).Nonempty →
          P a (ρ * c) c (z j) (e j) ⊆ P A B ℓ z' g') →
        (⋃ j, packetPiece θ ν Z' packets center label j).Nonempty →
        δ ^ (-t) * ρ * c ≤ B := by
  classical
  obtain ⟨d₀, hd₀, hd₀1, Hgrow⟩ := packet_container_width_growth hβ ht hmargin
  refine ⟨d₀, hd₀, hd₀1, ?_⟩
  intro δ hδ hδd h ρ a c b g m A B ℓ θ n N L x v S Z y w f z e Hs H Z' γ ν
    packets center hρ hA hAB hδθ hw hX hHB hsub hhigh hpack label z' g' hbody hne
  have ha : 0 < a := hδ.trans_le hHB.1
  have hb : 0 < ρ * c := ha.trans_le hHB.2.1
  have hc : 0 < c := hb.trans_le hHB.2.2.1
  let Q : Finset (Fin L) := Finset.univ.filter
    (fun j => (packetPiece θ ν Z' packets center label j).Nonempty)
  obtain ⟨p, W, hW, hWpiece⟩ := packet_piece_contains_packet hpack label hne
  exact Hgrow δ hδ hδd hρ ha.le hb.le hc hA hAB hδθ hw hX
    (fun j => (hHB.2.2.2.2.1 j).2.1.trans (hHB.2.2.2.2.1 j).2.2.1)
    hHB.2.2.2.2.2.1 (fun j => (hHB.2.2.2.2.1 j).2.2.2)
    hsub hhigh hpack Q z' g'
    (fun j hj => hbody j (Finset.mem_filter.mp hj).2)
    ⟨p, W, hW, fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨p, hWpiece j hj⟩⟩⟩

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
