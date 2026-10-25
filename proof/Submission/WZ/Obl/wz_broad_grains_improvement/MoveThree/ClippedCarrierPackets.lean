-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.ClippedCarrierPackets.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/ClippedCarrierPackets.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.ClippedNetCarrier
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.NormalizedCapCount
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.SecondPackets

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_separated_cover_refinement (enumerate enumerate_injective)
open WangZahlLot.Obl.wz_broad_grains_initialization (PacketRefinement)
open WangZahlLot.Obl.wz_measurable_angular_selection (pd)

noncomputable section

/-- The clipped directions of an actual physical carrier satisfy the same
uniform cubic cap bound, with counts taken in the original shading. -/
theorem clipped_carrier_cap_count :
    ∃ C : ℝ, 0 < C ∧
      ∀ {σ ω ζ δ ε b ρ c β τ lam den k Cnet e Λ Kc loss density : ℝ} {p n d : ℕ}
        {x v : Fin n → V} {Y : Fin n → Set V}
        {D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y}
        {R : Finset (Fin D.L)} {G : D.NormalizedBlock R}
        {A : BlockAngularData D R G β τ} {hk : 0 < k}
        {F : BlockFirstFilling A lam den k hk}
        {N : BlockNetData (σ := σ) F Cnet e Λ Kc d}
        {l : Fin A.labels.card} {j : Fin (N.N l)}
        (B : PhysicalCarrierBox N loss density l j) (hδ : 0 < δ), l ∈ F.good →
      ∀ z u θ, ρ ≤ θ →
        q R.card {i | z ∈ N.physicalPiece l j i ∧ pd (B.direction hδ i) u ≤ θ} ≤
          C * (θ / ρ) ^ 3 := by
  classical
  obtain ⟨C, hC, H⟩ := HB_normalized_cap_count
  refine ⟨C, hC, ?_⟩
  intro σ ω ζ δ ε b ρ c β τ lam den k Cnet e Λ Kc loss density p n d x v Y
    D R G A hk F N l j B hδ hl z u θ hθ
  let Q := (N.fibre l j).image (enumerate R)
  have hupper (i : Fin D.L) (hi : i ∈ Q) :
      ‖(B.map hδ).linear (WangZahlLot.Obl.wz_clustered_cover_volume_gain.boxAxis (D.e i) 2)‖ ≤ c⁻¹ := by
    obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hi
    exact (B.linear_data hδ hl i' hi').1
  have Hcap := H (D.dimensions hδ).2.1 (D.dimensions hδ).2.2.2.1
    D.cover.2.2.1 D.cover.2.2.2.2.2.2.2.1 D.grains Q (B.map hδ).linear
    (B.inverse_bound hδ) hupper z u θ hθ
  apply le_trans ?_ Hcap
  apply Nat.cast_le.mpr
  rw [← Set.ncard_image_of_injective _ (enumerate_injective R)]
  apply Set.ncard_le_ncard _ (Set.toFinite _)
  rintro i ⟨i', hi', rfl⟩
  change z ∈ N.physicalPiece l j i' ∧ _ at hi'
  have hmem : i' ∈ N.fibre l j := by
    by_contra hh
    rw [N.physicalPiece_outside l j i' hh] at hi'
    exact hi'.1
  exact ⟨Finset.mem_image.mpr ⟨i', hmem, rfl⟩,
    N.physicalPiece_subset l j i' hi'.1, hi'.2⟩

/-- Second angular data with original physical pieces and clipped directions.
The map is fixed for the whole first carrier, so its common frame can later
be used to transfer broadness back to the fine tubes. -/
structure ClippedCarrierAngularData {σ ω ζ δ ε b ρ c β τ den k Cnet e u t loss density : ℝ}
    {p n d : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}
    {D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y}
    {R : Finset (Fin D.L)} {G : D.NormalizedBlock R}
    {A : BlockAngularData D R G β τ} {hk : 0 < k}
    {F : BlockFirstFilling A (δ ^ t / firstFillingMassConstant) den k hk}
    {N : BlockNetData (σ := σ) F Cnet e (δ ^ (-u)) (δ ^ (-ζ / 2)) d}
    {l : Fin A.labels.card} {j : Fin (N.N l)}
    (B : PhysicalCarrierBox N loss density l j) (hδ : 0 < δ)
    (β₂ q₀ jump τ₂ : ℝ) where
  input : Fin R.card → Set V
  input_subset : ∀ i, input i ⊆ N.physicalPiece l j i
  input_measurable : ∀ i, MeasurableSet (input i)
  cut : Set V
  scale : ℝ
  shade : Fin R.card → Set V
  packets : V → Finset (Finset (Fin R.card))
  center : V → Finset (Fin R.card) → Fin R.card
  measurable_cut : MeasurableSet cut
  lower : δ ≤ scale
  upper : scale ≤ 1
  growth : δ ^ (-jump) * ρ ≤ scale
  refinement : PacketRefinement β₂ δ scale (B.direction hδ)
    (fun i => input i ∩ cut) shade packets center
  mass : O (δ ^ τ₂ / 2) * ∑ i, μ (N.physicalPiece l j i) ≤ ∑ i, μ (shade i)
  high : ∀ z ∈ ⋃ i, input i ∩ cut,
    δ ^ (-q₀) < q R.card {i | z ∈ input i ∩ cut}

theorem clipped_carrier_angular_data_uniform {ζ t β₂ q₀ jump τ₂ : ℝ}
    (hβ : 0 < β₂) (hβ1 : β₂ ≤ 1) (hjump : 0 < jump)
    (hcapgap : β₂ + 3 * jump < q₀) (hτ : 0 < τ₂)
    (hmassgap : 0 < ζ / 2 - q₀ - t) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧ ∀ δ : ℝ,
      ∀ hδ : 0 < δ, δ ≤ d₀ →
      ∀ {σ ω ε b ρ c β τ den k Cnet e u loss density : ℝ} {p n d : ℕ}
        {x v : Fin n → V} {Y : Fin n → Set V}
        {D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y}
        {R : Finset (Fin D.L)} {G : D.NormalizedBlock R}
        {A : BlockAngularData D R G β τ} {hk : 0 < k}
        {F : BlockFirstFilling A (δ ^ t / firstFillingMassConstant) den k hk}
        (N : BlockNetData (σ := σ) F Cnet e (δ ^ (-u)) (δ ^ (-ζ / 2)) d),
      ∀ l ∈ N.highLabels, ∀ j : Fin (N.N l),
        ∀ B : PhysicalCarrierBox N loss density l j,
          Nonempty (ClippedCarrierAngularData B hδ β₂ q₀ jump τ₂) := by
  obtain ⟨C, hC, Hcap⟩ := clipped_carrier_cap_count
  obtain ⟨dP, hdP, hdP1, HP⟩ := high_carrier_growing_packets hC hβ hβ1 hjump
    (by linarith : 0 < q₀ - β₂ - 3 * jump) hτ
  have hH : 0 < firstFillingMassConstant := by norm_num [firstFillingMassConstant]
  obtain ⟨dM, hdM, HM⟩ := WangZahlLot.Obl.wz_move_two_long_grains_gain.small_rpow
    hmassgap (K := 16 / firstFillingMassConstant) (by positivity)
  refine ⟨min dP dM, lt_min hdP hdM, (min_le_left _ _).trans hdP1, ?_⟩
  intro δ hδ hδ0 σ ω ε b ρ c β τ den k Cnet e u loss density p n d x v Y
    D R G A hk F N l hl j B
  have hR := ConcentratedGrainData.NormalizedBlock.nonempty D G hδ
  have hlgood := (Finset.mem_filter.mp hl).1
  have hlam : 0 < δ ^ t / firstFillingMassConstant := by positivity
  have hposfin := N.physical_piece_mass_pos_finite hδ hlam hlgood j
  have hmeas : MeasurableSet (N.physicalCarrier l j) :=
    (N.carrier_measurable l j).preimage G.affine.toContinuousAffineEquiv.continuous.measurable
  obtain ⟨cut, θ, Z, packets, center, hcut, hlo, hup, hgr, hp, hm, hh⟩ :=
    HP δ ρ hδ (hδ0.trans (min_le_left _ _)) (D.dimensions hδ).2.1 R.card
      (B.direction hδ) (N.physicalPiece l j) (N.physicalCarrier l j)
      (Finset.card_pos.mpr hR) (B.direction_norm hδ)
      (N.physicalPiece_measurable l j) hmeas (N.physicalPiece_in_carrier hlgood j)
      hposfin.1 hposfin.2
      (N.physical_carrier_high_overlap_budget hδ hR
        (HM δ hδ (hδ0.trans (min_le_right _ _))) hl j)
      (Hcap B hδ hlgood)
  exact ⟨{
    input := N.physicalPiece l j
    input_subset := fun _ => Subset.rfl
    input_measurable := N.physicalPiece_measurable l j
    cut := cut
    scale := θ
    shade := Z
    packets := packets
    center := center
    measurable_cut := hcut
    lower := hlo
    upper := hup
    growth := hgr
    refinement := hp
    mass := hm
    high := hh
  }⟩

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
