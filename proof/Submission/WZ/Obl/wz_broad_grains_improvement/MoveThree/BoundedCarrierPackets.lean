-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.BoundedCarrierPackets.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/BoundedCarrierPackets.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.ClippedCarrierPackets
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.FixedCapPackets

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory

noncomputable section

/-- The actual second packets can be required to have an arbitrarily small
fixed maximum angle. Their mass is still measured against the full original
first-net fibre, before the cap selection. -/
theorem bounded_clipped_carrier_angular_data_uniform {ζ t β₂ q₀ jump τ₂ angleMax : ℝ}
    (hβ : 0 < β₂) (hβ1 : β₂ ≤ 1) (hjump : 0 < jump)
    (hcapgap : β₂ + 3 * jump < q₀) (hτ : 0 < τ₂)
    (hmassgap : 0 < ζ / 2 - q₀ - t) (hangle : 0 < angleMax) :
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
          ∃ Q : ClippedCarrierAngularData B hδ β₂ q₀ jump τ₂, Q.scale ≤ angleMax := by
  let q₁ := (q₀ + ζ / 2 - t) / 2
  have hq : q₀ < q₁ := by dsimp [q₁]; linarith
  have hmassgap' : 0 < ζ / 2 - q₁ - t := by dsimp [q₁]; linarith
  obtain ⟨C, hC, Hcap⟩ := clipped_carrier_cap_count
  obtain ⟨dP, hdP, hdP1, HP⟩ := capped_high_carrier_growing_packets hC hβ hβ1 hjump
    (by linarith : 0 < q₀ - β₂ - 3 * jump) hτ hq hangle
  have hH : 0 < firstFillingMassConstant := by norm_num [firstFillingMassConstant]
  obtain ⟨dM, hdM, HM⟩ := WangZahlLot.Obl.wz_move_two_long_grains_gain.small_rpow
    hmassgap' (K := 16 / firstFillingMassConstant) (by positivity)
  refine ⟨min dP dM, lt_min hdP hdM, (min_le_left _ _).trans hdP1, ?_⟩
  intro δ hδ hδ0 σ ω ε b ρ c β τ den k Cnet e u loss density p n d x v Y
    D R G A hk F N l hl j B
  have hR := ConcentratedGrainData.NormalizedBlock.nonempty D G hδ
  have hlgood := (Finset.mem_filter.mp hl).1
  have hlam : 0 < δ ^ t / firstFillingMassConstant := by positivity
  have hposfin := N.physical_piece_mass_pos_finite hδ hlam hlgood j
  have hmeas : MeasurableSet (N.physicalCarrier l j) :=
    (N.carrier_measurable l j).preimage G.affine.toContinuousAffineEquiv.continuous.measurable
  obtain ⟨input, cut, θ, Z, packets, center, hinput, hcut, hlo, hup, hmax, hgr, hp, hm, hh⟩ :=
    HP δ ρ hδ (hδ0.trans (min_le_left _ _)) (D.dimensions hδ).2.1 R.card
      (B.direction hδ) (N.physicalPiece l j) (N.physicalCarrier l j)
      (Finset.card_pos.mpr hR) (B.direction_norm hδ)
      (N.physicalPiece_measurable l j) hmeas (N.physicalPiece_in_carrier hlgood j)
      hposfin.1 hposfin.2
      (N.physical_carrier_high_overlap_budget hδ hR
        (HM δ hδ (hδ0.trans (min_le_right _ _))) hl j)
      (Hcap B hδ hlgood)
  exact ⟨{
    input := input
    input_subset := fun i => (hinput i).2
    input_measurable := fun i => (hinput i).1
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
  }, hmax⟩

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
