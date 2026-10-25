-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.HighNetConcentration.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/HighNetConcentration.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.FilledConcentration
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.BlockHighLabels

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_transverse_cell_weighted_cover (netConst)

noncomputable section

/-- First fillings and their high-fibre carrier nets, retaining the original
indices and a quantified fraction of all filled index occurrences. -/
structure HighNetBlock {ω ζ δ ξ b ρ c β τ : ℝ} {p n : ℕ} {x v : Fin n → V}
    {Y : Fin n → Set V} {D : ConcentratedGrainData ω ζ δ ξ b ρ c p n x v Y}
    {R : Finset (Fin D.L)} {G : D.NormalizedBlock R}
    (A : BlockAngularData D R G β τ) (σ Cnet e t ν : ℝ) (d : ℕ) where
  filling : BlockFirstFilling A (δ ^ t / firstFillingMassConstant) (δ ^ (ν / 2))
    firstFillingShrink firstFillingShrink_pos
  nets : BlockNetData (σ := σ) filling Cnet e (δ ^ (-e)) (δ ^ (-ζ / 2)) d
  high_count : (1 / 2 : ℝ) * (∑ l ∈ filling.good, ((filling.indices l).card : ℝ)) ≤
    ∑ l ∈ nets.highLabels, ((filling.indices l).card : ℝ)
  power_retention : ∀ l ∈ filling.good,
    δ ^ (2 * e) * ((filling.indices l).card : ℝ) ≤ (nets.N l : ℝ) * nets.size l
  high_weight : ∀ l ∈ nets.highLabels, δ ^ (-ζ / 2) * (4 * filling.radius) ^ 2 <
    (nets.size l : ℝ) * (filling.volumeFactor * (ρ ^ 2 / 64))

/-- The full original-family reduction through the high-fibre net step.
Every loss can be arbitrarily small relative to the final requested error. -/
theorem gain_terminal_or_high_net_concentration_with_cap {σ ω ζ ε capLoss : ℝ}
    (hσ : 0 < σ) (hσhalf : σ ≤ 1 / 2) (hω : 0 < ω) (hE : E σ ω)
    (hζ : 0 < ζ) (hε : 0 < ε) (hcapLoss : 0 < capLoss)
    (hcapMax : capLoss ≤ ζ * σ / 16) :
    ∃ (β τ ξ b t ν e Cnet α κ θ d₀ : ℝ) (p d : ℕ),
      0 < β ∧ β ≤ 1 ∧ β ≤ ζ * σ / 128 ∧ 0 < τ ∧
      0 < ξ ∧ ξ ≤ ε / 4 ∧ ξ ≤ 1 ∧ 0 < b ∧ b ≤ ξ / 384 ∧
      0 < t ∧ t ≤ ν / 50 ∧ τ + 21 * ξ / 40 ≤ t ∧
      0 < ν ∧ ν ≤ ε / 1000 ∧ ν ≤ ζ * σ / 100 ∧
      0 < e ∧ e ≤ ε / 1000 ∧ e ≤ ζ * σ / 128 ∧ 0 < Cnet ∧
      0 < α ∧ 0 < κ ∧ 0 < θ ∧ θ ≤ ε ∧ 0 < d₀ ∧ d₀ ≤ 1 / 4096 ∧ 0 < p ∧ 0 < d ∧
      ∀ δ h : ℝ, 0 < δ → δ ≤ d₀ → 0 ≤ h → h ≤ θ →
      ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V),
      A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y →
      ∀ ρ c, J ω ζ δ h ρ c n x v Y 2 →
      Gain σ ω κ α δ n Y ∨ J ω ζ δ ε ρ c n x v Y 3 ∨
        ∃ Y' : Fin n → Set V,
          (∀ i, Y' i ⊆ Y i) ∧
          O (δ ^ (ε / 8)) * ∑ i, μ (Y i) ≤ ∑ i, μ (Y' i) ∧
          A δ (ξ / 4) (δ ^ (-(ξ / 4))) (δ ^ (-(ξ / 4))) n x v Y' ∧
          (∀ q ∈ ⋃ i, Y' i, ∀ r : ℝ, 0 < r → r ≤ 1 →
            μ ((⋃ i, Y' i) ∩ ball q r) ≤
              O (δ ^ (-capLoss) * (δ / r) ^ (ω + σ) * r ^ 3)) ∧
          ∃ (D : ConcentratedGrainData ω ζ δ ξ b ρ c p n x v Y')
            (F : AngularBlockFamily D β τ),
            ∀ R : F.blocks, Nonempty (HighNetBlock (F.angular R) σ Cnet e t ν d) := by
  classical
  let e := min (ε / 1000) (ζ * σ / 128)
  have he : 0 < e := lt_min (by positivity) (by positivity)
  have heε : e ≤ ε / 1000 := min_le_left _ _
  have heζ : e ≤ ζ * σ / 128 := min_le_right _ _
  obtain ⟨Cnet, ηnet, dnet, hCnet, hηnet, hdnet, hdnetmax, Hnet⟩ :=
    block_filling_balanced_nets hσ.le hσhalf hω hE e he
  let ν := min ηnet (min (ε / 1000) (ζ * σ / 100))
  have hν : 0 < ν := lt_min hηnet (lt_min (by positivity) (by positivity))
  have hνη : ν ≤ ηnet := min_le_left _ _
  have hνε : ν ≤ ε / 1000 := (min_le_right _ _).trans (min_le_left _ _)
  have hνζ : ν ≤ ζ * σ / 100 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨β, τ, ξ, b, t, α, κ, θ, dfill, p, hβ, hβ1, hβζ, hτ, hξ, hξε, hξ1,
    hb, hbξ, ht, htν, hmass, hα, hκ, hθ, hθε, hdfill, _, hp, Hfill⟩ :=
    gain_terminal_or_filled_concentration_with_cap hσ hσhalf hω hE hζ hε hν hcapLoss hcapMax
  have hH : 0 < firstFillingMassConstant := by norm_num [firstFillingMassConstant]
  have hgap : e + e + t + t + β + ζ * σ / 16 < ζ * σ / 4 := by
    have hh : 0 < ζ * σ := mul_pos hζ hσ
    linarith only [heζ, htν, hνζ, hβζ, hh]
  obtain ⟨d, dcomp, hd, hdcomp, _, Hcomp⟩ := first_net_parameters hCnet he hζ
    (netCapCoefficient_pos (s := ω + σ) firstFillingShrink_pos).le
    (by positivity : 0 ≤ 110592 * (2 : ℝ) ^ p) hH hgap
  obtain ⟨drad, hdrad, Hrad⟩ := first_filling_net_scale_cutoff hω firstFillingShrink_pos
  refine ⟨β, τ, ξ, b, t, ν, e, Cnet, α, κ, θ,
    min dfill (min dnet (min dcomp drad)), p, d,
    hβ, hβ1, hβζ, hτ, hξ, hξε, hξ1, hb, hbξ, ht, htν, hmass,
    hν, hνε, hνζ, he, heε, heζ, hCnet, hα, hκ, hθ, hθε,
    by positivity, (min_le_right _ _).trans ((min_le_left _ _).trans hdnetmax), hp, hd, ?_⟩
  intro δ h hδ hδd hh hhθ n x v Y hA ρ c hJ
  have hδfill := hδd.trans (min_le_left _ _)
  have hδnet := hδd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδcomp := hδd.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hδrad := hδd.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hδ1 : δ ≤ 1 := hδnet.trans (hdnetmax.trans (by norm_num))
  obtain ⟨hΛ, hKc, hret, hdepth, hsmall⟩ := Hcomp δ hδ hδcomp
  rcases Hfill δ h hδ hδfill hh hhθ n x v Y hA ρ c hJ with hgain | hterminal | hdata
  · exact Or.inl hgain
  · exact Or.inr (Or.inl hterminal)
  obtain ⟨Y', hsub, hYret, hA', hcap, hden, D, F, HF⟩ := hdata
  right; right
  refine ⟨Y', hsub, hYret, hA', hcap, D, F, ?_⟩
  intro R
  let A := F.angular R
  let FF := Classical.choice (HF R)
  have hR : R.val.Nonempty := ConcentratedGrainData.NormalizedBlock.nonempty D (F.frame R) hδ
  have hdim := A.packet_dimensions hδ hR
  have hbase : 4 * δ ≤ FF.radius := Hrad δ hδ hδrad ρ A.packetShort D.lower_scale
    hdim.1 (hdim.2.2.1.trans hdim.2.2.2.1)
  have hden' : 6144 * δ ^ ηnet ≤ δ ^ (ν / 2) * firstFillingShrink / 16000 :=
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hνη) (by norm_num)).trans hden
  obtain ⟨NN⟩ := Hnet δ hδ hδnet (δ ^ (-ζ / 2)) hKc D R.val hR (F.frame R)
    A FF d (δ ^ (-e)) hξ1 hA' (by positivity) hd hΛ
    (hdepth R.val.card (D.block_cardinality_at_base hδ
      (hδnet.trans hdnetmax) hξ1 hA' R.val)) hbase hden'
  refine ⟨{
    filling := FF
    nets := NN
    high_count := NN.high_count_of_cap_comparison hδ hδ1 hR hCnet hd hβ.le
      (by positivity) hmass hA' (ball_density_cap_mono hδ hδ1 hcapMax hcap) hsmall
    power_retention := ?_
    high_weight := fun l hl => NN.high_fibre_weight hδ hl }⟩
  intro l hl
  obtain ⟨_, _, _, _, _, _, hcount, _⟩ := NN.net l hl
  exact balanced_net_power_retention hδ hd (Nat.cast_nonneg _) hret hcount


theorem gain_terminal_or_high_net_concentration {σ ω ζ ε : ℝ}
    (hσ : 0 < σ) (hσhalf : σ ≤ 1 / 2) (hω : 0 < ω) (hE : E σ ω)
    (hζ : 0 < ζ) (hε : 0 < ε) :
    ∃ (β τ ξ b t ν e Cnet α κ θ d₀ : ℝ) (p d : ℕ),
      0 < β ∧ β ≤ 1 ∧ β ≤ ζ * σ / 128 ∧ 0 < τ ∧
      0 < ξ ∧ ξ ≤ ε / 4 ∧ ξ ≤ 1 ∧ 0 < b ∧ b ≤ ξ / 384 ∧
      0 < t ∧ t ≤ ν / 50 ∧ τ + 21 * ξ / 40 ≤ t ∧
      0 < ν ∧ ν ≤ ε / 1000 ∧ ν ≤ ζ * σ / 100 ∧
      0 < e ∧ e ≤ ε / 1000 ∧ e ≤ ζ * σ / 128 ∧ 0 < Cnet ∧
      0 < α ∧ 0 < κ ∧ 0 < θ ∧ θ ≤ ε ∧ 0 < d₀ ∧ d₀ ≤ 1 / 4096 ∧ 0 < p ∧ 0 < d ∧
      ∀ δ h : ℝ, 0 < δ → δ ≤ d₀ → 0 ≤ h → h ≤ θ →
      ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V),
      A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y →
      ∀ ρ c, J ω ζ δ h ρ c n x v Y 2 →
      Gain σ ω κ α δ n Y ∨ J ω ζ δ ε ρ c n x v Y 3 ∨
        ∃ Y' : Fin n → Set V,
          (∀ i, Y' i ⊆ Y i) ∧
          O (δ ^ (ε / 8)) * ∑ i, μ (Y i) ≤ ∑ i, μ (Y' i) ∧
          A δ (ξ / 4) (δ ^ (-(ξ / 4))) (δ ^ (-(ξ / 4))) n x v Y' ∧
          (∀ q ∈ ⋃ i, Y' i, ∀ r : ℝ, 0 < r → r ≤ 1 →
            μ ((⋃ i, Y' i) ∩ ball q r) ≤
              O (δ ^ (-(ζ * σ / 16)) * (δ / r) ^ (ω + σ) * r ^ 3)) ∧
          ∃ (D : ConcentratedGrainData ω ζ δ ξ b ρ c p n x v Y')
            (F : AngularBlockFamily D β τ),
            ∀ R : F.blocks, Nonempty (HighNetBlock (F.angular R) σ Cnet e t ν d) := by
  exact gain_terminal_or_high_net_concentration_with_cap hσ hσhalf hω hE hζ hε
    (by positivity : 0 < ζ * σ / 16) le_rfl

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
