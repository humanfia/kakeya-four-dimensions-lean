-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.PhysicalCarrierBox.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/PhysicalCarrierBox.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PhysicalBlockGeometry
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.LocalizedCarrier

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_separated_cover_refinement (enumerate)

noncomputable section

/-- An actual first-net carrier, localized at the original grain length,
has a physically thin box containing every occupied whole old grain. -/
structure PhysicalCarrierBox {σ ω ζ δ ε b ρ c β τ lam den k Cnet e Λ Kc : ℝ}
    {p n d : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}
    {D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y}
    {R : Finset (Fin D.L)} {G : D.NormalizedBlock R}
    {A : BlockAngularData D R G β τ} {hk : 0 < k}
    {F : BlockFirstFilling A lam den k hk}
    (N : BlockNetData (σ := σ) F Cnet e Λ Kc d)
    (loss density : ℝ) (l : Fin A.labels.card) (j : Fin (N.N l)) where
  short : ℝ
  middle : ℝ
  center : V
  frame : V ≃ₗᵢ[ℝ] V
  lower : D.a ≤ short
  ordered : short ≤ middle
  upper : middle ≤ 8 * c
  thin : short < δ ^ (1 - loss)
  enclosure : N.physicalCarrier l j ∩ ball (D.z G.natural_anchor) (2 * c) ⊆
    P short middle (8 * c) center frame
  dense : O (δ ^ density) * μ (P short middle (8 * c) center frame) ≤
    μ (N.physicalCarrierShade l j)

theorem physical_carrier_box_uniform {s capLoss h₀ h₁ loss : ℝ}
    (hs : 0 < s) (hh : h₀ < h₁) (hgap : capLoss + h₁ < loss * s) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d₀ →
      ∀ {σ ω ζ ε b ρ c β τ lam den k Cnet e Λ Kc : ℝ} {p n d : ℕ}
        {x v : Fin n → V} {Y : Fin n → Set V}
        {D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y}
        {R : Finset (Fin D.L)} {G : D.NormalizedBlock R}
        {A : BlockAngularData D R G β τ} {hk : 0 < k}
        {F : BlockFirstFilling A lam den k hk}
        (N : BlockNetData (σ := σ) F Cnet e Λ Kc d),
      0 < lam → 0 ≤ den → 8 * c ≤ 1 →
      δ ^ h₀ ≤ den * k / (16000 * 6144) →
      (∀ q ∈ ⋃ i, Y i, ∀ r : ℝ, 0 < r → r ≤ 1 →
        μ ((⋃ i, Y i) ∩ ball q r) ≤ O (δ ^ (-capLoss) * (δ / r) ^ s * r ^ 3)) →
      ∀ l ∈ F.good, ∀ j : Fin (N.N l), Nonempty (PhysicalCarrierBox N loss h₁ l j) := by
  obtain ⟨d₀, hd₀, hd₀1, H⟩ := capped_localized_carrier_short hs hh hgap
    (by norm_num : (0 : ℝ) < 2)
  refine ⟨d₀, hd₀, hd₀1, ?_⟩
  intro δ hδ hδd σ ω ζ ε b ρ c β τ lam den k Cnet e Λ Kc p n d x v Y D R G A hk F N
    hlam hden hcsmall hbudget hcap l hl j
  have hR := ConcentratedGrainData.NormalizedBlock.nonempty D G hδ
  obtain ⟨ha, hρ, hρ1, hc, _⟩ := D.dimensions hδ
  have hcard := (N.net l hl).2.2.2.2.1 j
  have hfib : (N.fibre l j).Nonempty := Finset.card_pos.mp
    (by rw [hcard]; exact (N.net l hl).2.1)
  obtain ⟨i, hi⟩ := hfib
  have hwhole : P D.a (ρ * c) c (D.z (enumerate R i)) (D.e (enumerate R i)) ⊆
      N.physicalCarrier l j ∩ ball (D.z G.natural_anchor) (2 * c) :=
    subset_inter (N.physical_body_in_carrier hl j i hi) (G.physical_body_ball hδ i)
  have hshade : N.physicalCarrierShade l j ⊆
      N.physicalCarrier l j ∩ ball (D.z G.natural_anchor) (2 * c) :=
    subset_inter (N.physicalCarrierShade_subset l j) (N.physicalCarrierShade_ball hδ l j)
  have hden' : O (δ ^ h₀) * μ (N.physicalCarrier l j) ≤ μ (N.physicalCarrierShade l j) :=
    (mul_le_mul' (ENNReal.ofReal_le_ofReal hbudget) le_rfl).trans
      (N.physicalCarrier_density hδ hR hlam hden hl j)
  obtain ⟨a', b', z', e', hlow, hab, hbc, hthin, hbody, _, hdense⟩ :=
    H δ hδ hδd D.a (ρ * c) c (D.z (enumerate R i)) (D.z G.natural_anchor)
      (D.e (enumerate R i)) (N.physicalCarrier l j) (N.physicalCarrierShade l j) (⋃ i, Y i)
      ha D.grains.2.1 D.grains.2.2.1 (by nlinarith) (N.physicalCarrier_convex l j)
      hwhole hshade (N.physicalCarrierShade_ambient l j) hden' hcap
  exact ⟨{
    short := a'
    middle := b'
    center := z'
    frame := e'
    lower := hlow
    ordered := hab
    upper := by nlinarith only [hbc]
    thin := hthin
    enclosure := by simpa only [show (4 : ℝ) * 2 = 8 by norm_num] using hbody
    dense := by simpa only [show (4 : ℝ) * 2 = 8 by norm_num] using hdense
  }⟩

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
