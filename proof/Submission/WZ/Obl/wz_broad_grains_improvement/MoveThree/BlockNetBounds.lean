-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.BlockNetBounds.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/BlockNetBounds.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.BlockNets
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.BlockPacketVolume
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.NetCounting

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open scoped Classical
open WangZahlLot.Obl.wz_transverse_cell_weighted_cover (netConst_pos)

noncomputable section
namespace BlockNetData

variable {σ ω ζ δ ε b ρ c β τ lam den k Cnet e Λ Kc : ℝ} {p n d : ℕ}
  {x v : Fin n → V} {Y : Fin n → Set V}
  {D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y}
  {R : Finset (Fin D.L)} {G : D.NormalizedBlock R}
  {A : BlockAngularData D R G β τ} {hk : 0 < k}
  {F : BlockFirstFilling A lam den k hk}

def lowLabels (N : BlockNetData (σ := σ) F Cnet e Λ Kc d) : Finset (Fin A.labels.card) :=
  F.good.filter fun l => (N.size l : ℝ) * (F.volumeFactor * (ρ ^ 2 / 64)) ≤
    grainCoefficient D.a ρ c D.z D.e D.Q * (4 * F.radius) ^ 2 / Kc

def highLabels (N : BlockNetData (σ := σ) F Cnet e Λ Kc d) : Finset (Fin A.labels.card) :=
  F.good.filter fun l => ¬ ((N.size l : ℝ) * (F.volumeFactor * (ρ ^ 2 / 64)) ≤
    grainCoefficient D.a ρ c D.z D.e D.Q * (4 * F.radius) ^ 2 / Kc)

/-- The actual simultaneous low-fibre estimate, after canceling its common
Jacobian and using the packet overlap bound. -/
theorem low_count_bound (N : BlockNetData (σ := σ) F Cnet e Λ Kc d)
    (hδ : 0 < δ) (hR : R.Nonempty) (hC : 0 < Cnet) (hΛ : 0 < Λ)
    (hd : 0 < d) (hKc : 0 < Kc) (hβ : 0 ≤ β)
    {cap : ℝ} (hcap : 0 ≤ cap)
    (hupp : μ (⋃ i, D.normalizedShade R G.affine i) ≤ O cap) :
    (lowQCoeff Cnet δ e F.radius ω σ (ρ ^ 2 / 64)
      (grainCoefficient D.a ρ c D.z D.e D.Q) Λ d * Kc ^ (σ / 2)) *
      (∑ l ∈ N.lowLabels, ((F.indices l).card : ℝ)) ≤ 2 * δ ^ (-β) * cap := by
  have hρ := (D.dimensions hδ).2.1
  have hM : 0 < grainCoefficient D.a ρ c D.z D.e D.Q :=
    (Real.rpow_pos_of_pos hδ (-ζ)).trans D.large
  have hJ := F.volumeFactor_pos hδ hR
  have hB := F.radius_pos hδ hR
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  let C := lowQCoeff Cnet δ e F.radius ω σ (ρ ^ 2 / 64)
    (grainCoefficient D.a ρ c D.z D.e D.Q) Λ d * Kc ^ (σ / 2)
  have hcoef : 0 ≤ C := by dsimp [C, lowQCoeff]; have := netConst_pos; positivity
  have hupp' : (∑ l ∈ N.lowLabels, μ (⋃ i, A.normalizedPiece l i)) ≤
      O (2 * δ ^ (-β) * cap) := by
    apply (A.normalizedPiece_union_sum hδ hβ N.lowLabels).trans
    apply (mul_le_mul' le_rfl hupp).trans_eq
    exact (ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * δ ^ (-β))).symm
  apply sum_affine_density_cancel N.lowLabels (fun l => (F.indices l).card)
    (fun l => μ (⋃ i, A.normalizedPiece l i)) hJ hcoef (by positivity) ?_ hupp'
  have H := N.low_sum
  change (∑ l ∈ N.lowLabels, O (_ * Kc ^ (σ / 2) * (F.indices l).card)) ≤ _ at H
  convert H using 1
  · apply Finset.sum_congr rfl
    intro l hl
    congr 1
    dsimp [C, lowQCoeff]
    ring
  · rfl

end BlockNetData
end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
