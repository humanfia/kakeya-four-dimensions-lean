-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.BlockHighLabels.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/BlockHighLabels.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.BlockNetBounds
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.BlockNetCap
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.HighLabelSelection
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.FirstNetParameters

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open scoped Classical
open WangZahlLot.Obl.wz_transverse_cell_weighted_cover (netConst netConst_pos)

noncomputable section
namespace BlockNetData

variable {σ ω ζ δ ε b ρ c β τ den k Cnet e u t : ℝ} {p n d : ℕ}
  {x v : Fin n → V} {Y : Fin n → Set V}
  {D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y}
  {R : Finset (Fin D.L)} {G : D.NormalizedBlock R}
  {A : BlockAngularData D R G β τ} {hk : 0 < k}
  {F : BlockFirstFilling A (δ ^ t / firstFillingMassConstant) den k hk}

/-- In the actual density-capped block, at least half of the filled index
occurrences lie in nets above the concentration threshold. -/
theorem high_count_of_cap_comparison
    (N : BlockNetData (σ := σ) F Cnet e (δ ^ (-u)) (δ ^ (-ζ / 2)) d)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : R.Nonempty) (hC : 0 < Cnet) (hd : 0 < d)
    (hβ : 0 ≤ β) (hs : 0 ≤ ω + σ) (hmass : τ + 21 * ε / 40 ≤ t)
    (hA : WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.A δ (ε / 4)
      (δ ^ (-(ε / 4))) (δ ^ (-(ε / 4))) n x v Y)
    (hcap : ∀ q ∈ ⋃ i, Y i, ∀ r : ℝ, 0 < r → r ≤ 1 →
      μ ((⋃ i, Y i) ∩ ball q r) ≤
        O (δ ^ (-(ζ * σ / 16)) * (δ / r) ^ (ω + σ) * r ^ 3))
    (hsmall : 64 * netCapCoefficient k (ω + σ) * (110592 * (2 : ℝ) ^ p) *
        firstFillingMassConstant < (Cnet * netConst / d) *
          δ ^ (e + u + t + t + β + ζ * σ / 16 - ζ * σ / 4)) :
    (1 / 2 : ℝ) * (∑ l ∈ F.good, ((F.indices l).card : ℝ)) ≤
      ∑ l ∈ N.highLabels, ((F.indices l).card : ℝ) := by
  have hρ := (D.dimensions hδ).2.1
  have hM : 0 < grainCoefficient D.a ρ c D.z D.e D.Q :=
    (Real.rpow_pos_of_pos hδ (-ζ)).trans D.large
  have hB := F.radius_pos hδ hR
  have hshort := G.short_pos
  have hmid := hshort.trans_le G.ordered
  have hn : (0 : ℝ) < R.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hR)
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hH : 0 < firstFillingMassConstant := by norm_num [firstFillingMassConstant]
  have hc := netCapCoefficient_pos (s := ω + σ) hk
  let cap := netCapCoefficient k (ω + σ) * δ ^ (-(ζ * σ / 16)) *
    (4 * F.radius) ^ (ω + σ) * (4 * G.short * G.middle)
  let Co := lowQCoeff Cnet δ e F.radius ω σ (ρ ^ 2 / 64)
    (grainCoefficient D.a ρ c D.z D.e D.Q) (δ ^ (-u)) d *
      (δ ^ (-ζ / 2)) ^ (σ / 2)
  have hcap0 : 0 ≤ cap := by dsimp [cap]; positivity
  have hCo : 0 < Co := by dsimp [Co, lowQCoeff]; have := netConst_pos; positivity
  have hlow : Co * (∑ l ∈ N.lowLabels, ((F.indices l).card : ℝ)) ≤
      2 * δ ^ (-β) * cap :=
    N.low_count_bound hδ hR hC (by positivity) hd (by positivity) hβ hcap0
      (F.normalized_block_net_cap hδ hR hs hA hcap)
  have hcount : δ ^ t / firstFillingMassConstant * δ ^ t * (R.card : ℝ) / 16 ≤
      ∑ l ∈ F.good, ((F.indices l).card : ℝ) := by
    apply le_trans ?_ F.count
    have hh := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hmass)
      (show 0 ≤ (δ ^ t / firstFillingMassConstant) * (R.card : ℝ) / 16 by positivity)
    nlinarith only [hh]
  have hpow : Co = (Cnet * netConst / d) * δ ^ (e + u) * (4 * F.radius) ^ (ω + σ) *
      1 * (ρ ^ 2 / 64) / (grainCoefficient D.a ρ c D.z D.e D.Q) * δ ^ (-(ζ * σ / 4)) := by
    simpa only [one_mul] using low_q_coefficient_power_form
      (J := 1) (w := ρ ^ 2 / 64) (A := Cnet) (ε := e) (u := u)
      (ζ := ζ) (σ := σ) (ω := ω) (B := F.radius) hδ hd hM
  have hgap := aggregate_cap_comparison (J := 1) (Kov := 2 * δ ^ (-β))
    (cap := cap) (K := Co) (S := ∑ l ∈ F.good, ((F.indices l).card : ℝ))
    (Vblk := 4 * G.short * G.middle) (R := 4 * F.radius) (s := ω + σ)
    (Ccap := netCapCoefficient k (ω + σ)) (Csat := 110592 * (2 : ℝ) ^ p)
    (H := firstFillingMassConstant) (Cnet := Cnet * netConst / d)
    (en := e + u) (t := t) (l := t) (uc := ζ * σ / 16) (zs := ζ * σ / 4)
    hδ (by norm_num) (by positivity) (by positivity) hM hn hc.le hH
    (by have := netConst_pos; positivity) le_rfl hcap0 le_rfl G.saturated hcount hpow hsmall
  have hgap' : 2 * δ ^ (-β) * cap <
      Co * (∑ l ∈ F.good, ((F.indices l).card : ℝ)) / 2 := by simpa only [one_mul] using hgap
  exact high_labels_carry_half F.good (fun l => (F.indices l).card)
    (fun l => (N.size l : ℝ) * (F.volumeFactor * (ρ ^ 2 / 64)) ≤
      grainCoefficient D.a ρ c D.z D.e D.Q * (4 * F.radius) ^ 2 / δ ^ (-ζ / 2))
    hCo hlow hgap'

/-- A high label has an absolute concentration power, since the original
block coefficient exceeds delta to the minus zeta. -/
theorem high_fibre_weight
    (N : BlockNetData (σ := σ) F Cnet e (δ ^ (-u)) (δ ^ (-ζ / 2)) d)
    (hδ : 0 < δ) {l : Fin A.labels.card} (hl : l ∈ N.highLabels) :
    δ ^ (-ζ / 2) * (4 * F.radius) ^ 2 <
      (N.size l : ℝ) * (F.volumeFactor * (ρ ^ 2 / 64)) := by
  have hh := (Finset.mem_filter.mp hl).2
  exact high_fibre_weight_of_large_coefficient hδ D.large.le (lt_of_not_ge hh)

end BlockNetData
end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
