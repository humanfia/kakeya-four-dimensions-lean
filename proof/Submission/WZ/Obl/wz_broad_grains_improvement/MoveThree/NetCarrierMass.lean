-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.NetCarrierMass.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/NetCarrierMass.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.NetCarrierOverlap
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.UniformMass

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open scoped Classical

noncomputable section
namespace HighNetBlock

variable {σ ω ζ δ ε b ρ c β τ Cnet e t ν : ℝ} {p n d : ℕ}
  {x v : Fin n → V} {Y : Fin n → Set V}
  {D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y}
  {R : Finset (Fin D.L)} {G : D.NormalizedBlock R}
  {A : BlockAngularData D R G β τ}

/-- High carrier fibres retain a small power of the original block count. -/
theorem carrier_count_retention (H : HighNetBlock A σ Cnet e t ν d)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hmass : τ + 21 * ε / 40 ≤ t) :
    δ ^ (2 * e + 2 * t) / (32 * firstFillingMassConstant) * (R.card : ℝ) ≤
      ∑ l ∈ H.nets.highLabels, (H.nets.N l : ℝ) * H.nets.size l := by
  have hH : 0 < firstFillingMassConstant := by norm_num [firstFillingMassConstant]
  have hcount : δ ^ t / firstFillingMassConstant * δ ^ t * (R.card : ℝ) / 16 ≤
      ∑ l ∈ H.filling.good, ((H.filling.indices l).card : ℝ) := by
    apply le_trans ?_ H.filling.count
    have hh := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hmass)
      (show 0 ≤ (δ ^ t / firstFillingMassConstant) * (R.card : ℝ) / 16 by positivity)
    nlinarith only [hh]
  calc
    _ = δ ^ (2 * e) * ((1 / 2 : ℝ) *
        (δ ^ t / firstFillingMassConstant * δ ^ t * (R.card : ℝ) / 16)) := by
      rw [Real.rpow_add hδ, show (2 : ℝ) * t = t + t by ring, Real.rpow_add hδ]
      ring
    _ ≤ δ ^ (2 * e) * ((1 / 2 : ℝ) *
        (∑ l ∈ H.filling.good, ((H.filling.indices l).card : ℝ))) := by gcongr
    _ ≤ δ ^ (2 * e) * (∑ l ∈ H.nets.highLabels, ((H.filling.indices l).card : ℝ)) :=
      mul_le_mul_of_nonneg_left H.high_count (Real.rpow_nonneg hδ.le _)
    _ ≤ _ := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun l hl => H.power_retention l (Finset.mem_filter.mp hl).1

/-- The filled row mass turns the retained high-net count into retained
actual normalized grain shading. -/
theorem carrier_mass_retention (H : HighNetBlock A σ Cnet e t ν d)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hmass : τ + 21 * ε / 40 ≤ t) :
    O (384 / firstFillingMassConstant ^ 2 * δ ^ (2 * e + 3 * t)) *
        ∑ i, μ (D.normalizedShade R G.affine i) ≤
      ∑ l ∈ H.nets.highLabels, ∑ j, ∑ i, μ (H.nets.piece l j i) := by
  have hρ := (D.dimensions hδ).2.1
  have hH : 0 < firstFillingMassConstant := by norm_num [firstFillingMassConstant]
  let row := 48 * (δ ^ t / firstFillingMassConstant) * (2 * ρ) ^ 2
  have hrow : 0 ≤ row := by dsimp [row]; positivity
  let keep := 384 / firstFillingMassConstant ^ 2 * δ ^ (2 * e + 3 * t)
  have hkeep : 0 ≤ keep := by dsimp [keep]; positivity
  have hupp : (∑ i, μ (D.normalizedShade R G.affine i)) ≤ O ((ρ ^ 2 / 64) * R.card) := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      WangZahlLot.Obl.wz_regular_transverse_affine_cells.sum_le_uniform_mass
        Finset.univ _ (by positivity : 0 ≤ ρ ^ 2 / 64)
        (fun i _ => (measure_mono (G.contained i)).trans_eq (G.body_volume i))
  have hcount := H.carrier_count_retention hδ hδ1 hmass
  have hscalar : keep * ((ρ ^ 2 / 64) * R.card) ≤
      row * (∑ l ∈ H.nets.highLabels, (H.nets.N l : ℝ) * H.nets.size l) := by
    apply le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left hcount hrow)
    dsimp [keep, row]
    rw [show 2 * e + 3 * t = t + (2 * e + 2 * t) by ring, Real.rpow_add hδ]
    ring
  have hrows : (∑ l ∈ H.nets.highLabels, ∑ j : Fin (H.nets.N l),
      O (row * (H.nets.size l : ℝ))) ≤
      ∑ l ∈ H.nets.highLabels, ∑ j, ∑ i, μ (H.nets.piece l j i) := by
    apply Finset.sum_le_sum
    intro l hl
    apply Finset.sum_le_sum
    intro j _
    exact H.nets.piece_mass (Finset.mem_filter.mp hl).1 j
  calc
    _ ≤ O keep * O ((ρ ^ 2 / 64) * R.card) := mul_le_mul' le_rfl hupp
    _ = O (keep * ((ρ ^ 2 / 64) * R.card)) := (ENNReal.ofReal_mul hkeep).symm
    _ ≤ O (row * (∑ l ∈ H.nets.highLabels, (H.nets.N l : ℝ) * H.nets.size l)) :=
      ENNReal.ofReal_le_ofReal hscalar
    _ = ∑ l ∈ H.nets.highLabels, ∑ j : Fin (H.nets.N l), O (row * (H.nets.size l : ℝ)) := by
      dsimp only [O]
      rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun l _ => by positivity)]
      apply Finset.sum_congr rfl
      intro l hl
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      ring
    _ ≤ _ := hrows

end HighNetBlock
end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
