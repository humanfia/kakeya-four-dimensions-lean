-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.BlockParameters.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/BlockParameters.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.NormalizedGrainBlocks

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory

noncomputable section
namespace ConcentratedGrainData

variable {ω ζ δ ε b ρ c : ℝ} {p n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}

/-- Every selected block satisfies the polynomial cardinality condition at
base scale delta squared. -/
theorem block_cardinality_bound (D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 4096) (hε : ε ≤ 1)
    (hA : A δ (ε / 4) (δ ^ (-(ε / 4))) (δ ^ (-(ε / 4))) n x v Y)
    (R : Finset (Fin D.L)) : (R.card : ℝ) ≤ (δ ^ (2 : ℕ)) ^ (-100 : ℝ) := by
  have hδ1 : δ ≤ 1 := hδsmall.trans (by norm_num)
  have hcard : (R.card : ℝ) ≤ D.L := by
    exact_mod_cast (show R.card ≤ D.L by simpa using Finset.card_le_univ R)
  have hL := grain_card_bound hδ hA D.cover D.grains
  have h64 : (64 : ℝ) ≤ δ ^ (-1 : ℝ) := by
    rw [Real.rpow_neg_one, inv_eq_one_div, le_div_iff₀ hδ]
    linarith
  have hexp : δ ^ (-(2 * (ε / 4) + 5)) ≤ δ ^ (-6 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have heq : δ ^ (-1 : ℝ) * δ ^ (-6 : ℝ) = δ ^ (-7 : ℝ) := by
    rw [← Real.rpow_add hδ]
    norm_num
  have hδ2 : δ ^ (2 : ℕ) ≤ δ := by nlinarith
  calc
    _ ≤ (D.L : ℝ) := hcard
    _ ≤ 64 * δ ^ (-(2 * (ε / 4) + 5)) := hL
    _ ≤ δ ^ (-1 : ℝ) * δ ^ (-6 : ℝ) :=
      mul_le_mul h64 hexp (Real.rpow_nonneg hδ.le _) (Real.rpow_nonneg hδ.le _)
    _ = δ ^ (-7 : ℝ) := heq
    _ ≤ δ ^ (-100 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by norm_num)
    _ ≤ _ := Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hδ) hδ2 (by norm_num)

/-- The prism widths and the original grain scale guarantee the geometric
base-scale restrictions for the second normalization. -/
theorem NormalizedBlock.base_parameters (D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y)
    {R : Finset (Fin D.L)} (G : NormalizedBlock D R)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 4096) :
    δ ^ (2 : ℕ) ≤ (ρ / 100) / 4 ∧
    δ ^ (2 : ℕ) ≤ Real.sqrt ((ρ ^ 2 / 64) / (4 * G.short * G.middle)) / 16 := by
  obtain ⟨ha, hρ, -, hc, hc1⟩ := D.dimensions hδ
  have hδρ : δ ≤ ρ := D.grains.1.trans (D.grains.2.1.trans (by nlinarith))
  have hδ2 : δ ^ (2 : ℕ) ≤ ρ / 4096 := by
    have hh := mul_le_mul_of_nonneg_left hδsmall hδ.le
    nlinarith
  have hs : 0 < G.short := G.short_pos
  have hb : 0 < G.middle := G.short_pos.trans_le G.ordered
  have hab : G.short * G.middle ≤ 16 := by
    have hh := mul_le_mul (G.ordered.trans G.middle_le) G.middle_le hb.le
      (by norm_num : (0 : ℝ) ≤ 4)
    norm_num at hh
    exact hh
  have hquot : (ρ / 64) ^ 2 ≤ (ρ ^ 2 / 64) / (4 * G.short * G.middle) := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * G.short * G.middle)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hab (sq_nonneg ρ)]
  have hsqrt : ρ / 64 ≤ Real.sqrt ((ρ ^ 2 / 64) / (4 * G.short * G.middle)) :=
    (Real.le_sqrt (by positivity) (by positivity)).mpr hquot
  constructor <;> nlinarith

end ConcentratedGrainData
end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
