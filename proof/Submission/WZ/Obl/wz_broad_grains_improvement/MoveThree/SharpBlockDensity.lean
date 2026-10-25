-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.SharpBlockDensity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/SharpBlockDensity.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.BlockParameters
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.SharpDensityScalar
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.SharpBodyEstimate

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_flat_factored_improvement (BodyEstimate)
open WangZahlLot.Obl.wz_separated_cover_refinement (enumerate)

noncomputable section

/-- Every saturated normalized grain block has a density lower bound with
an explicit concentration gain and aspect-ratio loss. -/
theorem sharp_normalized_block_density {σ ω : ℝ} (hbody : BodyEstimate σ ω) :
    ∀ t : ℝ, 0 < t → ∃ A η d₀ : ℝ, 0 < A ∧ 0 < η ∧ 0 < d₀ ∧ d₀ ≤ 1 / 4000000 ∧
      ∀ δ ε : ℝ, 0 < δ → δ ≤ d₀ → 0 ≤ ε → ε ≤ min η 1 →
      ∀ (ζ b ρ c : ℝ) (p n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V),
      WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.A δ (ε / 4) (δ ^ (-(ε / 4))) (δ ^ (-(ε / 4))) n x v Y →
      ∀ (D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y)
        (R : Finset (Fin D.L)), R.Nonempty → ∀ G : D.NormalizedBlock R,
      O (A / (2 : ℝ) ^ p * δ ^ t *
        (grainCoefficient D.a ρ c D.z D.e D.Q) ^ (σ / 2) *
        (grainPackingCoefficient δ ε) ^ (-σ) * (ρ / G.short) ^ (σ + ω) *
        (G.short / G.middle) ^ (σ / 2) * (4 * G.short * G.middle)) ≤
          μ (⋃ i, D.normalizedShade R G.affine i) := by
  intro t ht
  obtain ⟨C, η, d₀, hC, hη, hd₀, hsmall, H⟩ :=
    sharp_saturated_prism_body_estimate hbody (t / 2) (by positivity)
  let C' := C / 110592 * (16 : ℝ) ^ (-σ) * (819200 : ℝ) ^ (-ω)
  refine ⟨C', η, min d₀ (1 / 4000000), by dsimp [C']; positivity, hη,
    lt_min hd₀ (by norm_num), min_le_right _ _, ?_⟩
  intro δ ε hδ hδd hε hεsmall ζ b ρ c p n x v Y hA D R hR G
  have hδtiny : δ ≤ 1 / 4000000 := hδd.trans (min_le_right _ _)
  have hδsmall : δ ≤ 1 / 4096 := by linarith
  have hδ1 : δ ≤ 1 := hδsmall.trans (by norm_num)
  have hδ2 : δ ^ (2 : ℕ) ≤ δ := by nlinarith
  obtain ⟨ha, hρ, -, hc, hc1⟩ := D.dimensions hδ
  have hcard := D.block_cardinality_bound hδ hδsmall (hεsmall.trans (min_le_right _ _)) hA R
  obtain ⟨hdround, -⟩ := G.base_parameters D hδ hδsmall
  have hδρ : δ ≤ ρ := D.grains.1.trans (D.grains.2.1.trans
    (mul_le_of_le_one_right hρ.le hc1))
  have hdwidth : δ ^ (2 : ℕ) ≤ (ρ / 100) / (8192 * G.short) := by
    apply (le_div_iff₀ (by have hh := G.short_pos; positivity : 0 < 8192 * G.short)).mpr
    have hs := mul_le_mul_of_nonneg_left (G.ordered.trans G.middle_le) (sq_nonneg δ)
    have hsq : δ ^ (2 : ℕ) ≤ ρ / 4000000 := by nlinarith
    nlinarith only [hs, hsq]
  have hM := (grainCoefficient_bounds ha.le (mul_pos hρ hc).le hc.le D.z D.e D.Q).1
  have hP := grainPackingCoefficient_ge_one δ ε
  have hdensity i : O ((δ ^ (2 : ℕ)) ^ η) * μ (D.normalizedBody R G.affine i) ≤
      μ (D.normalizedShade R G.affine i) := by
    apply le_trans _ (G.dense i)
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    apply (Real.rpow_le_rpow (sq_nonneg δ) hδ2 hη.le).trans
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by
      have hh := hεsmall.trans (min_le_left _ _)
      linarith)
  have Hblock := H (δ ^ (2 : ℕ)) (sq_pos_of_pos hδ)
    (hδ2.trans (hδd.trans (min_le_left _ _))) R.card
    (D.normalizedBody R G.affine) (D.normalizedShade R G.affine)
    (fun i => G.affine (D.z (enumerate R i))) G.short G.middle (ρ / 100) (ρ ^ 2 / 64)
    (grainCoefficient D.a ρ c D.z D.e D.Q) (grainPackingCoefficient δ ε) (110592 * (2 : ℝ) ^ p)
    (Finset.card_pos.mpr hR) hcard G.short_pos G.ordered G.middle_le (by positivity)
    hdround (by positivity) hdwidth hM hP (by positivity) G.geometry.compact G.geometry.convex
    G.round G.long G.body_volume G.measurable G.contained hdensity G.convex_count G.packing
    G.saturated G.center G.frame G.enclosure
  rw [sharp_prism_density_identity hC (by positivity) hδ hρ G.short_pos
    (G.short_pos.trans_le G.ordered) (zero_lt_one.trans_le hM) (zero_lt_one.trans_le hP)] at Hblock
  exact Hblock

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
