-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.NetCarrierOverlap.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/NetCarrierOverlap.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.NetCarrierData

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric

noncomputable section

/-- The row-density factor and the high-fibre concentration pay for the
volume of a carrier, with an explicit positive exponent margin. -/
theorem high_carrier_scalar {δ ζ q₀ t H : ℝ} (hδ : 0 < δ) (hH : 0 < H)
    (hsmall : δ ^ (ζ / 2 - q₀ - t) ≤ 16 / H) :
    384 * δ ^ (-q₀) ≤ 6144 * (δ ^ t / H) * δ ^ (-ζ / 2) := by
  have hh := mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hδ.le (t - ζ / 2))
  have hleft : δ ^ (ζ / 2 - q₀ - t) * δ ^ (t - ζ / 2) = δ ^ (-q₀) := by
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  rw [hleft] at hh
  have hright : (16 / H) * δ ^ (t - ζ / 2) =
      (16 / H) * (δ ^ t * δ ^ (-ζ / 2)) := by
    congr 1
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  rw [hright] at hh
  calc
    _ ≤ 384 * ((16 / H) * (δ ^ t * δ ^ (-ζ / 2))) :=
      mul_le_mul_of_nonneg_left hh (by norm_num)
    _ = _ := by ring

namespace BlockNetData

variable {σ ω ζ δ ε b ρ c β τ den k Cnet e u t q₀ : ℝ} {p n d : ℕ}
  {x v : Fin n → V} {Y : Fin n → Set V}
  {D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y}
  {R : Finset (Fin D.L)} {G : D.NormalizedBlock R}
  {A : BlockAngularData D R G β τ} {hk : 0 < k}
  {F : BlockFirstFilling A (δ ^ t / firstFillingMassConstant) den k hk}

/-- Each high carrier has enough original packet shading to support a
common cut at the prescribed large multiplicity. -/
theorem carrier_high_overlap_budget
    (N : BlockNetData (σ := σ) F Cnet e (δ ^ (-u)) (δ ^ (-ζ / 2)) d)
    (hδ : 0 < δ) (hR : R.Nonempty)
    (hsmall : δ ^ (ζ / 2 - q₀ - t) ≤ 16 / firstFillingMassConstant)
    {l : Fin A.labels.card} (hl : l ∈ N.highLabels) (j : Fin (N.N l)) :
    O (δ ^ (-q₀)) * μ (N.carrier l j) ≤
      (1 / 2 : ENNReal) * ∑ i, μ (N.piece l j i) := by
  have hl' : l ∈ F.good := (Finset.mem_filter.mp hl).1
  have hH : 0 < firstFillingMassConstant := by norm_num [firstFillingMassConstant]
  have hlam : 0 < δ ^ t / firstFillingMassConstant := by positivity
  have hJ := F.volumeFactor_pos hδ hR
  have hB := F.radius_pos hδ hR
  have hρ := (D.dimensions hδ).2.1
  have hscalar := high_carrier_scalar hδ hH hsmall
  have hhigh := N.high_fibre_weight hδ hl
  have hineq : 384 * δ ^ (-q₀) * (4 * F.radius) ^ 2 ≤
      6144 * (δ ^ t / firstFillingMassConstant) *
        ((N.size l : ℝ) * (F.volumeFactor * (ρ ^ 2 / 64))) := by
    exact (mul_le_mul_of_nonneg_right hscalar (sq_nonneg _)).trans
      (by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hhigh.le
          (show 0 ≤ 6144 * (δ ^ t / firstFillingMassConstant) by positivity))
  have hJ0 : O F.volumeFactor ≠ 0 := (ENNReal.ofReal_pos.mpr hJ).ne'
  apply (ENNReal.mul_le_mul_iff_left hJ0 ENNReal.ofReal_ne_top).mp
  calc
    (O (δ ^ (-q₀)) * μ (N.carrier l j)) * O F.volumeFactor =
        O (δ ^ (-q₀)) * (O F.volumeFactor * μ (N.carrier l j)) := by ring
    _ ≤ O (δ ^ (-q₀)) * O (384 * (4 * F.radius) ^ 2) :=
      mul_le_mul' le_rfl (N.carrier_volume hδ hR hlam hl' j)
    _ = O (384 * δ ^ (-q₀) * (4 * F.radius) ^ 2) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]
      congr 1
      ring
    _ ≤ O (6144 * (δ ^ t / firstFillingMassConstant) *
        ((N.size l : ℝ) * (F.volumeFactor * (ρ ^ 2 / 64)))) :=
      ENNReal.ofReal_le_ofReal hineq
    _ = ((1 / 2 : ENNReal) * O (48 * (δ ^ t / firstFillingMassConstant) *
        (2 * ρ) ^ 2 * (N.size l : ℝ))) * O F.volumeFactor := by
      have hhalf : (1 / 2 : ENNReal) = O (1 / 2) := by
        norm_num [O, ENNReal.ofReal_div_of_pos]
      rw [hhalf, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    _ ≤ ((1 / 2 : ENNReal) * ∑ i, μ (N.piece l j i)) * O F.volumeFactor :=
      mul_le_mul' (mul_le_mul' le_rfl (N.piece_mass hl' j)) le_rfl

/-- Carrier components have positive finite mass, as needed for measurable
angular selection after the common overlap cut. -/
theorem piece_mass_pos_finite
    (N : BlockNetData (σ := σ) F Cnet e (δ ^ (-u)) (δ ^ (-ζ / 2)) d)
    (hδ : 0 < δ) {l : Fin A.labels.card} (hl : l ∈ F.good) (j : Fin (N.N l)) :
    0 < ∑ i, μ (N.piece l j i) ∧ (∑ i, μ (N.piece l j i)) ≠ ⊤ := by
  have hρ := (D.dimensions hδ).2.1
  have hH : 0 < firstFillingMassConstant := by norm_num [firstFillingMassConstant]
  have hq : (0 : ℝ) < N.size l := Nat.cast_pos.mpr (N.net l hl).2.1
  constructor
  · exact (ENNReal.ofReal_pos.mpr (by positivity :
      0 < 48 * (δ ^ t / firstFillingMassConstant) * (2 * ρ) ^ 2 * (N.size l : ℝ))).trans_le
        (N.piece_mass hl j)
  · apply ENNReal.sum_ne_top.mpr
    intro i _
    exact measure_ne_top_of_subset ((N.piece_subset l j i).trans
      ((A.normalizedPiece_subset l i).trans ((G.contained i).trans (G.unit_ball i))))
      (measure_ball_lt_top (μ := volume)).ne

end BlockNetData
end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
