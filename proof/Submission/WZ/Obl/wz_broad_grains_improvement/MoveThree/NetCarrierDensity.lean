-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.NetCarrierDensity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/NetCarrierDensity.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.NetCarrierData
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.BlockDensityUpper

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_transverse_cell_weighted_cover
  (prism cTube axisDir prism_subset_cTube)

noncomputable section
namespace BlockNetData

variable {σ ω ζ δ ε b ρ c β τ lam den k Cnet e Λ Kc : ℝ} {p n d : ℕ}
  {x v : Fin n → V} {Y : Fin n → Set V}
  {D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y}
  {R : Finset (Fin D.L)} {G : D.NormalizedBlock R}
  {A : BlockAngularData D R G β τ} {hk : 0 < k}
  {F : BlockFirstFilling A lam den k hk}

def physicalCarrier (N : BlockNetData (σ := σ) F Cnet e Λ Kc d)
    (l : Fin A.labels.card) (j : Fin (N.N l)) : Set V := G.affine ⁻¹' N.carrier l j

def physicalCarrierShade (N : BlockNetData (σ := σ) F Cnet e Λ Kc d)
    (l : Fin A.labels.card) (j : Fin (N.N l)) : Set V :=
  G.affine ⁻¹' (N.carrier l j ∩ ⋃ i, A.normalizedPiece l i)

theorem carrier_convex (N : BlockNetData (σ := σ) F Cnet e Λ Kc d)
    (l : Fin A.labels.card) (j : Fin (N.N l)) : Convex ℝ (N.carrier l j) :=
  (WangZahlLot.Obl.wz_regular_transverse_affine_cells.tube_convex _ _ _).affine_preimage
    (F.map l).toAffineMap

theorem physicalCarrier_convex (N : BlockNetData (σ := σ) F Cnet e Λ Kc d)
    (l : Fin A.labels.card) (j : Fin (N.N l)) : Convex ℝ (N.physicalCarrier l j) :=
  (N.carrier_convex l j).affine_preimage G.affine.toAffineMap

/-- The first dense representative makes its entire carrier dense in the
original packet union, even after the net chooses an equal-cardinality fibre. -/
theorem carrier_density (N : BlockNetData (σ := σ) F Cnet e Λ Kc d)
    (hδ : 0 < δ) (hR : R.Nonempty) (hlam : 0 < lam) (hden : 0 ≤ den)
    {l : Fin A.labels.card} (hl : l ∈ F.good) (j : Fin (N.N l)) :
    O (den * k / (16000 * 6144)) * μ (N.carrier l j) ≤
      μ (N.carrier l j ∩ ⋃ i, A.normalizedPiece l i) := by
  have hB := F.radius_pos hδ hR
  have hJ := F.volumeFactor_pos hδ hR
  have hrep := (N.net l hl).2.2.1 j
  obtain ⟨_, horth, _, _, hmass⟩ := (F.filling l hl).2.2.2 (N.representative l j) hrep
  have hsub : prism F.radius F.radius
      (F.map l (A.start (N.representative l j) + (1 / 2 : ℝ) • A.axis (N.representative l j)))
      (F.direction l (N.representative l j)) ⊆
      cTube F.radius
        (F.map l (A.start (N.representative l j) + (1 / 2 : ℝ) • A.axis (N.representative l j)))
        (F.direction l (N.representative l j)) := prism_subset_cTube hB.le le_rfl hB horth
  have hmass' : O ((den * k / 16000) * F.radius ^ 2) ≤
      μ (F.map l '' (N.carrier l j ∩ ⋃ i, A.normalizedPiece l i)) := by
    apply hmass.trans
    apply measure_mono
    rintro z ⟨hp, q, hq, rfl⟩
    exact ⟨q, ⟨hsub hp, hq⟩, rfl⟩
  have hJ0 : O F.volumeFactor ≠ 0 := (ENNReal.ofReal_pos.mpr hJ).ne'
  apply (ENNReal.mul_le_mul_iff_left hJ0 ENNReal.ofReal_ne_top).mp
  calc
    (O (den * k / (16000 * 6144)) * μ (N.carrier l j)) * O F.volumeFactor =
        O (den * k / (16000 * 6144)) * (O F.volumeFactor * μ (N.carrier l j)) := by ring
    _ ≤ O (den * k / (16000 * 6144)) * O (384 * (4 * F.radius) ^ 2) :=
      mul_le_mul' le_rfl (N.carrier_volume hδ hR hlam hl j)
    _ = O ((den * k / 16000) * F.radius ^ 2) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ den * k / (16000 * 6144))]
      congr 1
      ring
    _ ≤ _ := hmass'
    _ = μ (N.carrier l j ∩ ⋃ i, A.normalizedPiece l i) * O F.volumeFactor := by
      rw [F.map_volume, mul_comm]

theorem physicalCarrier_density (N : BlockNetData (σ := σ) F Cnet e Λ Kc d)
    (hδ : 0 < δ) (hR : R.Nonempty) (hlam : 0 < lam) (hden : 0 ≤ den)
    {l : Fin A.labels.card} (hl : l ∈ F.good) (j : Fin (N.N l)) :
    O (den * k / (16000 * 6144)) * μ (N.physicalCarrier l j) ≤
      μ (N.physicalCarrierShade l j) := by
  obtain ⟨ha, hρ, _, hc, _⟩ := D.dimensions hδ
  have hJ : 0 < ρ / (64 * D.a * c ^ 2) := by positivity
  have hpre (W : Set V) : O (ρ / (64 * D.a * c ^ 2)) * μ (G.affine ⁻¹' W) = μ W := by
    rw [← G.jacobian, image_preimage_eq _ G.affine.surjective]
  apply (ENNReal.mul_le_mul_iff_left (ENNReal.ofReal_pos.mpr hJ).ne' ENNReal.ofReal_ne_top).mp
  change (O (den * k / (16000 * 6144)) * μ (G.affine ⁻¹' N.carrier l j)) *
      O (ρ / (64 * D.a * c ^ 2)) ≤
    μ (G.affine ⁻¹' (N.carrier l j ∩ ⋃ i, A.normalizedPiece l i)) *
      O (ρ / (64 * D.a * c ^ 2))
  rw [mul_assoc, mul_comm (μ (G.affine ⁻¹' N.carrier l j)), hpre,
    mul_comm (μ (G.affine ⁻¹' (N.carrier l j ∩ ⋃ i, A.normalizedPiece l i))), hpre]
  exact N.carrier_density hδ hR hlam hden hl j

theorem physicalCarrierShade_ambient (N : BlockNetData (σ := σ) F Cnet e Λ Kc d)
    (l : Fin A.labels.card) (j : Fin (N.N l)) :
    N.physicalCarrierShade l j ⊆ ⋃ i, Y i := by
  rintro q ⟨_, hq⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp hq
  have hp := A.normalizedPiece_subset l i hi
  have hp' : q ∈ D.Hg (WangZahlLot.Obl.wz_separated_cover_refinement.enumerate R i) :=
    (G.affine.injective.mem_set_image).mp hp
  exact D.grain_subset_ambient _ hp'

end BlockNetData
end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
