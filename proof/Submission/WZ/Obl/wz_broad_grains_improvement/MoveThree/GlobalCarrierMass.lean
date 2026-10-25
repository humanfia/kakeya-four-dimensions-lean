-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.GlobalCarrierMass.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/GlobalCarrierMass.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.NetCarrierMass
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PhysicalCarrierPieces
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.AngularBlockFamily

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_separated_cover_refinement (enumerate)

noncomputable section
namespace HighNetBlock

variable {σ ω ζ δ ξ b ρ c β τ Cnet e t ν : ℝ} {p n d : ℕ}
  {x v : Fin n → V} {Y : Fin n → Set V}
  {D : ConcentratedGrainData ω ζ δ ξ b ρ c p n x v Y}
  {R : Finset (Fin D.L)} {G : D.NormalizedBlock R}
  {A : BlockAngularData D R G β τ}

/-- Undoing the common block Jacobian gives exactly the same retention
factor for the actual physical carrier pieces. -/
theorem physical_carrier_mass_retention (H : HighNetBlock A σ Cnet e t ν d)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hmass : τ + 21 * ξ / 40 ≤ t) :
    O (384 / firstFillingMassConstant ^ 2 * δ ^ (2 * e + 3 * t)) *
        ∑ i, μ (D.Hg (enumerate R i)) ≤
      ∑ l ∈ H.nets.highLabels, ∑ j, ∑ i, μ (H.nets.physicalPiece l j i) := by
  obtain ⟨ha, hρ, _, hc, _⟩ := D.dimensions hδ
  have hJ : 0 < ρ / (64 * D.a * c ^ 2) := by positivity
  have hphys : O (ρ / (64 * D.a * c ^ 2)) *
      (∑ l ∈ H.nets.highLabels, ∑ j, ∑ i, μ (H.nets.physicalPiece l j i)) =
      ∑ l ∈ H.nets.highLabels, ∑ j, ∑ i, μ (H.nets.piece l j i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact G.preimage_sum_volume _
  apply (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hJ).ne'
    ENNReal.ofReal_ne_top).mp
  rw [hphys]
  calc
    _ = O (384 / firstFillingMassConstant ^ 2 * δ ^ (2 * e + 3 * t)) *
        ∑ i, μ (D.normalizedShade R G.affine i) := by
      simp_rw [ConcentratedGrainData.normalizedShade, G.jacobian]
      rw [← Finset.mul_sum]
      ac_rfl
    _ ≤ _ := H.carrier_mass_retention hδ hδ1 hmass

end HighNetBlock
namespace AngularBlockFamily

variable {σ ω ζ δ ξ b ρ c β τ Cnet e t ν : ℝ} {p n d : ℕ}
  {x v : Fin n → V} {Y : Fin n → Set V}
  {D : ConcentratedGrainData ω ζ δ ξ b ρ c p n x v Y}

/-- The selected disjoint blocks retain their balanced fraction of the
full old-grain mass before any angular selection. -/
theorem block_mass (F : AngularBlockFamily D β τ) (hδ : 0 < δ) :
    O (δ ^ (ξ / 4 + ξ / 40) / 2) * ∑ j, μ (D.Hg j) ≤
      ∑ R : F.blocks, ∑ i : Fin R.val.card, μ (D.Hg (enumerate R.val i)) := by
  classical
  have hsum : ∑ j ∈ F.blocks.biUnion id, μ (D.Hg j) =
      ∑ R : F.blocks, ∑ i : Fin R.val.card, μ (D.Hg (enumerate R.val i)) := by
    rw [Finset.sum_biUnion F.disjoint]
    change (∑ R ∈ F.blocks, ∑ j ∈ R, μ (D.Hg j)) = _
    rw [← Finset.sum_coe_sort F.blocks (fun R => ∑ j ∈ R, μ (D.Hg j))]
    apply Finset.sum_congr rfl
    intro R _
    rw [← Finset.sum_coe_sort R.val (fun j => μ (D.Hg j))]
    exact (Equiv.sum_comp R.val.equivFin.symm (fun j => μ (D.Hg j.val))).symm
  calc
    _ = O (δ ^ (ξ / 80) / 2) *
        (O (δ ^ (ξ / 4 + ξ / 80)) * ∑ j, μ (D.Hg j)) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      rw [show ξ / 4 + ξ / 40 = ξ / 80 + (ξ / 4 + ξ / 80) by ring,
        Real.rpow_add hδ]
      ring
    _ ≤ O (δ ^ (ξ / 80) / 2) * ∑ j ∈ D.Q, μ (D.Hg j) :=
      mul_le_mul' le_rfl D.retained
    _ ≤ ∑ j ∈ F.blocks.biUnion id, μ (D.Hg j) :=
      D.retained_block_mass hδ F.blocks F.subset F.card
    _ = _ := hsum

/-- The high physical carriers of all selected blocks retain a uniform
fraction of the original old-grain mass. The carriers may have unrelated
angular scales or cardinalities. -/
theorem physical_carrier_mass (F : AngularBlockFamily D β τ)
    (H : ∀ R : F.blocks, HighNetBlock (F.angular R) σ Cnet e t ν d)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hmass : τ + 21 * ξ / 40 ≤ t) :
    O (192 / firstFillingMassConstant ^ 2 * δ ^ (2 * e + 3 * t + ξ / 4 + ξ / 40)) *
        ∑ j, μ (D.Hg j) ≤
      ∑ R : F.blocks, ∑ l ∈ (H R).nets.highLabels,
        ∑ j, ∑ i, μ ((H R).nets.physicalPiece l j i) := by
  calc
    _ = O (384 / firstFillingMassConstant ^ 2 * δ ^ (2 * e + 3 * t)) *
        (O (δ ^ (ξ / 4 + ξ / 40) / 2) * ∑ j, μ (D.Hg j)) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      rw [show 2 * e + 3 * t + ξ / 4 + ξ / 40 =
        (2 * e + 3 * t) + (ξ / 4 + ξ / 40) by ring, Real.rpow_add hδ]
      ring
    _ ≤ O (384 / firstFillingMassConstant ^ 2 * δ ^ (2 * e + 3 * t)) *
        ∑ R : F.blocks, ∑ i : Fin R.val.card, μ (D.Hg (enumerate R.val i)) :=
      mul_le_mul' le_rfl (F.block_mass hδ)
    _ = ∑ R : F.blocks, O (384 / firstFillingMassConstant ^ 2 * δ ^ (2 * e + 3 * t)) *
        ∑ i : Fin R.val.card, μ (D.Hg (enumerate R.val i)) := Finset.mul_sum _ _ _
    _ ≤ _ := Finset.sum_le_sum fun R _ => (H R).physical_carrier_mass_retention hδ hδ1 hmass

end AngularBlockFamily
end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
