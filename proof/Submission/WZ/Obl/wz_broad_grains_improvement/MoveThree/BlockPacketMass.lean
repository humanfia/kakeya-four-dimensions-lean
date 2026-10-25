-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.BlockPacketMass.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/BlockPacketMass.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.BlockPacketGeometry

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open scoped Classical
open WangZahlLot.Obl.wz_broad_grains_initialization (packetPiece)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (unit)
open WangZahlLot.Obl.wz_separated_cover_refinement (enumerate_sum)

noncomputable section
namespace BlockAngularData

variable {ω ζ δ ε b ρ c β τ : ℝ} {p n : ℕ} {x v : Fin n → V}
  {Y : Fin n → Set V} {D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y}
  {R : Finset (Fin D.L)} {G : D.NormalizedBlock R}

theorem normalizedPiece_mass_sum (A : BlockAngularData D R G β τ) (hδ : 0 < δ) :
    (∑ l, ∑ i, μ (A.normalizedPiece l i)) = ∑ i, μ (A.shade i) := by
  have hρ : 0 < ρ := (D.dimensions hδ).2.1
  have ht i : A.shade i ⊆ T (2 * ρ) (A.unitStart i) (unit (A.axis i)) :=
    (A.refinement.1 i).2.trans ((G.contained i).trans (A.unit_body_tube i))
  have hh := A.refinement.piece_mass (x := A.unitStart)
    ((by positivity : 0 < 2 * ρ).trans_le A.lower) A.lower A.unit_axis_norm ht
  change (∑ l ∈ A.labels, ∑ i, μ (packetPiece A.scale (fun i => unit (A.axis i))
    A.shade A.packets A.center l i)) = _ at hh
  rw [← hh]
  exact enumerate_sum A.labels (fun l => ∑ i, μ (packetPiece A.scale
    (fun i => unit (A.axis i)) A.shade A.packets A.center l i))

theorem normalizedPiece_mass_lower (A : BlockAngularData D R G β τ) (hδ : 0 < δ) :
    O (δ ^ (τ + 21 * ε / 40) * (ρ ^ 2 / 64) * R.card) ≤
      ∑ l, ∑ i, μ (A.normalizedPiece l i) := by
  have hdense : O (δ ^ (21 * ε / 40) * R.card * (ρ ^ 2 / 64)) ≤
      ∑ i, μ (D.normalizedShade R G.affine i) := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => G.dense i)
    simp only [G.body_volume, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hh
    convert hh using 1
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  rw [A.normalizedPiece_mass_sum hδ]
  apply le_trans _ A.mass
  apply le_trans _ (mul_le_mul' le_rfl hdense)
  rw [← ENNReal.ofReal_mul (by positivity), Real.rpow_add hδ]
  exact le_of_eq (by congr 1; ring)

theorem normalizedPiece_mass_upper (A : BlockAngularData D R G β τ)
    (l : Fin A.labels.card) :
    (∑ i, μ (A.normalizedPiece l i)) ≤ O ((ρ ^ 2 / 64) * (A.active l).card) := by
  have hs : (∑ i, μ (A.normalizedPiece l i)) =
      ∑ i ∈ A.active l, μ (A.normalizedPiece l i) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    rw [A.normalizedPiece_outside l i hi]
    exact measure_empty
  rw [hs]
  calc
    _ ≤ ∑ _i ∈ A.active l, O (ρ ^ 2 / 64) := Finset.sum_le_sum fun i _ =>
      (measure_mono ((A.normalizedPiece_subset l i).trans (G.contained i))).trans_eq
        (G.body_volume i)
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [mul_comm, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]

theorem normalizedPiece_count_sum (A : BlockAngularData D R G β τ) (hδ : 0 < δ) :
    (∑ l, ((A.active l).card : ℝ)) ≤ (2 * 6 ^ 3 * 22 ^ 3 : ℝ) * R.card := by
  have hρ : 0 < ρ := (D.dimensions hδ).2.1
  have ht i : A.shade i ⊆ T (2 * ρ) (A.unitStart i) (unit (A.axis i)) :=
    (A.refinement.1 i).2.trans ((G.contained i).trans (A.unit_body_tube i))
  have hh := A.refinement.piece_card_sum (x := A.unitStart)
    ((by positivity : 0 < 2 * ρ).trans_le A.lower) A.lower A.unit_axis_norm ht
  change (∑ l ∈ A.labels, ({i | (packetPiece A.scale (fun i => unit (A.axis i))
    A.shade A.packets A.center l i).Nonempty}.ncard : ℝ)) ≤ _ at hh
  rw [← enumerate_sum A.labels (fun l => ({i | (packetPiece A.scale
    (fun i => unit (A.axis i)) A.shade A.packets A.center l i).Nonempty}.ncard : ℝ))] at hh
  simpa only [active, normalizedPiece, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred] using hh

end BlockAngularData
end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
