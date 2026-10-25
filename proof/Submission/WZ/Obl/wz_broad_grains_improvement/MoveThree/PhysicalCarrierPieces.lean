-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.PhysicalCarrierPieces.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/PhysicalCarrierPieces.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.NetCarrierOverlap
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.NetCarrierDensity

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_separated_cover_refinement (enumerate)

noncomputable section
namespace ConcentratedGrainData.NormalizedBlock

variable {ω ζ δ ε b ρ c : ℝ} {p n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}
  {D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y}
  {R : Finset (Fin D.L)}

theorem preimage_volume (G : D.NormalizedBlock R) (W : Set V) :
    O (ρ / (64 * D.a * c ^ 2)) * μ (G.affine ⁻¹' W) = μ W := by
  rw [← G.jacobian, image_preimage_eq _ G.affine.surjective]

theorem preimage_sum_volume (G : D.NormalizedBlock R) {ι : Type*} [Fintype ι]
    (W : ι → Set V) : O (ρ / (64 * D.a * c ^ 2)) * (∑ i, μ (G.affine ⁻¹' W i)) =
      ∑ i, μ (W i) := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => G.preimage_volume _)

end ConcentratedGrainData.NormalizedBlock
namespace BlockNetData

variable {σ ω ζ δ ε b ρ c β τ lam den k Cnet e Λ Kc : ℝ} {p n d : ℕ}
  {x v : Fin n → V} {Y : Fin n → Set V}
  {D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y}
  {R : Finset (Fin D.L)} {G : D.NormalizedBlock R}
  {A : BlockAngularData D R G β τ} {hk : 0 < k}
  {F : BlockFirstFilling A lam den k hk}

def physicalPiece (N : BlockNetData (σ := σ) F Cnet e Λ Kc d)
    (l : Fin A.labels.card) (j : Fin (N.N l)) (i : Fin R.card) : Set V :=
  G.affine ⁻¹' N.piece l j i

theorem physicalPiece_measurable (N : BlockNetData (σ := σ) F Cnet e Λ Kc d)
    (l : Fin A.labels.card) (j : Fin (N.N l)) (i : Fin R.card) :
    MeasurableSet (N.physicalPiece l j i) :=
  (N.piece_measurable l j i).preimage G.affine.toContinuousAffineEquiv.continuous.measurable

theorem physicalPiece_subset (N : BlockNetData (σ := σ) F Cnet e Λ Kc d)
    (l : Fin A.labels.card) (j : Fin (N.N l)) (i : Fin R.card) :
    N.physicalPiece l j i ⊆ D.Hg (enumerate R i) := by
  intro q hq
  exact (G.affine.injective.mem_set_image).mp
    (A.normalizedPiece_subset l i (N.piece_subset l j i hq))

theorem physicalPiece_outside (N : BlockNetData (σ := σ) F Cnet e Λ Kc d)
    (l : Fin A.labels.card) (j : Fin (N.N l)) (i : Fin R.card) (hi : i ∉ N.fibre l j) :
    N.physicalPiece l j i = ∅ := by
  simp [physicalPiece, piece, hi]

theorem physicalPiece_in_carrier (N : BlockNetData (σ := σ) F Cnet e Λ Kc d)
    {l : Fin A.labels.card} (hl : l ∈ F.good) (j : Fin (N.N l)) (i : Fin R.card) :
    N.physicalPiece l j i ⊆ N.physicalCarrier l j :=
  preimage_mono (N.piece_in_carrier hl j i)

theorem physical_piece_mass (N : BlockNetData (σ := σ) F Cnet e Λ Kc d)
    (hδ : 0 < δ) (hlam : 0 ≤ lam) {l : Fin A.labels.card} (hl : l ∈ F.good)
    (j : Fin (N.N l)) :
    O (12288 * lam * (D.a * (ρ * c) * c) * (N.size l : ℝ)) ≤
      ∑ i, μ (N.physicalPiece l j i) := by
  obtain ⟨ha, hρ, _, hc, _⟩ := D.dimensions hδ
  have hJ : 0 < ρ / (64 * D.a * c ^ 2) := by positivity
  apply (ENNReal.mul_le_mul_iff_left (ENNReal.ofReal_pos.mpr hJ).ne' ENNReal.ofReal_ne_top).mp
  rw [mul_comm _ (O (ρ / (64 * D.a * c ^ 2))),
    ← ENNReal.ofReal_mul hJ.le]
  have he : ρ / (64 * D.a * c ^ 2) *
      (12288 * lam * (D.a * (ρ * c) * c) * (N.size l : ℝ)) =
      48 * lam * (2 * ρ) ^ 2 * (N.size l : ℝ) := by field_simp; ring
  rw [he, mul_comm _ (O (ρ / (64 * D.a * c ^ 2)))]
  change O (48 * lam * (2 * ρ) ^ 2 * (N.size l : ℝ)) ≤
    O (ρ / (64 * D.a * c ^ 2)) * (∑ i, μ (G.affine ⁻¹' N.piece l j i))
  rw [G.preimage_sum_volume]
  exact N.piece_mass hl j

theorem physical_piece_mass_pos_finite (N : BlockNetData (σ := σ) F Cnet e Λ Kc d)
    (hδ : 0 < δ) (hlam : 0 < lam) {l : Fin A.labels.card} (hl : l ∈ F.good)
    (j : Fin (N.N l)) :
    0 < ∑ i, μ (N.physicalPiece l j i) ∧ (∑ i, μ (N.physicalPiece l j i)) ≠ ⊤ := by
  obtain ⟨ha, hρ, _, hc, _⟩ := D.dimensions hδ
  have hq : (0 : ℝ) < N.size l := Nat.cast_pos.mpr (N.net l hl).2.1
  constructor
  · exact (ENNReal.ofReal_pos.mpr (by positivity :
      0 < 12288 * lam * (D.a * (ρ * c) * c) * (N.size l : ℝ))).trans_le
        (N.physical_piece_mass hδ hlam.le hl j)
  · apply ENNReal.sum_ne_top.mpr
    intro i _
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    apply (measure_mono ((N.physicalPiece_subset l j i).trans
      (D.grains.2.2.2.2.1 (enumerate R i)).2.1)).trans_eq
    exact WangZahlLot.Obl.wz_clustered_cover_volume_gain.frozen_prism_volume
      ha.le (mul_pos hρ hc).le hc.le _ _

end BlockNetData

namespace BlockNetData

variable {σ ω ζ δ ε b ρ c β τ den k Cnet e u t q₀ : ℝ} {p n d : ℕ}
  {x v : Fin n → V} {Y : Fin n → Set V}
  {D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y}
  {R : Finset (Fin D.L)} {G : D.NormalizedBlock R}
  {A : BlockAngularData D R G β τ} {hk : 0 < k}
  {F : BlockFirstFilling A (δ ^ t / firstFillingMassConstant) den k hk}

theorem physical_carrier_high_overlap_budget
    (N : BlockNetData (σ := σ) F Cnet e (δ ^ (-u)) (δ ^ (-ζ / 2)) d)
    (hδ : 0 < δ) (hR : R.Nonempty)
    (hsmall : δ ^ (ζ / 2 - q₀ - t) ≤ 16 / firstFillingMassConstant)
    {l : Fin A.labels.card} (hl : l ∈ N.highLabels) (j : Fin (N.N l)) :
    O (δ ^ (-q₀)) * μ (N.physicalCarrier l j) ≤
      (1 / 2 : ENNReal) * ∑ i, μ (N.physicalPiece l j i) := by
  obtain ⟨ha, hρ, _, hc, _⟩ := D.dimensions hδ
  have hJ : 0 < ρ / (64 * D.a * c ^ 2) := by positivity
  apply (ENNReal.mul_le_mul_iff_left (ENNReal.ofReal_pos.mpr hJ).ne' ENNReal.ofReal_ne_top).mp
  change (O (δ ^ (-q₀)) * μ (G.affine ⁻¹' N.carrier l j)) *
      O (ρ / (64 * D.a * c ^ 2)) ≤
    ((1 / 2 : ENNReal) * ∑ i, μ (G.affine ⁻¹' N.piece l j i)) *
      O (ρ / (64 * D.a * c ^ 2))
  rw [mul_assoc, mul_comm (μ (G.affine ⁻¹' N.carrier l j)), G.preimage_volume,
    mul_assoc, mul_comm (∑ i, μ (G.affine ⁻¹' N.piece l j i)), G.preimage_sum_volume]
  exact N.carrier_high_overlap_budget hδ hR hsmall hl j

end BlockNetData
end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
