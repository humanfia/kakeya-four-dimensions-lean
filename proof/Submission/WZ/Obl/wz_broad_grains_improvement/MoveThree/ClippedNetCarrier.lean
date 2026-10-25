-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.ClippedNetCarrier.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/ClippedNetCarrier.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PhysicalCarrierBox
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PhysicalCarrierPieces
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.RenormScalars

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_separated_cover_refinement (enumerate)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (boxAxis boxAxis_norm)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (unit norm_unit)

noncomputable section
namespace PhysicalCarrierBox

variable {σ ω ζ δ ε b ρ c β τ lam den k Cnet e Λ Kc loss density : ℝ} {p n d : ℕ}
  {x v : Fin n → V} {Y : Fin n → Set V}
  {D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y}
  {R : Finset (Fin D.L)} {G : D.NormalizedBlock R}
  {A : BlockAngularData D R G β τ} {hk : 0 < k}
  {F : BlockFirstFilling A lam den k hk}
  {N : BlockNetData (σ := σ) F Cnet e Λ Kc d}
  {l : Fin A.labels.card} {j : Fin (N.N l)}

theorem short_pos (B : PhysicalCarrierBox N loss density l j) (hδ : 0 < δ) :
    0 < B.short := (D.dimensions hδ).1.trans_le B.lower

def map (B : PhysicalCarrierBox N loss density l j) (hδ : 0 < δ) : V ≃ᵃ[ℝ] V :=
  carrierAffine (lt_min (B.short_pos hδ)
    (mul_pos (D.dimensions hδ).2.1 (D.dimensions hδ).2.2.2.1))
    (D.dimensions hδ).2.2.2.1 (D.dimensions hδ).2.1
    (D.z G.natural_anchor) B.center B.frame

def slabWidth (B : PhysicalCarrierBox N loss density l j) : ℝ :=
  ρ * B.short / (4 * min B.short (ρ * c))

def direction (B : PhysicalCarrierBox N loss density l j) (hδ : 0 < δ)
    (i : Fin R.card) : V := unit ((B.map hδ).linear (boxAxis (D.e (enumerate R i)) 2))

theorem whole_body (B : PhysicalCarrierBox N loss density l j) (hδ : 0 < δ)
    (hl : l ∈ F.good) (i : Fin R.card) (hi : i ∈ N.fibre l j) :
    P D.a (ρ * c) c (D.z (enumerate R i)) (D.e (enumerate R i)) ⊆
      P B.short B.middle (8 * c) B.center B.frame ∩ ball (D.z G.natural_anchor) (2 * c) :=
  subset_inter ((subset_inter (N.physical_body_in_carrier hl j i hi)
    (G.physical_body_ball hδ i)).trans B.enclosure) (G.physical_body_ball hδ i)

theorem inverse_bound (B : PhysicalCarrierBox N loss density l j) (hδ : 0 < δ)
    (u : V) : ‖(B.map hδ).linear.symm u‖ ≤ (4 * c) * ‖u‖ :=
  carrier_linear_inverse (lt_min (B.short_pos hδ)
    (mul_pos (D.dimensions hδ).2.1 (D.dimensions hδ).2.2.2.1))
    (D.dimensions hδ).2.2.2.1 (min_le_right _ _) B.frame (B.map hδ).linear
    (carrierAffine_linear _ _ _ _ _ _) u

theorem direction_norm (B : PhysicalCarrierBox N loss density l j) (hδ : 0 < δ)
    (i : Fin R.card) : ‖B.direction hδ i‖ = 1 := by
  apply norm_unit
  intro hz
  have haxis : boxAxis (D.e (enumerate R i)) 2 = 0 :=
    (B.map hδ).linear.injective (hz.trans (map_zero _).symm)
  have hh := boxAxis_norm (D.e (enumerate R i)) 2
  rw [haxis, norm_zero] at hh
  norm_num at hh

theorem linear_data (B : PhysicalCarrierBox N loss density l j) (hδ : 0 < δ)
    (hl : l ∈ F.good) (i : Fin R.card) (hi : i ∈ N.fibre l j) :
    ‖(B.map hδ).linear (boxAxis (D.e (enumerate R i)) 2)‖ ≤ c⁻¹ ∧
      ‖B.direction hδ i - B.frame (boxAxis (D.e (enumerate R i)) 2)‖ ≤ 2 * ρ := by
  obtain ⟨ha, hρ, hρ1, hc, _⟩ := D.dimensions hδ
  exact (clipped_carrier_linear_data ha.le hρ hρ1 hc D.grains.2.1 (B.short_pos hδ)
    (D.z (enumerate R i)) B.center (D.e (enumerate R i)) B.frame (B.map hδ).linear
    ((B.whole_body hδ hl i hi).trans inter_subset_left)
    (carrierAffine_linear _ _ _ _ _ _)).2.2.2

theorem whole_tube (B : PhysicalCarrierBox N loss density l j) (hδ : 0 < δ)
    (hl : l ∈ F.good) (i : Fin R.card) (hi : i ∈ N.fibre l j) :
    B.map hδ '' P D.a (ρ * c) c (D.z (enumerate R i)) (D.e (enumerate R i)) ⊆
      T (2 * ρ) (B.map hδ (D.z (enumerate R i)) - (1 / 2 : ℝ) • B.direction hδ i)
        (B.direction hδ i) := by
  obtain ⟨ha, hρ, hρ1, hc, _⟩ := D.dimensions hδ
  exact (clipped_carrier_grain_tube ha.le hρ hρ1 hc D.grains.2.1 (B.short_pos hδ)
    (D.z (enumerate R i)) (D.z G.natural_anchor) B.center
    (D.e (enumerate R i)) B.frame ((B.whole_body hδ hl i hi).trans inter_subset_left)).2.2.2.2

theorem whole_ball_slab (B : PhysicalCarrierBox N loss density l j) (hδ : 0 < δ)
    (hl : l ∈ F.good) (hsmall : B.slabWidth ≤ 1 / 8)
    (i : Fin R.card) (hi : i ∈ N.fibre l j) :
    B.map hδ '' P D.a (ρ * c) c (D.z (enumerate R i)) (D.e (enumerate R i)) ⊆
      ball (0 : V) 1 ∩ {p | |p 0| ≤ B.slabWidth / 2} := by
  apply (image_mono (B.whole_body hδ hl i hi)).trans
  exact carrierAffine_ball_and_slab _ _ _ hsmall _ _ _

theorem direction_slab (B : PhysicalCarrierBox N loss density l j) (hδ : 0 < δ)
    (hl : l ∈ F.good) (i : Fin R.card) (hi : i ∈ N.fibre l j) :
    |B.direction hδ i 0| ≤ 4 * B.slabWidth := by
  obtain ⟨ha, hρ, _, hc, _⟩ := D.dimensions hδ
  exact clipped_carrier_normal_bound ha.le hρ hc (B.short_pos hδ)
    (D.z (enumerate R i)) (D.z G.natural_anchor) B.center
    (D.e (enumerate R i)) B.frame ((B.whole_body hδ hl i hi).trans inter_subset_left)

theorem slabWidth_pos (B : PhysicalCarrierBox N loss density l j) (hδ : 0 < δ) :
    0 < B.slabWidth := by
  obtain ⟨ha, hρ, _, hc, _⟩ := D.dimensions hδ
  have hB := B.short_pos hδ
  dsimp [slabWidth]
  positivity

theorem slabWidth_bound (B : PhysicalCarrierBox N loss density l j) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hloss : 0 ≤ loss) : B.slabWidth ≤ δ ^ (-loss) * (2 * ρ) :=
  renormS_slab hδ hδ1 hloss D.grains.1 D.grains.2.1 B.lower B.thin
    (D.dimensions hδ).2.1

theorem map_volume (B : PhysicalCarrierBox N loss density l j) (hδ : 0 < δ) (U : Set V) :
    μ (B.map hδ '' U) = O (ρ / (64 * min B.short (ρ * c) * c ^ 2)) * μ U :=
  carrierAffine_volume _ _ _ _ _ _ U

end PhysicalCarrierBox
end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
