-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.PhysicalBlockGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/PhysicalBlockGeometry.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.NetCarrierDensity
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.ClippedCarrier

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (norm_sq_coords)
open WangZahlLot.Obl.wz_separated_cover_refinement (enumerate)

noncomputable section
namespace ConcentratedGrainData.NormalizedBlock

variable {ω ζ δ ε b ρ c : ℝ} {p n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}
  {D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y}
  {R : Finset (Fin D.L)}

/-- All whole old grains of a natural block lie within twice the old grain
length of its anchor, in the original coordinates. -/
theorem physical_body_ball (G : D.NormalizedBlock R) (hδ : 0 < δ) (i : Fin R.card) :
    P D.a (ρ * c) c (D.z (enumerate R i)) (D.e (enumerate R i)) ⊆
      ball (D.z G.natural_anchor) (2 * c) := by
  obtain ⟨ha, hρ, hρ1, hc, _⟩ := D.dimensions hδ
  have haρ : D.a ≤ D.a / ρ := (le_div_iff₀ hρ).mpr
    (mul_le_of_le_one_right ha.le hρ1)
  have hac : D.a / ρ ≤ c := (div_le_iff₀ hρ).mpr (by linarith [D.grains.2.1])
  intro q hq
  have hnear := G.natural_near i
  have hp : q ∈ P (2 * D.a / ρ) (2 * c) (2 * c)
      (D.z G.natural_anchor) (D.e G.natural_anchor) := by
    apply hnear
    exact ⟨hq.1.trans (by linarith), hq.2.1.trans (by linarith [D.grains.2.2.1]), hq.2.2⟩
  have hcoord (j : Fin 3) : |D.e G.natural_anchor (q - D.z G.natural_anchor) j| ≤ c := by
    fin_cases j
    · exact hp.1.trans (by convert hac using 1 <;> ring)
    · exact hp.2.1.trans (by linarith)
    · exact hp.2.2.trans (by linarith)
  have hs (j : Fin 3) : (D.e G.natural_anchor (q - D.z G.natural_anchor) j) ^ 2 ≤ c ^ 2 :=
    sq_le_sq.mpr (by simpa only [abs_of_pos hc] using hcoord j)
  have hn := norm_sq_coords (D.e G.natural_anchor (q - D.z G.natural_anchor))
  rw [(D.e G.natural_anchor).norm_map] at hn
  rw [mem_ball, dist_eq_norm]
  nlinarith [hs 0, hs 1, hs 2, norm_nonneg (q - D.z G.natural_anchor)]

end ConcentratedGrainData.NormalizedBlock
namespace BlockNetData

variable {σ ω ζ δ ε b ρ c β τ lam den k Cnet e Λ Kc : ℝ} {p n d : ℕ}
  {x v : Fin n → V} {Y : Fin n → Set V}
  {D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y}
  {R : Finset (Fin D.L)} {G : D.NormalizedBlock R}
  {A : BlockAngularData D R G β τ} {hk : 0 < k}
  {F : BlockFirstFilling A lam den k hk}

theorem physical_body_in_carrier (N : BlockNetData (σ := σ) F Cnet e Λ Kc d)
    {l : Fin A.labels.card} (hl : l ∈ F.good) (j : Fin (N.N l))
    (i : Fin R.card) (hi : i ∈ N.fibre l j) :
    P D.a (ρ * c) c (D.z (enumerate R i)) (D.e (enumerate R i)) ⊆ N.physicalCarrier l j := by
  intro q hq
  exact (N.net l hl).2.2.2.2.2.2.2.1 j i hi
    ⟨G.affine q, ⟨q, hq, rfl⟩, rfl⟩

theorem physicalCarrierShade_ball (N : BlockNetData (σ := σ) F Cnet e Λ Kc d)
    (hδ : 0 < δ) (l : Fin A.labels.card) (j : Fin (N.N l)) :
    N.physicalCarrierShade l j ⊆ ball (D.z G.natural_anchor) (2 * c) := by
  rintro q ⟨_, hq⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp hq
  have hp := G.contained i (A.normalizedPiece_subset l i hi)
  exact G.physical_body_ball hδ i ((G.affine.injective.mem_set_image).mp hp)

theorem physicalCarrierShade_subset (N : BlockNetData (σ := σ) F Cnet e Λ Kc d)
    (l : Fin A.labels.card) (j : Fin (N.N l)) :
    N.physicalCarrierShade l j ⊆ N.physicalCarrier l j := fun _ h => h.1

end BlockNetData
end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
