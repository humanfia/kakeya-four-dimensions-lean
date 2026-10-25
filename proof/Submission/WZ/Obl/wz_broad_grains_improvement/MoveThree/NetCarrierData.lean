-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.NetCarrierData.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/NetCarrierData.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.HighNetConcentration

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open scoped Classical
open WangZahlLot.Obl.wz_transverse_cell_weighted_cover (cTube axisDir norm_axisDir)
open WangZahlLot.Obl.wz_regular_transverse_affine_cells
  (closedTube tube_subset_closedTube closedTube_volume_bounds)

noncomputable section
namespace BlockNetData

variable {σ ω ζ δ ε b ρ c β τ lam den k Cnet e Λ Kc : ℝ} {p n d : ℕ}
  {x v : Fin n → V} {Y : Fin n → Set V}
  {D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y}
  {R : Finset (Fin D.L)} {G : D.NormalizedBlock R}
  {A : BlockAngularData D R G β τ} {hk : 0 < k}
  {F : BlockFirstFilling A lam den k hk}

def carrier (N : BlockNetData (σ := σ) F Cnet e Λ Kc d)
    (l : Fin A.labels.card) (j : Fin (N.N l)) : Set V :=
  F.map l ⁻¹' cTube F.radius
    (F.map l (A.start (N.representative l j) + (1 / 2 : ℝ) • A.axis (N.representative l j)))
    (F.direction l (N.representative l j))

def piece (N : BlockNetData (σ := σ) F Cnet e Λ Kc d)
    (l : Fin A.labels.card) (j : Fin (N.N l)) (i : Fin R.card) : Set V :=
  if i ∈ N.fibre l j then A.normalizedPiece l i else ∅

theorem piece_measurable (N : BlockNetData (σ := σ) F Cnet e Λ Kc d)
    (l : Fin A.labels.card) (j : Fin (N.N l)) (i : Fin R.card) :
    MeasurableSet (N.piece l j i) := by
  unfold piece
  split_ifs
  · exact A.normalizedPiece_measurable l i
  · exact MeasurableSet.empty

theorem piece_subset (N : BlockNetData (σ := σ) F Cnet e Λ Kc d)
    (l : Fin A.labels.card) (j : Fin (N.N l)) (i : Fin R.card) :
    N.piece l j i ⊆ A.normalizedPiece l i := by
  unfold piece
  split_ifs
  · exact Subset.rfl
  · exact empty_subset _

theorem piece_disjoint_labels (N : BlockNetData (σ := σ) F Cnet e Λ Kc d)
    {l l' : Fin A.labels.card} (hne : l ≠ l')
    (j : Fin (N.N l)) (j' : Fin (N.N l')) (i : Fin R.card) :
    Disjoint (N.piece l j i) (N.piece l' j' i) := by
  exact (A.refinement.piece_disjoint i
    ((WangZahlLot.Obl.wz_separated_cover_refinement.enumerate_injective A.labels).ne hne)).mono
      (N.piece_subset l j i) (N.piece_subset l' j' i)

theorem piece_disjoint_carriers (N : BlockNetData (σ := σ) F Cnet e Λ Kc d)
    {l : Fin A.labels.card} (hl : l ∈ F.good) {j j' : Fin (N.N l)}
    (hne : j ≠ j') (i : Fin R.card) :
    Disjoint (N.piece l j i) (N.piece l j' i) := by
  have hd := (N.net l hl).2.2.2.2.2.1 j j' hne
  by_cases hi : i ∈ N.fibre l j
  · have hi' : i ∉ N.fibre l j' := fun hh => Finset.disjoint_left.mp hd hi hh
    simp only [piece, if_neg hi', disjoint_empty]
  · simp only [piece, if_neg hi, empty_disjoint]

theorem piece_in_carrier (N : BlockNetData (σ := σ) F Cnet e Λ Kc d)
    {l : Fin A.labels.card} (hl : l ∈ F.good) (j : Fin (N.N l)) (i : Fin R.card) :
    N.piece l j i ⊆ N.carrier l j := by
  intro q hq
  by_cases hi : i ∈ N.fibre l j
  · have hpiece : q ∈ A.normalizedPiece l i := by simpa [piece, hi] using hq
    have hbody := G.contained i (A.normalizedPiece_subset l i hpiece)
    exact (N.net l hl).2.2.2.2.2.2.2.1 j i hi ⟨q, hbody, rfl⟩
  · simpa [piece, hi] using hq

theorem carrier_measurable (N : BlockNetData (σ := σ) F Cnet e Λ Kc d)
    (l : Fin A.labels.card) (j : Fin (N.N l)) : MeasurableSet (N.carrier l j) := by
  apply MeasurableSet.preimage (isOpen_thickening.measurableSet)
  exact (F.map l).toContinuousAffineEquiv.continuous.measurable

theorem piece_mass (N : BlockNetData (σ := σ) F Cnet e Λ Kc d)
    {l : Fin A.labels.card} (hl : l ∈ F.good) (j : Fin (N.N l)) :
    O (48 * lam * (2 * ρ) ^ 2 * (N.size l : ℝ)) ≤ ∑ i, μ (N.piece l j i) := by
  have hcard := (N.net l hl).2.2.2.2.1 j
  have hf := (N.net l hl).2.2.2.1 j
  have H : (∑ i ∈ N.fibre l j, O (48 * lam * (2 * ρ) ^ 2)) ≤
      ∑ i ∈ N.fibre l j, μ (A.normalizedPiece l i) := by
    apply Finset.sum_le_sum
    intro i hi
    exact ((F.filling l hl).2.2.2 i (hf hi)).1
  have hleft : (∑ i ∈ N.fibre l j, O (48 * lam * (2 * ρ) ^ 2)) =
      O (48 * lam * (2 * ρ) ^ 2 * (N.size l : ℝ)) := by
    simp only [Finset.sum_const, nsmul_eq_mul, hcard]
    rw [mul_comm]
    simpa only [O, ENNReal.ofReal_natCast] using
      (ENNReal.ofReal_mul' (p := 48 * lam * (2 * ρ) ^ 2) (Nat.cast_nonneg (N.size l))).symm
  rw [hleft] at H
  convert H using 1
  rw [show (∑ i, μ (N.piece l j i)) =
      ∑ i ∈ N.fibre l j, μ (A.normalizedPiece l i) by
    simp only [piece, apply_ite μ, measure_empty, Finset.sum_ite_mem, Finset.univ_inter]]

theorem carrier_volume (N : BlockNetData (σ := σ) F Cnet e Λ Kc d)
    (hδ : 0 < δ) (hR : R.Nonempty) (hlam : 0 < lam)
    {l : Fin A.labels.card} (hl : l ∈ F.good) (j : Fin (N.N l)) :
    O F.volumeFactor * μ (N.carrier l j) ≤ O (384 * (4 * F.radius) ^ 2) := by
  have hB := F.radius_pos hδ hR
  have hB1 := F.radius_small hδ hR hlam
  have hrep := (N.net l hl).2.2.1 j
  have hdir := ((F.filling l hl).2.2.2 (N.representative l j) hrep).2.1
  rw [← F.map_volume]
  rw [carrier, image_preimage_eq _ (F.map l).surjective]
  exact (measure_mono (tube_subset_closedTube _ _ _)).trans
    (closedTube_volume_bounds (by positivity : 0 < 4 * F.radius) (by linarith)
      _ _ (norm_axisDir hdir)).2

end BlockNetData
end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
