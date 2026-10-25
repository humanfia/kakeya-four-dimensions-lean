-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.WindowBlockRows.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/WindowBlockRows.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.WindowHighNetBlock
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.GlobalCarrierMass

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_separated_cover_refinement (enumerate)

noncomputable section
namespace WindowHighNetBlock

variable {σ ω ζ δ ξ b ρ c β τ Cnet e t ν loss β₂ q₀ jump τ₂ widthJump fillExp : ℝ}
  {p n d : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}
  {D : ConcentratedGrainData ω ζ δ ξ b ρ c p n x v Y}
  {R : Finset (Fin D.L)} {G : D.NormalizedBlock R}
  {A : BlockAngularData D R G β τ} {hδ : 0 < δ}

abbrev CarrierLabels (H : WindowHighNetBlock A hδ σ Cnet e t ν loss β₂ q₀ jump τ₂ widthJump fillExp d) :=
  Σ l : H.high.nets.highLabels, Fin (H.high.nets.N l.val)

def box (H : WindowHighNetBlock A hδ σ Cnet e t ν loss β₂ q₀ jump τ₂ widthJump fillExp d)
    (k : H.CarrierLabels) : PhysicalCarrierBox H.high.nets loss (2 * ν) k.1.val k.2 :=
  (H.carriers k.1.val k.1.property k.2).choose

def packet (H : WindowHighNetBlock A hδ σ Cnet e t ν loss β₂ q₀ jump τ₂ widthJump fillExp d)
    (k : H.CarrierLabels) : ClippedCarrierAngularData (H.box k) hδ β₂ q₀ jump τ₂ :=
  (H.carriers k.1.val k.1.property k.2).choose_spec.choose

def rows (H : WindowHighNetBlock A hδ σ Cnet e t ν loss β₂ q₀ jump τ₂ widthJump fillExp d)
    (k : H.CarrierLabels) : CarrierWindowRows (H.packet k) widthJump fillExp :=
  Classical.choice (H.carriers k.1.val k.1.property k.2).choose_spec.choose_spec

abbrev RowLabels (H : WindowHighNetBlock A hδ σ Cnet e t ν loss β₂ q₀ jump τ₂ widthJump fillExp d) :=
  Σ k : H.CarrierLabels, Fin (H.rows k).count

def row (H : WindowHighNetBlock A hδ σ Cnet e t ν loss β₂ q₀ jump τ₂ widthJump fillExp d)
    (k : H.RowLabels) (i : Fin R.card) : Set V := (H.rows k.1).shade k.2 i

theorem row_measurable
    (H : WindowHighNetBlock A hδ σ Cnet e t ν loss β₂ q₀ jump τ₂ widthJump fillExp d)
    (k : H.RowLabels) (i : Fin R.card) : MeasurableSet (H.row k i) :=
  (H.rows k.1).measurable k.2 i

theorem row_subset_physical
    (H : WindowHighNetBlock A hδ σ Cnet e t ν loss β₂ q₀ jump τ₂ widthJump fillExp d)
    (k : H.RowLabels) (i : Fin R.card) :
    H.row k i ⊆ H.high.nets.physicalPiece k.1.1.val k.1.2 i :=
  ((H.rows k.1).subset k.2 i).trans
    ((((H.packet k.1).refinement.1 i).2.trans inter_subset_left).trans ((H.packet k.1).input_subset i))

theorem row_subset
    (H : WindowHighNetBlock A hδ σ Cnet e t ν loss β₂ q₀ jump τ₂ widthJump fillExp d)
    (k : H.RowLabels) (i : Fin R.card) : H.row k i ⊆ D.Hg (enumerate R i) :=
  (H.row_subset_physical k i).trans (H.high.nets.physicalPiece_subset _ _ i)

theorem row_disjoint
    (H : WindowHighNetBlock A hδ σ Cnet e t ν loss β₂ q₀ jump τ₂ widthJump fillExp d)
    (i : Fin R.card) : Pairwise fun k k' : H.RowLabels => Disjoint (H.row k i) (H.row k' i) := by
  intro k k' hne
  rcases k with ⟨⟨l, j⟩, w⟩
  rcases k' with ⟨⟨l', j'⟩, w'⟩
  by_cases hl : l = l'
  · subst l'
    by_cases hj : j = j'
    · subst j'
      exact (H.rows ⟨l, j⟩).disjoint i (fun he => hne (by cases he; rfl))
    · exact ((H.high.nets.piece_disjoint_carriers (Finset.mem_filter.mp l.property).1 hj i).preimage G.affine).mono
        (H.row_subset_physical ⟨⟨l, j⟩, w⟩ i) (H.row_subset_physical ⟨⟨l, j'⟩, w'⟩ i)
  · exact ((H.high.nets.piece_disjoint_labels (fun he => hl (Subtype.ext he)) j j' i).preimage G.affine).mono
      (H.row_subset_physical ⟨⟨l, j⟩, w⟩ i) (H.row_subset_physical ⟨⟨l', j'⟩, w'⟩ i)

/-- All windows of the block retain the product of the second angular
selection and the fixed-length window selection, with no further loss. -/
theorem row_mass
    (H : WindowHighNetBlock A hδ σ Cnet e t ν loss β₂ q₀ jump τ₂ widthJump fillExp d) :
    O (δ ^ τ₂ / 68) *
      (∑ l ∈ H.high.nets.highLabels, ∑ j, ∑ i, μ (H.high.nets.physicalPiece l j i)) ≤
      ∑ k : H.RowLabels, ∑ i, μ (H.row k i) := by
  classical
  have hlocal (k : H.CarrierLabels) :
      O (δ ^ τ₂ / 68) * (∑ i, μ (H.high.nets.physicalPiece k.1.val k.2 i)) ≤
        ∑ w, ∑ i, μ ((H.rows k).shade w i) := by
    calc
      _ = (1 / 34 : ENNReal) * (O (δ ^ τ₂ / 2) *
          (∑ i, μ (H.high.nets.physicalPiece k.1.val k.2 i))) := by
        rw [← mul_assoc]
        congr 1
        rw [show δ ^ τ₂ / 68 = (1 / 34) * (δ ^ τ₂ / 2) by ring]
        dsimp only [O]
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 34)]
        norm_num [ENNReal.ofReal_div_of_pos]
      _ ≤ (1 / 34 : ENNReal) * ∑ i, μ ((H.packet k).shade i) :=
        mul_le_mul' le_rfl (H.packet k).mass
      _ ≤ _ := (H.rows k).mass
  rw [show (∑ l ∈ H.high.nets.highLabels, ∑ j, ∑ i, μ (H.high.nets.physicalPiece l j i)) =
      ∑ k : H.CarrierLabels, ∑ i, μ (H.high.nets.physicalPiece k.1.val k.2 i) by
    rw [Fintype.sum_sigma (fun k : H.CarrierLabels =>
      ∑ i, μ (H.high.nets.physicalPiece k.1.val k.2 i))]
    exact (Finset.sum_coe_sort H.high.nets.highLabels
      (fun l => ∑ j, ∑ i, μ (H.high.nets.physicalPiece l j i))).symm]
  rw [Finset.mul_sum, Fintype.sum_sigma (fun k : H.RowLabels => ∑ i, μ (H.row k i))]
  exact Finset.sum_le_sum (fun k _ => hlocal k)

end WindowHighNetBlock
end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
