-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.AngularBlockFamily.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/AngularBlockFamily.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.NormalizedPacketPieces

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory

noncomputable section

/-- Angular selections on disjoint saturated blocks. The blocks may have
different angular scales, while the selection exponent and loss are uniform. -/
structure AngularBlockFamily {ω ζ δ ε b ρ c : ℝ} {p n : ℕ} {x v : Fin n → V}
    {Y : Fin n → Set V} (D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y)
    (β τ : ℝ) where
  blocks : Finset (Finset (Fin D.L))
  subset : ∀ R ∈ blocks, R ⊆ D.Q
  disjoint : (↑blocks : Set (Finset (Fin D.L))).PairwiseDisjoint id
  card : (D.Q.card : ℝ) ≤ 2 * (blocks.biUnion id).card
  frame : ∀ R : blocks, D.NormalizedBlock R.val
  angular : ∀ R : blocks, BlockAngularData D R.val (frame R) β τ

namespace AngularBlockFamily

variable {ω ζ δ ε b ρ c β τ : ℝ} {p n : ℕ} {x v : Fin n → V}
  {Y : Fin n → Set V} {D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y}

abbrev Labels (F : AngularBlockFamily D β τ) :=
  Σ R : F.blocks, Fin (F.angular R).labels.card

def grainPiece (F : AngularBlockFamily D β τ) (j : Fin D.L) (l : F.Labels) : Set V :=
  (F.angular l.1).grainPiece j l.2

theorem grainPiece_measurable (F : AngularBlockFamily D β τ) (j : Fin D.L) (l : F.Labels) :
    MeasurableSet (F.grainPiece j l) := (F.angular l.1).grainPiece_measurable j l.2

theorem grainPiece_subset (F : AngularBlockFamily D β τ) (j : Fin D.L) (l : F.Labels) :
    F.grainPiece j l ⊆ D.Hg j := (F.angular l.1).grainPiece_subset j l.2

theorem grainPiece_disjoint (F : AngularBlockFamily D β τ) (j : Fin D.L)
    (l l' : F.Labels) (hne : l ≠ l') : Disjoint (F.grainPiece j l) (F.grainPiece j l') := by
  classical
  rcases l with ⟨R, l⟩
  rcases l' with ⟨R', l'⟩
  by_cases hR : R = R'
  · subst R'
    exact (F.angular R).grainPiece_disjoint j l l' (by intro hh; exact hne (by cases hh; rfl))
  · have hR' : R.val ≠ R'.val := fun hh => hR (Subtype.ext hh)
    have hd := F.disjoint R.property R'.property hR'
    by_cases hj : j ∈ R.val
    · have hj' : j ∉ R'.val := fun hh => Finset.disjoint_left.mp hd hj hh
      change Disjoint _ ((F.angular R').grainPiece j l')
      rw [(F.angular R').grainPiece_outside hj']
      simp
    · change Disjoint ((F.angular R).grainPiece j l) _
      rw [(F.angular R).grainPiece_outside hj]
      simp

/-- Summing the actual packet pieces over the disjoint saturated blocks
retains the balanced-block mass and the chosen angular selection fraction. -/
theorem grainPiece_mass (F : AngularBlockFamily D β τ) (hδ : 0 < δ) :
    O (δ ^ (τ + ε / 4 + ε / 40) / 2) * ∑ j, μ (D.Hg j) ≤
      ∑ j, ∑ l : F.Labels, μ (F.grainPiece j l) := by
  classical
  have hcoeff : O (δ ^ (τ + ε / 4 + ε / 40) / 2) =
      O (δ ^ τ) * O (δ ^ (ε / 80) / 2) * O (δ ^ (ε / 4 + ε / 80)) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    calc
      δ ^ (τ + ε / 4 + ε / 40) / 2 = δ ^ (τ + ε / 80 + (ε / 4 + ε / 80)) / 2 := by
        congr 2; ring
      _ = _ := by rw [Real.rpow_add hδ, Real.rpow_add hδ]; ring
  have hmass := D.retained_block_mass hδ F.blocks F.subset F.card
  have hsum : ∑ j ∈ F.blocks.biUnion id, μ (D.Hg j) =
      ∑ R : F.blocks, ∑ j ∈ R.val, μ (D.Hg j) := by
    rw [Finset.sum_biUnion F.disjoint,
      Finset.sum_coe_sort F.blocks (fun R => ∑ j ∈ R, μ (D.Hg j))]
    rfl
  calc
    _ = O (δ ^ τ) * (O (δ ^ (ε / 80) / 2) *
        (O (δ ^ (ε / 4 + ε / 80)) * ∑ j, μ (D.Hg j))) := by
      rw [hcoeff]; simp only [mul_assoc]
    _ ≤ O (δ ^ τ) * (O (δ ^ (ε / 80) / 2) * ∑ j ∈ D.Q, μ (D.Hg j)) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl D.retained)
    _ ≤ O (δ ^ τ) * ∑ j ∈ F.blocks.biUnion id, μ (D.Hg j) :=
      mul_le_mul' le_rfl hmass
    _ = ∑ R : F.blocks, O (δ ^ τ) * ∑ j ∈ R.val, μ (D.Hg j) := by
      rw [hsum, Finset.mul_sum]
    _ ≤ ∑ R : F.blocks, ∑ j, ∑ l, μ ((F.angular R).grainPiece j l) :=
      Finset.sum_le_sum fun R _ => (F.angular R).grainPiece_mass hδ
    _ = ∑ j, ∑ l : F.Labels, μ (F.grainPiece j l) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      exact (Fintype.sum_sigma (fun l : F.Labels => μ (F.grainPiece j l))).symm

/-- Reindex all block labels by one finite type and lift them to fine-tube
incidences. Only the already quantified balance and angular losses occur. -/
theorem fine_pieces (F : AngularBlockFamily D β τ) (hδ : 0 < δ) :
    ∃ (K : ℕ) (label : Fin K ≃ F.Labels) (W : Fin n → Fin K → Set V),
      (∀ i l, W i l = fineGrainPiece D.f D.γ D.Z
        (fun j l => F.grainPiece j (label l)) i l) ∧
      (∀ i l, MeasurableSet (W i l) ∧ W i l ⊆ D.Z i) ∧
      (∀ i l l', l ≠ l' → Disjoint (W i l) (W i l')) ∧
      O (δ ^ (τ + ε / 4 + ε / 40) / 4) * ∑ i, μ (D.Z i) ≤ ∑ i, ∑ l, μ (W i l) ∧
      (∀ l, Broad ω ζ δ (ε / 4) ρ n D.N v D.S (fun i => W i l) D.f) ∧
      ∀ l z, D.m * q D.L {j | z ∈ F.grainPiece j (label l)} ≤
          q n {i | z ∈ W i l} ∧
        q n {i | z ∈ W i l} ≤ 2 * D.m * q D.L {j | z ∈ F.grainPiece j (label l)} := by
  classical
  let K := Fintype.card F.Labels
  let e : Fin K ≃ F.Labels := (Fintype.equivFin F.Labels).symm
  let B : Fin D.L → Fin K → Set V := fun j l => F.grainPiece j (e l)
  have hmass : O (δ ^ (τ + ε / 4 + ε / 40) / 2) * ∑ j, μ (D.Hg j) ≤
      ∑ j, ∑ l, μ (B j l) := by
    apply (F.grainPiece_mass hδ).trans_eq
    apply Finset.sum_congr rfl
    intro j _
    exact (Equiv.sum_comp e (fun l => μ (F.grainPiece j l))).symm
  obtain ⟨hWm, hWdisj, hWmass, hWbroad⟩ := labelled_grain_refinement D.grains
    (fun i => (D.cover.1 i).1) (fun i => (D.cover.1 i).2.2) D.broad B
    (fun j l => F.grainPiece_measurable j (e l)) (fun j l => F.grainPiece_subset j (e l))
    (fun j l l' hh => F.grainPiece_disjoint j (e l) (e l') (e.injective.ne hh))
    (by positivity : 0 ≤ δ ^ (τ + ε / 4 + ε / 40) / 2) hmass
  refine ⟨K, e, fineGrainPiece D.f D.γ D.Z B, fun _ _ => rfl,
    hWm, hWdisj, ?_, hWbroad, ?_⟩
  · convert hWmass using 1
    congr 2
    ring
  · intro l q
    exact fineGrainPiece_count_bounds D.grains (fun i => (D.cover.1 i).2.2)
      B (fun j l => F.grainPiece_subset j (e l)) l q

end AngularBlockFamily
end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
