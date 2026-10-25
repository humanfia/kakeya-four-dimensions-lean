-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.ConcentratedBlocks.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/ConcentratedBlocks.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.LocalCoefficient
import Submission.WZ.Obl.wz_concentrated_convex_factorization.Blocks

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_concentrated_convex_factorization (count Upper disjoint_blocks)

noncomputable section

/-- A stable large local coefficient supplies disjoint saturated blocks
covering at least half the indices. Each block has a single neighborhood,
a dense convex container, and the global convex upper bound at that scale. -/
theorem localCoefficient_dense_blocks {ι : Type*} [DecidableEq ι]
    (U : ι → Set V) {vol K : ℝ} (near : ι → ι → Prop) (Q : Finset ι)
    (hvol : 0 < vol) (hK : 0 < K)
    (hU : ∀ i ∈ Q, O vol ≤ μ (U i))
    (hlarge : 2 * K < localCoefficient U vol near Q)
    (hstable : ∀ R ⊆ Q, (Q.card : ℝ) ≤ 2 * R.card →
      localCoefficient U vol near Q ≤ K * localCoefficient U vol near R) :
    ∃ F : Finset (Finset ι),
      (∀ P ∈ F, P.Nonempty ∧ P ⊆ Q ∧
        ∃ j ∈ Q, ∃ W : Set V, Convex ℝ W ∧ μ W ≠ ⊤ ∧
          (∀ i ∈ P, near j i ∧ U i ⊆ W) ∧
          localCoefficient U vol near Q / (2 * K) * (μ W).toReal <
            (P.card : ℝ) * vol ∧
          Upper U vol P (localCoefficient U vol near Q)) ∧
      (↑F : Set (Finset ι)).PairwiseDisjoint id ∧
      (Q.card : ℝ) ≤ 2 * (F.biUnion id).card := by
  classical
  apply disjoint_blocks Q
  intro R hRQ hcard hR
  have hstableR := hstable R hRQ hcard
  have hlargeR : 2 < localCoefficient U vol near R := by nlinarith
  obtain ⟨j, hj, W, hW, hfin, hden⟩ := localCoefficient_dense_test U near R hvol.le
    (fun i hi => hU i (hRQ hi)) hlargeR
  let P := (R.filter (near j)).filter (fun i => U i ⊆ W)
  have hPsub : P ⊆ R := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hP : P.Nonempty := by
    by_contra h
    have he : P.card = 0 := by simp [Finset.not_nonempty_iff_eq_empty.mp h]
    have hzero : count U (R.filter (near j)) W = 0 := he
    rw [hzero, Nat.cast_zero, zero_mul] at hden
    exact (not_lt_of_ge (mul_nonneg (by linarith) ENNReal.toReal_nonneg) hden).elim
  refine ⟨P, hPsub, hP, j, hRQ hj, W, hW, hfin, ?_, ?_, ?_⟩
  · intro i hi
    have hmem := Finset.mem_filter.mp hi
    exact ⟨(Finset.mem_filter.mp hmem.1).2, hmem.2⟩
  · have hscale : localCoefficient U vol near Q / (2 * K) ≤
        localCoefficient U vol near R / 2 := by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith
    exact (mul_le_mul_of_nonneg_right hscale ENNReal.toReal_nonneg).trans_lt hden
  · apply (localCoefficient_upper U near Q hvol.le hU j (hRQ hj)).subset hvol.le
    intro i hi
    exact Finset.mem_filter.mpr ⟨hRQ (hPsub hi),
      (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2⟩

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
