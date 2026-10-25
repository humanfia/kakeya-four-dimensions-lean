-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.NetCounting.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/NetCounting.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Core

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory

noncomputable section

/-- Cancel the common positive affine volume factor after summing a density
bound that is linear in each label's cardinality. -/
theorem sum_affine_density_cancel {ι : Type*} (S : Finset ι) (card : ι → ℕ)
    (mass : ι → ENNReal) {J C cap : ℝ} (hJ : 0 < J) (hC : 0 ≤ C) (hcap : 0 ≤ cap)
    (hlow : (∑ l ∈ S, O (J * C * card l)) ≤ O J * ∑ l ∈ S, mass l)
    (hupp : (∑ l ∈ S, mass l) ≤ O cap) :
    C * (∑ l ∈ S, (card l : ℝ)) ≤ cap := by
  have hl := hlow.trans (mul_le_mul' le_rfl hupp)
  have hleft : (∑ l ∈ S, O (J * C * card l)) =
      O (J * (C * ∑ l ∈ S, (card l : ℝ))) := by
    unfold O
    rw [← ENNReal.ofReal_sum_of_nonneg (fun l _ => by positivity), ← Finset.mul_sum]
    congr 1
    ring
  rw [hleft, ← ENNReal.ofReal_mul hJ.le] at hl
  have hh := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hJ.le hcap)).mp hl
  exact (mul_le_mul_iff_right₀ hJ).mp hh

/-- A small upper bound on the low labels forces the complementary labels
to retain at least half of all index occurrences. -/
theorem high_labels_carry_half {ι : Type*} (S : Finset ι) (card : ι → ℕ)
    (isLow : ι → Prop) [DecidablePred isLow] {C cap : ℝ} (hC : 0 < C)
    (hlow : C * (∑ l ∈ S.filter isLow, (card l : ℝ)) ≤ cap)
    (hgap : cap < C * (∑ l ∈ S, (card l : ℝ)) / 2) :
    (1 / 2 : ℝ) * (∑ l ∈ S, (card l : ℝ)) ≤
      ∑ l ∈ S.filter (fun l => ¬ isLow l), (card l : ℝ) := by
  have hs := Finset.sum_filter_add_sum_filter_not S isLow (fun l => (card l : ℝ))
  have hsplit := congrArg (fun t : ℝ => C * t) hs
  apply (mul_le_mul_iff_right₀ hC).mp
  nlinarith only [hlow, hgap, hsplit]

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
