-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_parameter_weak_strong_reduction.Counting.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_parameter_weak_strong_reduction

open Set Metric

/-- A fixed finite cover converts the local coefficient bound into a bound on the
number of indices, including repeated coefficients. -/
theorem exists_coefficient_count_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (q : Fin n → EuclideanSpace ℝ (Fin 3)) (B : ℝ),
      (∀ i, ‖q i‖ ≤ 10) → 0 ≤ B →
      (∀ x, ({i | q i ∈ ball x 1}.ncard : ℝ) ≤ B) →
      (n : ℝ) ≤ C * B := by
  classical
  obtain ⟨t, _, ht, hcover⟩ :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) 10).finite_cover_balls
      (show (0 : ℝ) < 1 by norm_num)
  let F := ht.toFinset
  refine ⟨(F.card : ℝ) + 1, by positivity, ?_⟩
  intro n q B hq hB hcount
  have hcov : (Set.univ : Set (Fin n)) ⊆ ⋃ x ∈ F, {i | q i ∈ ball x 1} := by
    intro i _
    have hqi : q i ∈ closedBall 0 10 := by simpa [mem_closedBall, dist_zero_right] using hq i
    obtain ⟨x, hxt, hxi⟩ := mem_iUnion₂.mp (hcover hqi)
    exact mem_iUnion₂.mpr ⟨x, by simpa [F] using hxt, hxi⟩
  have hcard : n ≤ ∑ x ∈ F, ({i | q i ∈ ball x 1}).ncard := by
    calc
      n = (Set.univ : Set (Fin n)).ncard := by simp
      _ ≤ (⋃ x ∈ F, {i | q i ∈ ball x 1}).ncard := ncard_le_ncard hcov
      _ ≤ _ := F.set_ncard_biUnion_le _
  calc
    (n : ℝ) ≤ ∑ x ∈ F, (({i | q i ∈ ball x 1}).ncard : ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ _x ∈ F, B := Finset.sum_le_sum fun x _ => hcount x
    _ = (F.card : ℝ) * B := by simp
    _ ≤ ((F.card : ℝ) + 1) * B := mul_le_mul_of_nonneg_right (by linarith) hB

end WangZahlLot.Obl.wz_parameter_weak_strong_reduction
