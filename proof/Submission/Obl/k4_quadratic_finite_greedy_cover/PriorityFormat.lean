-- Adapted from this LOT tree, o117, session x0390, commit 0d48789,
-- Submission/Obl/k4_quadratic_candidate_atlas_conversion/PriorityFormat.lean.

import Submission.Obl.k4_quadratic_finite_greedy_cover.EligibilityFormat

namespace Submission.Obl.k4_quadratic_finite_greedy_cover

open Set

/-- An arbitrary finite priority history has polynomial Boolean cost linear in
the selected family size. Its degree bound is independent of that size. -/
theorem priority_assignment_format
    (Nk L : ℝ) (W C : ℕ) (B : Fin W → ℝ) (ρ gain ε : ℝ)
    (r : ℕ → ℝ) (T : ℕ → ℕ) (lev : Fin C → ℕ) (γ : Fin C → Fin W)
    (j : Fin C → ℕ) (A : Fin C → Set Trajectory) (S : Finset (CandidateDatum C))
    (H : ℝ) (D : ℕ) (hH : 0 ≤ H)
    (hA : ∀ b copy, fmt 6 H D {z | (copy, z) ∈ A b})
    (hR : ∀ a ∈ S, a.test.totalDegree ≤ 2)
    (a : CandidateDatum C) (ha : a ∈ S)
    (P : Finset (CandidateDatum C)) (hP : P ⊆ S)
    (hrep : a.trajectories = candidateEnvelope Nk L W C B ρ gain ε r T lev γ j A a \
      selectedUnion P CandidateDatum.parent
        (candidateEnvelope Nk L W C B ρ gain ε r T lev γ j A) a.parent)
    (copy : ℕ) :
    fmt 6 (((S.card : ℝ) + 1) * (H + 96)) (max D 4)
      {z | (copy, z) ∈ a.trajectories} := by
  classical
  let E := candidateEnvelope Nk L W C B ρ gain ε r T lev γ j A
  have hEnv (b : CandidateDatum C) (hb : b ∈ S) :
      fmt 6 (H + 96) (max D 4) {z | (copy, z) ∈ E b} :=
    candidateEnvelope_format Nk L W C B ρ gain ε r T lev γ j A b
      (hR b hb) H D copy (hA b.parent copy)
  have hPrev : ∀ b ∈ P, fmt 6 (H + 96) (max D 4)
      {z | b.parent = a.parent ∧ (copy, z) ∈ E b} := by
    intro b hb
    by_cases hparent : b.parent = a.parent
    · exact fmt_congr (hEnv b (hP hb)) (fun z => by simp [hparent])
    · have he : {z | b.parent = a.parent ∧ (copy, z) ∈ E b} = ∅ := by
        ext z
        simp [hparent]
      rw [he]
      exact Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.mono (fmt_empty 6 (max D 4))
        (by linarith) le_rfl
  have hUnion : fmt 6 ((P.card : ℝ) * (H + 96)) (max D 4)
      (⋃ b ∈ P, {z | b.parent = a.parent ∧ (copy, z) ∈ E b}) := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using
      fmt_biUnion P (fun _ => H + 96)
        (fun b => {z | b.parent = a.parent ∧ (copy, z) ∈ E b}) hPrev
  have hd : fmt 6 ((H + 96) + (P.card : ℝ) * (H + 96)) (max D 4)
      ({z | (copy, z) ∈ E a} \
        (⋃ b ∈ P, {z | b.parent = a.parent ∧ (copy, z) ∈ E b})) := by
    simpa only [max_self] using fmt_diff (hEnv a ha) hUnion
  have htarget : fmt 6 ((H + 96) + (P.card : ℝ) * (H + 96)) (max D 4)
      {z | (copy, z) ∈ a.trajectories} := by
    apply fmt_congr hd
    intro z
    simp only [hrep, Set.mem_sdiff, Set.mem_iUnion, Set.mem_ofPred_eq, selectedUnion, E]
  have hcard : (P.card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast Finset.card_le_card hP
  apply Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.mono htarget _ le_rfl
  nlinarith [mul_le_mul_of_nonneg_right hcard (show 0 ≤ H + 96 by linarith)]

end Submission.Obl.k4_quadratic_finite_greedy_cover
