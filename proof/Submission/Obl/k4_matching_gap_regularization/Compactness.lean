import Submission.Obl.k4_matching_gap_regularization.Data

set_option autoImplicit false

namespace Submission.Obl.k4_matching_gap_regularization

open Filter Set
open scoped Topology

/-- Bounded finite collections of exponents have a common subsequential
limit; having a zero among the first D coordinates is closed. -/
lemma compact_exponent_subseq {D J : ℕ} (hDJ : D ≤ J)
    (β : ℕ → ℕ → ℝ) (hβ : ∀ m, Admissible D J (β m)) :
    ∃ (b : ℕ → ℝ) (φ : ℕ → ℕ), Admissible D J b ∧ StrictMono φ ∧
      ∀ j, 1 ≤ j → j ≤ J → Tendsto (fun m => β (φ m) j) atTop (𝓝 (b j)) := by
  classical
  let u : ℕ → Fin J → ℝ := fun m j => β m (j.val + 1)
  have hu : ∀ m, u m ∈ {b : Fin J → ℝ | ∀ j, b j ∈ Icc (0 : ℝ) 2} := by
    intro m j
    exact (hβ m).1 (j.val + 1) (by omega) (by omega)
  obtain ⟨a, ha, φ, hφ, hlim⟩ :=
    (isCompact_pi_infinite fun _ : Fin J => isCompact_Icc (a := (0 : ℝ)) (b := 2)).isSeqCompact hu
  have hzclosed : IsClosed {b : Fin J → ℝ | ∃ j : Fin J, j.val + 1 ≤ D ∧ b j = 0} := by
    simp only [ofPred_exists]
    apply isClosed_iUnion_of_finite
    intro j
    by_cases hj : j.val + 1 ≤ D
    · simpa only [hj, true_and] using
        (isClosed_eq (continuous_apply j) continuous_const : IsClosed {b : Fin J → ℝ | b j = 0})
    · simp [hj]
  have hzmem : ∀ m, ∃ j : Fin J, j.val + 1 ≤ D ∧ u m j = 0 := by
    intro m
    obtain ⟨j, hj₁, hjD, hjzero⟩ := (hβ m).2
    refine ⟨⟨j - 1, by omega⟩, ?_, ?_⟩
    · change j - 1 + 1 ≤ D
      omega
    simpa only [u, show j - 1 + 1 = j by omega] using hjzero
  have hazero : ∃ j : Fin J, j.val + 1 ≤ D ∧ a j = 0 :=
    hzclosed.mem_of_tendsto hlim (Eventually.of_forall fun m => hzmem (φ m))
  let b : ℕ → ℝ := fun j => if hj : 1 ≤ j ∧ j ≤ J then a ⟨j - 1, by omega⟩ else 0
  refine ⟨b, φ, ⟨?_, ?_⟩, hφ, ?_⟩
  · intro j hj₁ hjJ
    simpa [b, hj₁, hjJ] using ha ⟨j - 1, by omega⟩
  · obtain ⟨j, hjD, hjzero⟩ := hazero
    refine ⟨j.val + 1, by omega, hjD, ?_⟩
    simpa [b, show j.val + 1 ≤ J by omega] using hjzero
  · intro j hj₁ hjJ
    have h := tendsto_pi_nhds.1 hlim ⟨j - 1, by omega⟩
    simpa [Function.comp_def, u, show j - 1 + 1 = j by omega, b, hj₁, hjJ] using h

end Submission.Obl.k4_matching_gap_regularization
