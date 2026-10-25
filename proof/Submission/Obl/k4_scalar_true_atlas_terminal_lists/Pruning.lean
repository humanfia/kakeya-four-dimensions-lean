import Mathlib
import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.MassBounds

/-! Whole-chart pruning after a common observation restriction. -/

namespace Submission.Obl.k4_scalar_true_atlas_terminal_lists

open MeasureTheory Set
open scoped ENNReal BigOperators

/-- Keep the charts that retain at least half their own original mass.
The aggregate loss is charged to the original world laws. -/
theorem prune_to_common_good {Y : Type*} [MeasurableSpace Y] {W n : ℕ}
    (ω : Fin W → ENNReal) (μ : Fin W → Measure Y) [∀ a, IsFiniteMeasure (μ a)]
    (γ : Fin n → Fin W) (C : Fin n → Set Y) (G : Fin W → Set Y)
    (hC : ∀ i, MeasurableSet (C i)) (hG : ∀ a, MeasurableSet (G a))
    (hdisj : ∀ i i', i ≠ i' → γ i = γ i' → μ (γ i) (C i ∩ C i') = 0) :
    ∃ F : Finset (Fin n),
      (∀ i ∈ F, μ (γ i) (C i) ≤ 2 * μ (γ i) (C i ∩ G (γ i))) ∧
      (∑ a, ω a * μ a {q | ∃ i, γ i = a ∧ q ∈ C i}) ≤
        (∑ a, ω a * μ a {q | ∃ i ∈ F, γ i = a ∧ q ∈ C i ∩ G a}) +
          3 * (∑ a, ω a * μ a (G a)ᶜ) := by
  classical
  let F : Finset (Fin n) := Finset.univ.filter
    (fun i => μ (γ i) (C i) ≤ 2 * μ (γ i) (C i ∩ G (γ i)))
  let B : Finset (Fin n) := Finset.univ \ F
  have hF : ∀ i ∈ F, μ (γ i) (C i) ≤ 2 * μ (γ i) (C i ∩ G (γ i)) := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hB : ∀ i ∈ B, μ (γ i) (C i) ≤ 2 * μ (γ i) (C i ∩ (G (γ i))ᶜ) := by
    intro i hi
    have hn : ¬ μ (γ i) (C i) ≤ 2 * μ (γ i) (C i ∩ G (γ i)) := by
      simpa only [B, F, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter,
        true_and, not_and, true_implies] using (Finset.mem_sdiff.mp hi).2
    apply Submission.Obl.k4_scalar_terminal_chart_packet_extraction.le_two_mul_inter_of_diff_le
      (μ (γ i)) (c := μ (γ i) (C i ∩ G (γ i))) (by finiteness)
    · simp only [sdiff_compl]
      exact le_rfl
    · exact (lt_of_not_ge hn).le
  have hbad := Submission.Obl.k4_scalar_terminal_chart_packet_extraction.weighted_bad_le
    ω μ γ C (fun a => (G a)ᶜ) B hC (fun a => (hG a).compl)
    (fun i _ i' _ hne hγ => hdisj i i' hne hγ) hB
  let U : Fin W → Set Y := fun a =>
    {q | ∃ i ∈ F, γ i = a ∧ q ∈ C i ∩ G a}
  have hsub (a : Fin W) : {q | ∃ i, γ i = a ∧ q ∈ C i} ⊆
      (U a ∪ (G a)ᶜ) ∪ ⋃ i ∈ B.filter (fun i => γ i = a), C i := by
    intro q hq
    obtain ⟨i, hγ, hi⟩ := hq
    by_cases hiF : i ∈ F
    · left
      by_cases hqG : q ∈ G a
      · exact Or.inl ⟨i, hiF, hγ, hi, hqG⟩
      · exact Or.inr hqG
    · right
      exact mem_biUnion (by simp [B, hiF, hγ]) hi
  have hmass (a : Fin W) : μ a {q | ∃ i, γ i = a ∧ q ∈ C i} ≤
      μ a (U a) + μ a (G a)ᶜ + ∑ i ∈ B.filter (fun i => γ i = a), μ a (C i) := by
    calc
      _ ≤ μ a ((U a ∪ (G a)ᶜ) ∪ ⋃ i ∈ B.filter (fun i => γ i = a), C i) :=
        measure_mono (hsub a)
      _ ≤ μ a (U a ∪ (G a)ᶜ) + μ a (⋃ i ∈ B.filter (fun i => γ i = a), C i) :=
        measure_union_le _ _
      _ ≤ (μ a (U a) + μ a (G a)ᶜ) +
          ∑ i ∈ B.filter (fun i => γ i = a), μ a (C i) := by
        gcongr
        · exact measure_union_le _ _
        · exact measure_biUnion_finset_le _ _
  have hfib : (∑ a, ω a * ∑ i ∈ B.filter (fun i => γ i = a), μ a (C i)) =
      ∑ i ∈ B, ω (γ i) * μ (γ i) (C i) := by
    rw [← Finset.sum_fiberwise B γ (fun i => ω (γ i) * μ (γ i) (C i))]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
  refine ⟨F, hF, ?_⟩
  calc
    _ ≤ ∑ a, ω a * (μ a (U a) + μ a (G a)ᶜ +
        ∑ i ∈ B.filter (fun i => γ i = a), μ a (C i)) := by
      gcongr with a
      exact hmass a
    _ = (∑ a, ω a * μ a (U a)) + (∑ a, ω a * μ a (G a)ᶜ) +
        ∑ a, ω a * ∑ i ∈ B.filter (fun i => γ i = a), μ a (C i) := by
      simp_rw [mul_add, Finset.sum_add_distrib]
    _ ≤ (∑ a, ω a * μ a (U a)) + (∑ a, ω a * μ a (G a)ᶜ) +
        2 * (∑ a, ω a * μ a (G a)ᶜ) := by rw [hfib]; gcongr
    _ = _ := by dsimp [U]; ring

end Submission.Obl.k4_scalar_true_atlas_terminal_lists
