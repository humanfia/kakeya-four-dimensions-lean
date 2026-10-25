-- Adapted from the same LOT tree, o201, session x0697, commit d395b4346c32c12a70c4bc86d657dea88e733fcd
-- Source: Submission/Obl/k4_horizontal_critical_rate_candidates/Inherited/CriticalSimulation.lean
-- Earlier source attribution is retained below.
-- Adapted from the same LOT tree, o107, session x0353, commit 2dadd64f9c576ee68d49917fce08111798f9ad02
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/CriticalSimulation.lean
-- Unaccepted helper shared on origin/x0353; namespace and local imports renamed.
import Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited.EndpointSimulation
import Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited.CriticalJitter

/-! Refresh and representative-time errors in the critical path experiment. -/

namespace Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited

/-- A fine refresh followed by one approximate trajectory traversal has an
explicit error relative to the current event. -/
theorem horizontal_refreshed_step_error
    (q qf qa : Fin 3 → ℝ) (c K δ E : ℝ)
    (hK : 1 ≤ K) (hδ : 0 ≤ δ) (hc : |c| ≤ K) (hqf : |qf 1| ≤ K)
    (hqT : q 0 ∈ Set.Icc (0 : ℝ) 1) (hqfT : qf 0 ∈ Set.Icc (0 : ℝ) 1)
    (hqaT : qa 0 ∈ Set.Icc (0 : ℝ) 1)
    (hnear : ∀ i, |q i - qf i| ≤ δ)
    (htrajectory : ∀ i : Fin 2,
      |qa i.succ - horizontalTraverse c (qf 0) (qa 0) ![qf 1, qf 2] i| ≤ E) :
    ∀ i : Fin 2,
      |qa i.succ - horizontalTraverse c (q 0) (qa 0) ![q 1, q 2] i| ≤ E + 6 * K * δ := by
  have hspace : ∀ i : Fin 2, |(![q 1, q 2] : Fin 2 → ℝ) i - ![qf 1, qf 2] i| ≤ δ := by
    intro i
    fin_cases i
    · exact hnear 1
    · exact hnear 2
  have hrefresh := horizontalTraverse_refresh_error c (q 0) (qf 0) (qa 0) K δ
    ![q 1, q 2] ![qf 1, qf 2] hK hδ hc hqf hqT hqfT hqaT (hnear 0) hspace
  intro i
  have hr : |horizontalTraverse c (qf 0) (qa 0) ![qf 1, qf 2] i -
      horizontalTraverse c (q 0) (qa 0) ![q 1, q 2] i| ≤ 6 * K * δ := by
    simpa only [abs_sub_comm] using hrefresh i
  exact (abs_sub_le (qa i.succ) (horizontalTraverse c (qf 0) (qa 0) ![qf 1, qf 2] i)
    (horizontalTraverse c (q 0) (qa 0) ![q 1, q 2] i)).trans (add_le_add (htrajectory i) hr)

/-- Approximate traversals and time-cell representatives give a single
deterministic endpoint error. The starting transverse coordinate is unrestricted. -/
theorem critical_endpoint_simulation_near_times
    (c : Fin 3 → ℝ) (p : Fin 4 → Fin 3 → ℝ) (τ : Fin 3 → ℝ) (K E δ : ℝ)
    (hK : 1 ≤ K) (hE : 0 ≤ E) (hδ : 0 ≤ δ)
    (hc : ∀ i, |c i| ≤ K) (hqZ : |p 0 1| ≤ K)
    (hpt : ∀ i, p i 0 ∈ Set.Icc (0 : ℝ) 1)
    (hτ : ∀ i, τ i ∈ Set.Icc (0 : ℝ) 1)
    (hnear : ∀ i : Fin 3, |p i.succ 0 - τ i| ≤ δ)
    (hstep : ∀ i : Fin 3, ∀ j : Fin 2,
      |p i.succ j.succ - horizontalTraverse (c i) (p i.castSucc 0) (p i.succ 0)
        ![p i.castSucc 1, p i.castSucc 2] j| ≤ E) :
    ∀ i, |criticalEndpoint c (p 0) (τ 2, ![τ 0, τ 1]) i - p 3 i| ≤
      7 * E + 20 * K ^ 2 * δ := by
  have hspatial : ∀ j : Fin 2,
      |p 3 j.succ - criticalSpatialEndpoint c (p 0) (p 3 0) ![p 1 0, p 2 0] j| ≤ 7 * E := by
    have hs := critical_endpoint_simulation c (fun i => p i 0) (fun i => ![p i 1, p i 2])
      E hE hpt (by
        intro i j
        fin_cases j
        · simpa using hstep i 0
        · simpa using hstep i 1)
    have hq : (![p 0 0, p 0 1, p 0 2] : Fin 3 → ℝ) = p 0 := by
      ext i
      fin_cases i <;> rfl
    intro j
    fin_cases j
    · simpa [hq] using hs 0
    · simpa [hq] using hs 1
  have hstart : |p 0 0| ≤ K :=
    (abs_le.mpr ⟨by linarith [(hpt 0).1], (hpt 0).2⟩).trans hK
  have hj := critical_endpoint_time_perturbation c (p 0) K δ (p 3 0) (τ 2)
    ![p 1 0, p 2 0] ![τ 0, τ 1] hK hδ hc hstart hqZ (hpt 3) (hτ 2)
    (by intro i; fin_cases i; exact hpt 1; exact hpt 2)
    (by intro i; fin_cases i; exact hτ 0; exact hτ 1)
    (by simpa using hnear 2)
    (by intro i; fin_cases i; simpa using hnear 0; simpa using hnear 1)
  have hKsq : 1 ≤ K ^ 2 := by nlinarith
  have hKD : δ ≤ K ^ 2 * δ := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hKsq hδ
  intro i
  fin_cases i
  · change |τ 2 - p 3 0| ≤ _
    have ht : |τ 2 - p 3 0| ≤ δ := by simpa [abs_sub_comm] using hnear 2
    nlinarith
  · have he : |criticalEndpoint c (p 0) (τ 2, ![τ 0, τ 1]) 1 -
        criticalEndpoint c (p 0) (p 3 0, ![p 1 0, p 2 0]) 1| ≤ 20 * K ^ 2 * δ := by
      simpa only [abs_sub_comm] using hj 1
    have hs : |criticalEndpoint c (p 0) (p 3 0, ![p 1 0, p 2 0]) 1 - p 3 1| ≤ 7 * E := by
      simpa [criticalEndpoint, abs_sub_comm] using hspatial 0
    have hres : |criticalEndpoint c (p 0) (τ 2, ![τ 0, τ 1]) 1 - p 3 1| ≤
        7 * E + 20 * K ^ 2 * δ :=
      (abs_sub_le _ (criticalEndpoint c (p 0) (p 3 0, ![p 1 0, p 2 0]) 1) _).trans
        (by linarith only [he, hs])
    simpa using hres
  · have he : |criticalEndpoint c (p 0) (τ 2, ![τ 0, τ 1]) 2 -
        criticalEndpoint c (p 0) (p 3 0, ![p 1 0, p 2 0]) 2| ≤ 20 * K ^ 2 * δ := by
      simpa only [abs_sub_comm] using hj 2
    have hs : |criticalEndpoint c (p 0) (p 3 0, ![p 1 0, p 2 0]) 2 - p 3 2| ≤ 7 * E := by
      simpa [criticalEndpoint, abs_sub_comm] using hspatial 1
    have hres : |criticalEndpoint c (p 0) (τ 2, ![τ 0, τ 1]) 2 - p 3 2| ≤
        7 * E + 20 * K ^ 2 * δ :=
      (abs_sub_le _ (criticalEndpoint c (p 0) (p 3 0, ![p 1 0, p 2 0]) 2) _).trans
        (by linarith only [he, hs])
    simpa using hres

end Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited
