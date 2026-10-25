-- Adapted from this LOT tree, o117, session x0390, commit 0d48789,
-- Submission/Obl/k4_quadratic_candidate_atlas_conversion/PacketBudget.lean.

import Submission.Obl.k4_quadratic_finite_greedy_cover.Candidates

namespace Submission.Obl.k4_quadratic_finite_greedy_cover

open MeasureTheory Set

/-- At one time depth, disjoint trajectory assignments in each world and time
bin have total reference incidence mass at most one. -/
theorem full_packet_mass_le_one {ι : Type*} [Fintype ι]
    (W : ℕ) (ν : Fin W → Measure Trajectory) (ω : Fin W → ℝ)
    (γ : ι → Fin W) (j : ι → ℕ) (T : ℕ) (A : ι → Set Trajectory)
    (hν : ∀ w, IsProbabilityMeasure (ν w)) (hω : ∀ w, 0 ≤ ω w)
    (hωsum : (∑ w, ω w) = 1) (hAm : ∀ a, MeasurableSet (A a))
    (hj : ∀ a, j a < 2 ^ T)
    (hdisj : ∀ a a', a ≠ a' → γ a = γ a' → j a = j a' → Disjoint (A a) (A a')) :
    (∑ a, ENNReal.ofReal (ω (γ a)) * (ν (γ a)).prod volume
      (A a ×ˢ Icc ((j a : ℝ) / (2 : ℝ) ^ T) (((j a : ℝ) + 1) / (2 : ℝ) ^ T))) ≤ 1 := by
  classical
  have (w : Fin W) : IsProbabilityMeasure (ν w) := hν w
  let F : ι → Set Incidence := fun a =>
    A a ×ˢ Icc ((j a : ℝ) / (2 : ℝ) ^ T) (((j a : ℝ) + 1) / (2 : ℝ) ^ T)
  let H := levelMask 0 T (fun _ : ι => 0) γ j F
  have hFm : ∀ a, (fun _ : ι => 0) a = 0 → MeasurableSet (F a) :=
    fun a _ => (hAm a).prod measurableSet_Icc
  have hF : ∀ a, (fun _ : ι => 0) a = 0 → ∀ p ∈ F a,
      p.1 ∈ A a ∧ p.2 ∈ Icc ((j a : ℝ) / (2 : ℝ) ^ T)
        (((j a : ℝ) + 1) / (2 : ℝ) ^ T) := fun _ _ _ hp => hp
  have hA : ∀ a a', (fun _ : ι => 0) a = 0 → (fun _ : ι => 0) a' = 0 →
      a ≠ a' → γ a = γ a' → j a = j a' → Disjoint (A a) (A a') :=
    fun a a' _ _ hne hγ hj => hdisj a a' hne hγ hj
  have hmass := levelMask_mass ν (fun w => ENNReal.ofReal (ω w))
    0 T (fun _ : ι => 0) γ j A F hFm hF hA
  have heq : (∑ w, ENNReal.ofReal (ω w) * (ν w).prod volume (H w)) =
      ∑ a, ENNReal.ofReal (ω (γ a)) * (ν (γ a)).prod volume (F a) := by
    simpa [H] using hmass
  have hsub (w : Fin W) : H w ⊆ Set.univ ×ˢ Icc (0 : ℝ) 1 := by
    intro p hp
    obtain ⟨a, _, _, hpa, _⟩ := hp
    have hq : 0 < (2 : ℝ) ^ T := by positivity
    have hlow : 0 ≤ (j a : ℝ) / (2 : ℝ) ^ T := div_nonneg (Nat.cast_nonneg _) hq.le
    have hjR : (j a : ℝ) + 1 ≤ (2 : ℝ) ^ T := by exact_mod_cast Nat.succ_le_of_lt (hj a)
    have hhigh : ((j a : ℝ) + 1) / (2 : ℝ) ^ T ≤ 1 := (div_le_one hq).mpr hjR
    exact ⟨mem_univ _, hlow.trans hpa.2.1, hpa.2.2.trans hhigh⟩
  calc
    _ = ∑ w, ENNReal.ofReal (ω w) * (ν w).prod volume (H w) := heq.symm
    _ ≤ ∑ w, ENNReal.ofReal (ω w) * (ν w).prod volume (Set.univ ×ˢ Icc (0 : ℝ) 1) :=
      Finset.sum_le_sum (fun w _ => mul_le_mul' le_rfl (measure_mono (hsub w)))
    _ = 1 := by
      simp only [Measure.prod_prod, measure_univ, Real.volume_Icc, sub_zero,
        ENNReal.ofReal_one, mul_one]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun w _ => hω w), hωsum]
      exact ENNReal.ofReal_one

end Submission.Obl.k4_quadratic_finite_greedy_cover
