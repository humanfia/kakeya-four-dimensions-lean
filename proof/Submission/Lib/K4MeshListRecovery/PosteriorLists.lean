import Submission.Lib.K4MeshListRecovery.MeasurableLists

/-!
Adapted from: here:o064

Turn aggregate posterior-neighbor agreement into short lists, without
selecting an individual candidate of possibly very small mass.  This is the
posterior-neighbors step of the supplied paper's candidate conversion.
-/

namespace Submission.Lib.K4MeshListRecovery

open Finset MeasureTheory Set
open Submission.Lib.K4OriginalLists

/-- A measurable list succeeds at least as often as the average neighbor
list of two independent draws from a subprobability vector. -/
theorem exists_posterior_neighbor_lists
    {X β : Type*} [MeasurableSpace X] [Fintype β]
    (π : X → β → ℝ) (hπmeas : ∀ a, Measurable (fun x => π x a))
    (hπnonneg : ∀ x a, 0 ≤ π x a) (hπmass : ∀ x, ∑ a, π x a ≤ 1)
    (allowed : Finset β) (D : ℕ) (neighbors : β → Finset β)
    (hneighbors : ∀ b, neighbors b ⊆ allowed ∧ (neighbors b).card ≤ D) :
    ∃ L : X → Finset β, MeasurableLists L ∧
      (∀ x, L x ⊆ allowed ∧ (L x).card ≤ D) ∧
      ∀ x, (∑ b, π x b * ∑ a ∈ neighbors b, π x a) ≤ ∑ a ∈ L x, π x a := by
  classical
  obtain ⟨L, hLmeas, hL, hmax⟩ :=
    exists_measurable_maximizing_lists allowed D π hπmeas
  refine ⟨L, hLmeas, hL, fun x => ?_⟩
  have hLnonneg : 0 ≤ ∑ a ∈ L x, π x a := sum_nonneg (fun a _ => hπnonneg x a)
  calc
    _ ≤ ∑ b, π x b * ∑ a ∈ L x, π x a := sum_le_sum (fun b _ =>
      mul_le_mul_of_nonneg_left (hmax x (neighbors b) (hneighbors b).1 (hneighbors b).2)
        (hπnonneg x b))
    _ = (∑ b, π x b) * ∑ a ∈ L x, π x a := by rw [sum_mul]
    _ ≤ 1 * ∑ a ∈ L x, π x a := mul_le_mul_of_nonneg_right (hπmass x) hLnonneg
    _ = _ := one_mul _

/-- Integrating the posterior construction keeps the full unnormalized
covered-law mass of neighbor agreement. -/
theorem recover_posterior_neighbor_mass
    {X β : Type*} [MeasurableSpace X] [Fintype β]
    (μ : Measure X) [IsFiniteMeasure μ]
    (π : X → β → ℝ) (hπmeas : ∀ a, Measurable (fun x => π x a))
    (hπnonneg : ∀ x a, 0 ≤ π x a) (hπmass : ∀ x, ∑ a, π x a ≤ 1)
    (allowed : Finset β) (D : ℕ) (neighbors : β → Finset β)
    (hneighbors : ∀ b, neighbors b ⊆ allowed ∧ (neighbors b).card ≤ D)
    (mass : ℝ) (hpair : mass ≤ ∫ x, ∑ b, π x b * ∑ a ∈ neighbors b, π x a ∂μ) :
    ∃ L : X → Finset β, MeasurableLists L ∧
      (∀ x, L x ⊆ allowed ∧ (L x).card ≤ D) ∧
      mass ≤ ∫ x, ∑ a ∈ L x, π x a ∂μ := by
  classical
  obtain ⟨L, hLmeas, hL, hpoint⟩ :=
    exists_posterior_neighbor_lists π hπmeas hπnonneg hπmass allowed D neighbors hneighbors
  have hπint (a : β) : Integrable (fun x => π x a) μ := by
    apply Integrable.of_bound (hπmeas a).aestronglyMeasurable 1
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hπnonneg x a)]
    exact (single_le_sum (fun b _ => hπnonneg x b) (mem_univ a)).trans (hπmass x)
  have hLint : Integrable (fun x => ∑ a ∈ L x, π x a) μ :=
    integrable_listDensity μ π L hπint hLmeas
  have hpairint : Integrable (fun x => ∑ b, π x b * ∑ a ∈ neighbors b, π x a) μ := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards with x
    have hnn : 0 ≤ ∑ b, π x b * ∑ a ∈ neighbors b, π x a :=
      sum_nonneg (fun b _ => mul_nonneg (hπnonneg x b)
        (sum_nonneg (fun a _ => hπnonneg x a)))
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    apply (hpoint x).trans
    exact (sum_le_sum_of_subset_of_nonneg (subset_univ (L x))
      (fun a _ _ => hπnonneg x a)).trans (hπmass x)
  exact ⟨L, hLmeas, hL, hpair.trans (integral_mono hpairint hLint hpoint)⟩

/-- The same construction directly on unnormalized joint densities.  No
lower bound on an observation's marginal mass is required. -/
theorem recover_neighbor_density_mass
    {X β : Type*} [MeasurableSpace X] [Fintype β]
    (μ : Measure X) (p : X → β → ℝ)
    (hpmeas : ∀ a, Measurable (fun x => p x a))
    (hpint : ∀ a, Integrable (fun x => p x a) μ) (hpnonneg : ∀ x a, 0 ≤ p x a)
    (allowed : Finset β) (D : ℕ) (neighbors : β → Finset β)
    (hneighbors : ∀ b, neighbors b ⊆ allowed ∧ (neighbors b).card ≤ D)
    (mass : ℝ) (hpair : mass ≤ ∫ x,
      (∑ b, p x b * ∑ a ∈ neighbors b, p x a) / (∑ a, p x a) ∂μ) :
    ∃ L : X → Finset β, MeasurableLists L ∧
      (∀ x, L x ⊆ allowed ∧ (L x).card ≤ D) ∧
      mass ≤ ∫ x, ∑ a ∈ L x, p x a ∂μ := by
  classical
  obtain ⟨L, hLmeas, hL, hmax⟩ :=
    exists_measurable_maximizing_lists allowed D p hpmeas
  have hpoint (x : X) :
      (∑ b, p x b * ∑ a ∈ neighbors b, p x a) / (∑ a, p x a) ≤ ∑ a ∈ L x, p x a := by
    by_cases hz : ∑ a, p x a = 0
    · rw [hz, div_zero]
      exact sum_nonneg (fun a _ => hpnonneg x a)
    · have hpos : 0 < ∑ a, p x a :=
        lt_of_le_of_ne (sum_nonneg (fun a _ => hpnonneg x a)) (Ne.symm hz)
      apply (div_le_iff₀ hpos).mpr
      calc
        _ ≤ ∑ b, p x b * ∑ a ∈ L x, p x a := sum_le_sum (fun b _ =>
          mul_le_mul_of_nonneg_left (hmax x (neighbors b) (hneighbors b).1 (hneighbors b).2)
            (hpnonneg x b))
        _ = _ := by rw [← sum_mul]; ring
  have htotint : Integrable (fun x => ∑ a, p x a) μ :=
    integrable_finsetSum _ (fun a _ => hpint a)
  have hpairint : Integrable (fun x =>
      (∑ b, p x b * ∑ a ∈ neighbors b, p x a) / (∑ a, p x a)) μ := by
    have hpairmeas : Measurable (fun x =>
        (∑ b, p x b * ∑ a ∈ neighbors b, p x a) / (∑ a, p x a)) := by fun_prop
    apply htotint.mono' hpairmeas.aestronglyMeasurable
    filter_upwards with x
    have hnn : 0 ≤ (∑ b, p x b * ∑ a ∈ neighbors b, p x a) / (∑ a, p x a) :=
      div_nonneg (sum_nonneg (fun b _ => mul_nonneg (hpnonneg x b)
        (sum_nonneg (fun a _ => hpnonneg x a)))) (sum_nonneg (fun a _ => hpnonneg x a))
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact (hpoint x).trans (sum_le_sum_of_subset_of_nonneg (subset_univ (L x))
      (fun a _ _ => hpnonneg x a))
  refine ⟨L, hLmeas, hL, hpair.trans (integral_mono hpairint ?_ hpoint)⟩
  exact integrable_listDensity μ p L hpint hLmeas

end Submission.Lib.K4MeshListRecovery
