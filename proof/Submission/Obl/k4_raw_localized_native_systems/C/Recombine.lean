import Mathlib

/-
Adapted from this LOT tree, o178, session x0596, `Recombine.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

/-!
# Recombining one-world binnings

Paired full-time binning is applied in each world whose own bad-pair mass is
small relative to its squared path mass.  The discarded worlds have squared mass
at most four times their bad mass, and by Jensen the weighted squared masses
dominate the square of the weighted mass.  Hence the retained weighted mass is
at least `(Σ ω m)² / 4 - Σ ω bad`.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open Finset

/-- Jensen for a probability vector: the square of the mean is at most the mean square. -/
theorem sq_weighted_sum_le {ι : Type*} [Fintype ι] (ω m : ι → ℝ) (hω0 : ∀ i, 0 ≤ ω i)
    (hω1 : ∑ i, ω i = 1) : (∑ i, ω i * m i) ^ 2 ≤ ∑ i, ω i * m i ^ 2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => Real.sqrt (ω i))
    (fun i => Real.sqrt (ω i) * m i)
  have hl : ∑ i, Real.sqrt (ω i) * (Real.sqrt (ω i) * m i) = ∑ i, ω i * m i := by
    apply Finset.sum_congr rfl; intro i _
    rw [← mul_assoc, Real.mul_self_sqrt (hω0 i)]
  have h1 : ∑ i, Real.sqrt (ω i) ^ 2 = ∑ i, ω i := by
    apply Finset.sum_congr rfl; intro i _; rw [Real.sq_sqrt (hω0 i)]
  have h2 : ∑ i, (Real.sqrt (ω i) * m i) ^ 2 = ∑ i, ω i * m i ^ 2 := by
    apply Finset.sum_congr rfl; intro i _; rw [mul_pow, Real.sq_sqrt (hω0 i)]
  rw [hl, h1, h2, hω1, one_mul] at hcs
  exact hcs

/-- **Recombination.** -/
theorem recombine_worlds {ι : Type*} [Fintype ι] [DecidableEq ι] (ω m bad : ι → ℝ)
    (hω0 : ∀ i, 0 ≤ ω i) (hω1 : ∑ i, ω i = 1) (hbad0 : ∀ i, 0 ≤ bad i)
    (S : Finset ι) (hS : ∀ i, i ∉ S → m i ^ 2 ≤ 4 * bad i) :
    (∑ i, ω i * m i) ^ 2 / 4 - ∑ i, ω i * bad i ≤ ∑ i ∈ S, ω i * (m i ^ 2 / 4) := by
  have hJ := sq_weighted_sum_le ω m hω0 hω1
  have hsplit : ∑ i, ω i * m i ^ 2 = ∑ i ∈ S, ω i * m i ^ 2 + ∑ i ∈ Sᶜ, ω i * m i ^ 2 := by
    rw [← Finset.sum_add_sum_compl S]
  have hout : ∑ i ∈ Sᶜ, ω i * m i ^ 2 ≤ 4 * ∑ i, ω i * bad i := by
    calc ∑ i ∈ Sᶜ, ω i * m i ^ 2 ≤ ∑ i ∈ Sᶜ, ω i * (4 * bad i) := by
          apply Finset.sum_le_sum; intro i hi
          exact mul_le_mul_of_nonneg_left (hS i (Finset.mem_compl.1 hi)) (hω0 i)
      _ ≤ ∑ i, ω i * (4 * bad i) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          intro i _ _; exact mul_nonneg (hω0 i) (by linarith [hbad0 i])
      _ = 4 * ∑ i, ω i * bad i := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  have hin : ∑ i ∈ S, ω i * (m i ^ 2 / 4) = (∑ i ∈ S, ω i * m i ^ 2) / 4 := by
    rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro i _; ring
  rw [hin]
  linarith

end Submission.Obl.k4_raw_localized_native_systems.C
