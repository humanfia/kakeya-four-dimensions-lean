-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
-- Adapted from this LOT tree, o107, session x0735, commit cc2492748f08.
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/MarginalFloors.lean.
import Mathlib

/-! Simultaneous floors for finitely many possibly overlapping label families. -/

namespace Submission.Obl.k4_finite_affine_parent_sources

open Finset

/-- Retain all marginal floors simultaneously, losing at most the sum of their
thresholds. The label sets may overlap arbitrarily; only the current support
is restricted, while all thresholds and reference objects remain fixed. -/
theorem exists_simultaneous_marginal_floors
    {Ω J : Type*} [DecidableEq Ω] [Fintype J] [DecidableEq J]
    (U : Finset Ω) (w : Ω → ℝ) (cells : J → Finset Ω) (threshold : J → ℝ)
    (hthreshold : ∀ j, 0 ≤ threshold j) :
    ∃ S : Finset Ω, S ⊆ U ∧
      (∑ e ∈ U, w e) - (∑ j, threshold j) ≤ ∑ e ∈ S, w e ∧
      ∀ j, (S ∩ cells j).Nonempty → threshold j ≤ ∑ e ∈ S ∩ cells j, w e := by
  classical
  let mass : Finset Ω → ℝ := fun S => ∑ e ∈ S, w e
  let active : Finset Ω → Finset J := fun S => univ.filter (fun j => (S ∩ cells j).Nonempty)
  let penalty : Finset Ω → ℝ := fun S => ∑ j ∈ active S, threshold j
  let score : Finset Ω → ℝ := fun S => mass S - penalty S
  obtain ⟨S, hS, hmax⟩ := exists_max_image U.powerset score
    ⟨U, mem_powerset.mpr (Subset.rfl)⟩
  have hSU : S ⊆ U := mem_powerset.mp hS
  refine ⟨S, hSU, ?_, ?_⟩
  · have hm := hmax U (mem_powerset.mpr (Subset.rfl))
    have hpenU : penalty U ≤ ∑ j, threshold j :=
      sum_le_sum_of_subset_of_nonneg (subset_univ (active U)) (fun j _ _ => hthreshold j)
    have hpenS : 0 ≤ penalty S := sum_nonneg fun j _ => hthreshold j
    change mass U - (∑ j, threshold j) ≤ mass S
    change mass U - penalty U ≤ mass S - penalty S at hm
    linarith
  · intro j hj
    by_contra hnot
    have hlight : mass (S ∩ cells j) < threshold j := lt_of_not_ge hnot
    let V := S \ cells j
    have hVS : V ⊆ S := sdiff_subset
    have hVU : V ⊆ U := hVS.trans hSU
    have hmaxV := hmax V (mem_powerset.mpr hVU)
    have hjactive : j ∈ active S := mem_filter.mpr ⟨mem_univ j, hj⟩
    have hactive : active V ⊆ active S := by
      intro k hk
      obtain ⟨e, he⟩ := (mem_filter.mp hk).2
      exact mem_filter.mpr ⟨mem_univ k,
        ⟨e, mem_inter.mpr ⟨hVS (mem_inter.mp he).1, (mem_inter.mp he).2⟩⟩⟩
    have hjnot : j ∉ active V := by
      intro h
      obtain ⟨e, he⟩ := (mem_filter.mp h).2
      exact (mem_sdiff.mp (mem_inter.mp he).1).2 (mem_inter.mp he).2
    have hpen : penalty V + threshold j ≤ penalty S := by
      have hsub : insert j (active V) ⊆ active S :=
        insert_subset_iff.mpr ⟨hjactive, hactive⟩
      have hsum := sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => hthreshold k)
      rw [sum_insert hjnot] at hsum
      simpa only [penalty, add_comm] using hsum
    have hmass : mass V + mass (S ∩ cells j) = mass S := by
      simpa only [mass, V, add_comm] using sum_inter_add_sum_sdiff S (cells j) w
    change mass V - penalty V ≤ mass S - penalty S at hmaxV
    linarith

end Submission.Obl.k4_finite_affine_parent_sources
