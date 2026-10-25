-- Adapted from this LOT tree, o117, session x0390, commit 0d48789,
-- Submission/Obl/k4_quadratic_candidate_atlas_conversion/MenuSelection.lean.

import Submission.Obl.k4_quadratic_finite_greedy_cover.GainMenu
import Submission.Obl.k4_quadratic_finite_greedy_cover.PrioritySelection

namespace Submission.Obl.k4_quadratic_finite_greedy_cover

open MeasureTheory Set

/-- The mass of a world-indexed finite cover is bounded by the sum of its
members under the same original laws. No disjointness is needed here. -/
theorem selectedUnion_weighted_le_sum {X ι β : Type*} [MeasurableSpace X]
    [Fintype β] (μ : β → Measure X) (ω : β → ℝ) (hω : ∀ w, 0 ≤ ω w)
    (H : β → Set X) (S : Finset ι) (world : ι → β) (V : ι → Set X) :
    (∑ w, ω w * (μ w).real (H w ∩ selectedUnion S world V w)) ≤
      ∑ a ∈ S, ω (world a) * (μ (world a)).real (H (world a) ∩ V a) := by
  classical
  have hworld (w : β) :
      (μ w).real (H w ∩ selectedUnion S world V w) ≤
        ∑ a ∈ S, if world a = w then (μ w).real (H w ∩ V a) else 0 := by
    have heq : H w ∩ selectedUnion S world V w =
        ⋃ a ∈ S, if world a = w then H w ∩ V a else ∅ := by
      ext p
      simp only [selectedUnion, mem_inter_iff, mem_iUnion, mem_ofPred_eq]
      aesop
    rw [heq]
    convert measureReal_biUnion_finset_le (μ := μ w) S
      (fun a => if world a = w then H w ∩ V a else ∅) using 1
    apply Finset.sum_congr rfl
    intro a ha
    split_ifs <;> simp
  calc
    _ ≤ ∑ w, ω w * (∑ a ∈ S, if world a = w then (μ w).real (H w ∩ V a) else 0) :=
      Finset.sum_le_sum (fun w _ => mul_le_mul_of_nonneg_left (hworld w) (hω w))
    _ = _ := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      simp [mul_ite, eq_comm]

/-- A menu specified only on a selected finite set can be averaged without
requiring arbitrary off-set labels to satisfy the menu bounds. -/
theorem finite_menu_mass_on {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (level bin : ι → ℕ) (hlevel : ∀ a ∈ S, level a < m) (hbin : ∀ a ∈ S, bin a < n)
    (mass : ι → ℝ) (c : ℝ) (h : c ≤ ∑ a ∈ S, mass a) :
    ∃ i < m, ∃ z < n,
      c / ((m * n : ℕ) : ℝ) ≤
        ∑ a ∈ S.filter (fun a => level a = i ∧ bin a = z), mass a := by
  classical
  let label : ι → Fin m × Fin n := fun a =>
    if ha : a ∈ S then (⟨level a, hlevel a ha⟩, ⟨bin a, hbin a ha⟩)
    else (⟨0, hm⟩, ⟨0, hn⟩)
  obtain ⟨i, z, hz⟩ := finite_menu_mass S m n hm hn label mass c h
  refine ⟨i, i.isLt, z, z.isLt, ?_⟩
  have heq : S.filter (fun a => label a = (i, z)) =
      S.filter (fun a => level a = (i : ℕ) ∧ bin a = (z : ℕ)) := by
    ext a
    by_cases ha : a ∈ S
    · simp [ha, label, Prod.ext_iff, Fin.ext_iff]
    · simp [ha]
  rwa [heq] at hz

/-- Select one old path level and one rounded gain bin from the full
trajectory-cylinder cover, before paying any small-derivative loss. -/
theorem candidate_level_gain_mass
    (W C m : ℕ) (ν : Fin W → Measure Trajectory) (ω : Fin W → ℝ)
    (H : Fin W → Set Incidence) (S : Finset (CandidateDatum C))
    (T : ℕ → ℕ) (lev : Fin C → ℕ) (γ : Fin C → Fin W) (j : Fin C → ℕ)
    (gain step c : ℝ) (hm : 0 < m) (hω : ∀ w, 0 ≤ ω w)
    (hstep : 0 < step) (hgain : 0 ≤ gain)
    (hlevel : ∀ a ∈ S, lev a.parent < m)
    (hgains : ∀ a ∈ S, gain ≤ a.gain ∧ a.gain ≤ 1 / 8)
    (hcover : c ≤ ∑ w, ω w * ((ν w).prod volume).real
      (H w ∩ selectedUnion S (fun a => γ a.parent) (candidateCylinder T lev j) w)) :
    ∃ i < m, ∃ z < ⌈(1 / 8 : ℝ) / step⌉₊ + 1,
      c / ((m * (⌈(1 / 8 : ℝ) / step⌉₊ + 1) : ℕ) : ℝ) ≤
        ∑ a ∈ S.filter (fun a => lev a.parent = i ∧ gainMenuIndex gain step a.gain = z),
          ω (γ a.parent) * ((ν (γ a.parent)).prod volume).real
            (H (γ a.parent) ∩ candidateCylinder T lev j a) := by
  classical
  apply finite_menu_mass_on S m (⌈(1 / 8 : ℝ) / step⌉₊ + 1) hm (by omega)
    (fun a => lev a.parent) (fun a => gainMenuIndex gain step a.gain) hlevel
    (fun a ha => gainMenuIndex_bound gain step a.gain (1 / 8) hstep hgain (hgains a ha).2)
  exact hcover.trans (selectedUnion_weighted_le_sum (fun w => (ν w).prod volume)
    ω hω H S (fun a => γ a.parent) (candidateCylinder T lev j))

end Submission.Obl.k4_quadratic_finite_greedy_cover
