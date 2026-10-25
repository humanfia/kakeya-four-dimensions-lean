-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.TimeRowSelection, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/TimeRowSelection.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/TimeRowSelection.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/TimeRowSelection.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Mathlib


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory

noncomputable section

/-- Select an actual original active row in every occupied time bin.
The construction is measurable because the bin label is countable.
No trajectory or incidence law is changed. -/
theorem exists_time_row_of_original_comparison {Ω : Type*} {q : ℕ}
    (E : Set Ω) (time : Ω → ℝ) (row : Ω → Fin q → ℝ)
    (ρ K L : ℝ) (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hbound : ∀ z ∈ E, ‖row z‖ ≤ K)
    (hcmp : ∀ z ∈ E, ∀ z' ∈ E,
      ‖row z - row z'‖ ≤ L * (|time z - time z'| + ρ)) :
    ∃ F : ℝ → Fin q → ℝ, Measurable F ∧
      (∀ z ∈ E, ‖F (time z)‖ ≤ K) ∧
      (∀ z ∈ E, ‖F (time z) - row z‖ ≤ 2 * L * ρ) ∧
      (∀ z ∈ E, ∀ z' ∈ E,
        ‖F (time z) - F (time z')‖ ≤ 3 * L * (|time z - time z'| + ρ)) ∧
      (∀ t, F t = 0 ∨ ∃ z ∈ E, ⌊time z / ρ⌋ = ⌊t / ρ⌋ ∧ F t = row z) := by
  classical
  let active (j : ℤ) : Prop := ∃ z ∈ E, ⌊time z / ρ⌋ = j
  let rows (j : ℤ) : Fin q → ℝ :=
    if h : active j then row h.choose else 0
  let F (t : ℝ) : Fin q → ℝ := rows ⌊t / ρ⌋
  have hrows (j : ℤ) (hj : active j) :
      ∃ z ∈ E, ⌊time z / ρ⌋ = j ∧ rows j = row z := by
    exact ⟨hj.choose, hj.choose_spec.1, hj.choose_spec.2, dif_pos hj⟩
  have hrep (z : Ω) (hz : z ∈ E) :
      ∃ w ∈ E, ⌊time w / ρ⌋ = ⌊time z / ρ⌋ ∧ F (time z) = row w :=
    hrows _ ⟨z, hz, rfl⟩
  have hgap {t u : ℝ} (h : ⌊t / ρ⌋ = ⌊u / ρ⌋) : |t - u| ≤ ρ := by
    have h' := (Int.abs_sub_lt_one_of_floor_eq_floor h).le
    simpa only [← sub_div, abs_div, abs_of_pos hρ, div_le_iff₀ hρ, one_mul] using h'
  refine ⟨F, ?_, ?_, ?_, ?_, ?_⟩
  · exact (measurable_of_countable rows).comp ((measurable_id.div_const ρ).floor)
  · intro z hz
    obtain ⟨w, hw, _, heq⟩ := hrep z hz
    rw [heq]
    exact hbound w hw
  · intro z hz
    obtain ⟨w, hw, hbin, heq⟩ := hrep z hz
    rw [heq]
    exact (hcmp w hw z hz).trans (by nlinarith [hgap hbin])
  · intro z hz z' hz'
    obtain ⟨w, hw, hbin, heq⟩ := hrep z hz
    obtain ⟨w', hw', hbin', heq'⟩ := hrep z' hz'
    rw [heq, heq']
    have htime : |time w - time w'| ≤ |time z - time z'| + 2 * ρ := by
      have h1 := abs_sub_le (time w) (time z) (time w')
      have h2 := abs_sub_le (time z) (time z') (time w')
      have h3 := hgap hbin
      have h4 := hgap hbin'
      rw [abs_sub_comm (time z') (time w')] at h2
      linarith
    exact (hcmp w hw w' hw').trans (by
      nlinarith [mul_le_mul_of_nonneg_left htime hL,
        mul_nonneg hL (abs_nonneg (time z - time z'))])
  · intro t
    by_cases ht : active ⌊t / ρ⌋
    · exact Or.inr (hrows _ ht)
    · exact Or.inl (dif_neg ht)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
