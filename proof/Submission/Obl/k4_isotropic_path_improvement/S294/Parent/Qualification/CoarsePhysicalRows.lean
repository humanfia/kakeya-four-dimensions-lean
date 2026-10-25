-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.CoarsePhysicalRows, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/CoarsePhysicalRows.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/CoarsePhysicalRows.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/CoarsePhysicalRows.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.RoundedCurveCover


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory

noncomputable section

/-- Two actual points whose fine-state corners assign the same
coarse physical cube differ by at most three coarse widths. -/
theorem physical_distance_of_rounded_code {b ρ : ℝ} (hb : 0 < b) (hρ : 0 < ρ)
    (hbρ : b ≤ ρ) (x y : Fin 4 → ℝ)
    (hcode : roundedPhysicalCode b ρ x = roundedPhysicalCode b ρ y) :
    ‖x - y‖ ≤ 3 * ρ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  change |x j - y j| ≤ 3 * ρ
  let u : ℝ := b * (⌊x j / b⌋ : ℝ)
  let v : ℝ := b * (⌊y j / b⌋ : ℝ)
  have hxu : |x j - u| ≤ b := by
    simpa only [u, mul_comm] using
      Submission.Lib.K4VelocityStrips.midpoint_floor_center_bound hb (x j)
  have hyv : |y j - v| ≤ b := by
    simpa only [v, mul_comm] using
      Submission.Lib.K4VelocityStrips.midpoint_floor_center_bound hb (y j)
  have hsame : ⌊u / ρ⌋ = ⌊v / ρ⌋ := congrFun hcode j
  have huv := (Int.abs_sub_lt_one_of_floor_eq_floor hsame).le
  rw [← sub_div, abs_div, abs_of_pos hρ, div_le_iff₀ hρ, one_mul] at huv
  have h1 := abs_sub_le (x j) u (y j)
  have h2 := abs_sub_le u v (y j)
  rw [abs_sub_comm v (y j)] at h2
  linarith

/-- Choose an ACTUAL active field row in every occupied physical
cube. Original physical comparison produces the coarse-row fit;
countable cube labels make the selection measurable. -/
theorem exists_original_coarse_rows {Ω : Type*} (E : Set Ω)
    (physical : Ω → Fin 4 → ℝ) (field : Ω → Fin 3 → ℝ)
    (b ρ B L : ℝ) (hb : 0 < b) (hρ : 0 < ρ) (hbρ : b ≤ ρ)
    (hB : 0 ≤ B) (hL : 0 ≤ L) (hbound : ∀ z ∈ E, ‖field z‖ ≤ B)
    (hcompare : ∀ z ∈ E, ∀ z' ∈ E,
      ‖field z - field z'‖ ≤ L * (‖physical z - physical z'‖ + ρ)) :
    ∃ row : (Fin 4 → ℤ) → Fin 3 → ℝ, Measurable row ∧
      (∀ C, ‖row C‖ ≤ B) ∧
      ∀ z ∈ E, ‖field z - row (roundedPhysicalCode b ρ (physical z))‖ ≤ 4 * L * ρ := by
  classical
  let active : (Fin 4 → ℤ) → Prop := fun C =>
    ∃ z, z ∈ E ∧ roundedPhysicalCode b ρ (physical z) = C
  let row : (Fin 4 → ℤ) → Fin 3 → ℝ := fun C =>
    if h : active C then field (Classical.choose h) else 0
  refine ⟨row, measurable_of_countable _, ?_, ?_⟩
  · intro C
    by_cases h : active C
    · simpa only [row, dite_eq_left h] using hbound _ (Classical.choose_spec h).1
    · simpa only [row, dite_eq_right h, norm_zero] using hB
  · intro z hz
    let C := roundedPhysicalCode b ρ (physical z)
    have h : active C := ⟨z, hz, rfl⟩
    have hs := Classical.choose_spec h
    have hd : ‖physical z - physical (Classical.choose h)‖ ≤ 3 * ρ :=
      physical_distance_of_rounded_code hb hρ hbρ _ _ hs.2.symm
    have hc := hcompare z hz _ hs.1
    change ‖field z - row C‖ ≤ _
    rw [show row C = field (Classical.choose h) by simp only [row, dite_eq_left h]]
    calc
      _ ≤ L * (‖physical z - physical (Classical.choose h)‖ + ρ) := hc
      _ ≤ L * (3 * ρ + ρ) := mul_le_mul_of_nonneg_left (add_le_add hd le_rfl) hL
      _ = _ := by ring

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
