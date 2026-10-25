-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.OutputReferenceEvents, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/OutputReferenceEvents.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/OutputReferenceEvents.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/OutputReferenceEvents.lean.
-- Existing source attributions are preserved below.

import Submission.Lib.K4OutputReferenceMenus

/-! Absolute history caps combine at a physical output state before its
original reference floor is used. The history label need not be included
in the physical state. The reference-transfer primitive is imported. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped ENNReal

/-- Scalar event caps are the Unit-control instance of the accepted
original-reference palette transfer. -/
theorem output_reference_event_cap {Ω J I : Type*}
    [MeasurableSpace Ω] [Fintype J]
    (μ θ : Measure Ω) (hθ : θ ≤ μ) (E : J → Set Ω) (state : Ω → I)
    (menus : J → Finset I) (w : J → ENNReal) (C : ENNReal)
    (hcover : ∀ᵐ p ∂θ, ∃ j, p ∈ E j)
    (hmenu : ∀ᵐ p ∂θ, ∀ j, p ∈ E j → state p ∈ menus j)
    (A : Set Ω) (hA : MeasurableSet A)
    (hcap : ∀ j, μ (E j ∩ A) ≤ C * w j) (i : I) :
    θ ({p | state p = i} ∩ A) ≤
      C * Submission.Lib.K4OutputReferenceMenus.outputReferenceWeight menus w i := by
  have hcapA (j : J) (U : Set Unit) (hU : MeasurableSet U) :
      (μ.restrict A) {p | p ∈ E j ∧ () ∈ U} ≤ C * w j * Measure.dirac () U := by
    by_cases hu : () ∈ U
    · simpa only [hu, and_true, Measure.restrict_apply' hA,
        Measure.dirac_apply_of_mem hu, mul_one, setOf_mem_eq] using hcap j
    · rw [Measure.dirac_apply' () hU]
      simp [hu]
  have hbound := Submission.Lib.K4OutputReferenceMenus.output_reference_palette_cap
    (μ.restrict A) (θ.restrict A) (Measure.restrict_mono_measure hθ A)
    E state (fun _ => ()) (Measure.dirac ()) menus w C
    ((ae_mono Measure.restrict_le_self) hcover)
    ((ae_mono Measure.restrict_le_self) hmenu) hcapA i univ MeasurableSet.univ
  simpa only [mem_univ, and_true, measure_univ, mul_one, Measure.restrict_apply' hA] using hbound

/-- A floor against the SUM of compatible full history references suffices
for a relative event cap on the SAME physical state. -/
theorem output_reference_relative_event_cap {Ω J I : Type*}
    [MeasurableSpace Ω] [Fintype J]
    (μ θ : Measure Ω) (hθ : θ ≤ μ) (E : J → Set Ω) (state : Ω → I)
    (menus : J → Finset I) (w : J → ENNReal) (C δ : ENNReal)
    (hδ0 : δ ≠ 0) (hδtop : δ ≠ ∞)
    (hcover : ∀ᵐ p ∂θ, ∃ j, p ∈ E j)
    (hmenu : ∀ᵐ p ∂θ, ∀ j, p ∈ E j → state p ∈ menus j)
    (A : Set Ω) (hA : MeasurableSet A)
    (hcap : ∀ j, μ (E j ∩ A) ≤ C * w j) (i : I)
    (hfloor : δ * Submission.Lib.K4OutputReferenceMenus.outputReferenceWeight menus w i ≤
      θ {p | state p = i}) :
    θ ({p | state p = i} ∩ A) ≤ (δ⁻¹ * C) * θ {p | state p = i} := by
  have href := mul_le_mul' (le_refl δ⁻¹) hfloor
  rw [← mul_assoc, ENNReal.inv_mul_cancel hδ0 hδtop, one_mul] at href
  calc
    _ ≤ C * Submission.Lib.K4OutputReferenceMenus.outputReferenceWeight menus w i :=
      output_reference_event_cap μ θ hθ E state menus w C hcover hmenu A hA hcap i
    _ ≤ C * (δ⁻¹ * θ {p | state p = i}) := mul_le_mul' le_rfl href
    _ = _ := by ac_rfl

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
