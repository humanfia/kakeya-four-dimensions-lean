-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.OriginalZoomEntryFloors, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/OriginalZoomEntryFloors.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/OriginalZoomEntryFloors.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/OriginalZoomEntryFloors.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.CanonicalParameterWorlds
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ZoomFineStateCells
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalRefinedEntries
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Basic


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory
open scoped BigOperators

noncomputable section

def canonicalZoomCoefficients {Λ : Type*} (c : Λ → Fin 7 → ℝ) (ρ : ℝ) (l : Λ) : Fin 7 → ℝ :=
  zoomCoefficients ρ (parameterCenter ρ (parameterCode ρ (c l))) (c l)

def originalFineState {Λ : Type*} (c : Λ → Fin 7 → ℝ) (b : ℝ) (z : Λ × ℝ) : Fin 4 → ℤ :=
  Submission.Lib.K4CommonLocalChoice.cell b (zpos (c z.1) z.2)

def canonicalZoomCell {Λ : Type*} (c : Λ → Fin 7 → ℝ) (ρ s : ℝ)
    (z : Λ × ℝ) : Fin 4 → ℤ :=
  Submission.Lib.K4CommonLocalChoice.cell s (zpos (canonicalZoomCoefficients c ρ z.1) z.2)

def originalZoomEntry {Λ : Type*} (c : Λ → Fin 7 → ℝ) (b ρ s : ℝ) (z : Λ × ℝ) :
    (Fin 4 → ℤ) × (Fin 7 → ℤ) × (Fin 4 → ℤ) :=
  originalRefinedEntry (originalFineState c b) (fun y => parameterCode ρ (c y.1))
    (canonicalZoomCell c ρ s) z

theorem measurable_canonicalZoomCoefficients {Λ : Type*} [MeasurableSpace Λ]
    {c : Λ → Fin 7 → ℝ} (hc : Measurable c) (ρ : ℝ) :
    Measurable (canonicalZoomCoefficients c ρ) := by
  unfold canonicalZoomCoefficients zoomCoefficients parameterCenter parameterCode
  fun_prop

theorem measurable_originalFineState {Λ : Type*} [MeasurableSpace Λ]
    {c : Λ → Fin 7 → ℝ} (hc : Measurable c) (b : ℝ) :
    Measurable (originalFineState c b) := by
  unfold originalFineState Submission.Lib.K4CommonLocalChoice.cell zpos zx zy
  fun_prop

theorem measurable_canonicalZoomCell {Λ : Type*} [MeasurableSpace Λ]
    {c : Λ → Fin 7 → ℝ} (hc : Measurable c) (ρ s : ℝ) :
    Measurable (canonicalZoomCell c ρ s) := by
  have hm := measurable_canonicalZoomCoefficients hc ρ
  unfold canonicalZoomCell Submission.Lib.K4CommonLocalChoice.cell zpos zx zy
  fun_prop

/-- On one original parent, produce ALL final original refined-entry
floors directly from its actual coefficients and original fine-state
reference measure. Actual zoom-cell lists and finite carriers are
constructed inside. Only the genuine full-parameter block palettes are
supplied. Every loss is paid by the old reference's TOTAL mass. -/
theorem original_zoom_entry_floors {Λ σ I : Type*}
    [MeasurableSpace Λ] [Fintype σ]
    (μ reference : Measure (Λ × ℝ)) (E : Set (Λ × ℝ)) (hE : MeasurableSet E)
    (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
    (b ρ K : ℝ) (hb : 0 < b) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hK : 1 ≤ K)
    (s : σ → ℝ) (hs : ∀ i, 0 < s i)
    (hsmall : ∀ i, (2+3*(K+1))*b ≤ ρ*s i)
    (ht : ∀ z ∈ E, z.2∈Icc (0 : ℝ) 1) (hcoeff : ∀ z ∈ E, ∀ j, |c z.1 j| ≤ K)
    (coarse : (Fin 7 → ℤ) → I)
    (blocks : (Fin 4 → ℤ) × I → Finset (Fin 7 → ℤ)) (P : ℕ)
    (hP : ∀ q, (blocks q).card ≤ P)
    (hblocks : ∀ z ∈ E, parameterCode ρ (c z.1) ∈
      blocks (originalFineState c b z,coarse (parameterCode ρ (c z.1))))
    (palette : σ → I → ENNReal) (δ : σ → ENNReal)
    (hpalette : ∀ i (F : Finset I), ∑ a ∈ F, palette i a ≤ 1) :
    ∃ R : Set (Λ × ℝ), MeasurableSet R ∧ R ⊆ E ∧
      μ (E \ R) ≤ (∑ i, δ i*(P*256 : ℕ))*reference univ ∧
      ∀ i z, z∈R →
        δ i * reference ((originalFineState c b) ⁻¹' {originalFineState c b z}) *
          palette i (coarse (parameterCode ρ (c z.1))) <
            (μ.restrict R) ((originalZoomEntry c b ρ (s i)) ⁻¹' {originalZoomEntry c b ρ (s i) z}) := by
  classical
  let world : Λ → Fin 7 → ℤ := fun l => parameterCode ρ (c l)
  have hwmeas : Measurable (fun z : Λ × ℝ => world z.1) :=
    ((measurable_parameterCode ρ).comp hc).comp measurable_fst
  have hstate := measurable_originalFineState hc b
  have hcells := fun i => measurable_canonicalZoomCell hc ρ (s i)
  have hzbound : ∀ z ∈ E, ∀ j : Fin 4, |zpos (c z.1) z.2 j| ≤ 3*K+1 := by
    intro z hz j
    fin_cases j
    · change |z.2| ≤ _
      have hh : |z.2| ≤ 1 := by rw [abs_of_nonneg (ht z hz).1]; exact (ht z hz).2
      linarith
    · exact (abs_zx_le (hcoeff z hz) (ht z hz)).trans (by linarith)
    · exact (abs_zy_le (hcoeff z hz) (ht z hz) 0).trans (by linarith)
    · exact (abs_zy_le (hcoeff z hz) (ht z hz) 1).trans (by linarith)
  have hfinite := Submission.Lib.K4ContinuousPlanks.finite_range_floor_code
    (fun z : E => zpos (c z.val.1) z.val.2) (3*K+1)
      (fun z j => hzbound z.val z.property j) hb
  let WF := hfinite.toFinset
  have hWF : ∀ z∈E, originalFineState c b z∈WF := by
    intro z hz
    exact hfinite.mem_toFinset.mpr ⟨⟨z,hz⟩,rfl⟩
  have hworldFinite := original_parameter_worlds_finite E c ρ K hρ hcoeff
  let IF := hworldFinite.toFinset.image coarse
  have hIF : ∀ z∈E, coarse (world z.1)∈IF := by
    intro z hz
    exact Finset.mem_image.mpr ⟨_,hworldFinite.mem_toFinset.mpr ⟨z,hz,rfl⟩,rfl⟩
  have hex (i : σ) := exists_original_fine_state_zoom_cells_on_active_worlds E c world
    (parameterCenter ρ) b ρ (s i) (K+1) hb hρ hρ1 (hs i) (by linarith)
    (fun z hz => original_parameter_center_bound ρ K hρ hρ1 (c z.1) (hcoeff z hz))
    ht (hsmall i)
  choose cells hcard hknown using hex
  obtain ⟨R,hR,hsub,hloss,hfloor⟩ := original_refined_entry_selection μ E hE
    (originalFineState c b) hstate (fun z => world z.1) hwmeas
    (fun i => canonicalZoomCell c ρ (s i)) hcells coarse WF IF blocks cells P
    (fun _ => 256) hP hcard hWF hIF hblocks hknown
    (fun w => reference ((originalFineState c b) ⁻¹' {w})) palette δ (fun i => hpalette i IF)
  have hbudget : (∑ w∈WF, reference ((originalFineState c b) ⁻¹' {w})) ≤ reference univ := by
    rw [sum_measure_preimage_singleton WF (fun w _ => hstate (measurableSet_singleton w))]
    exact measure_mono (subset_univ _)
  exact ⟨R,hR,hsub,hloss.trans (mul_le_mul' le_rfl hbudget),hfloor⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
