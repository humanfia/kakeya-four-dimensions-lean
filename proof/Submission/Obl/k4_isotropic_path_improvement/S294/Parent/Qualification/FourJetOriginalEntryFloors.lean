-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.FourJetOriginalEntryFloors, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/FourJetOriginalEntryFloors.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1027, commit a194894209bc49bb7eab8e89d27e5205146250d6,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/FourJetOriginalEntryFloors.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalZoomEntryFloors
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FourJetWorldCells

/-! # Original refined-entry floors with arbitrary intercepts

Adapted from this LOT tree, o265, x0943 at 5207eac7,
Broad/Qualification/OriginalZoomEntryFloors.lean. That file attributes
its original source to o106, x0352 at 1e57792e. Only the four central
jets enter the cell multiplicity; finite carriers have no size cost.
-/
set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
open Set MeasureTheory
open scoped BigOperators
noncomputable section

theorem original_zoom_entry_floors_of_jets {Λ σ I : Type*}
    [MeasurableSpace Λ] [Fintype σ]
    (μ reference : Measure (Λ × ℝ)) (E : Set (Λ × ℝ)) (hE : MeasurableSet E)
    (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
    (b ρ H : ℝ) (hb : 0 < b) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hH : 0 ≤ H)
    (s : σ → ℝ) (hs : ∀ i, 0 < s i)
    (hsmall : ∀ i, (2+3*(H+1))*b ≤ ρ*s i)
    (ht : ∀ z ∈ E, z.2∈Icc (0 : ℝ) 1)
    (hjets : ∀ z ∈ E, |c z.1 1| ≤ H ∧ |c z.1 2| ≤ H ∧
      |c z.1 4| ≤ H ∧ |c z.1 6| ≤ H)
    (hstateFinite : (originalFineState c b '' E).Finite)
    (hworldFinite : ((fun z : Λ × ℝ => parameterCode ρ (c z.1)) '' E).Finite)
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
  let WF := hstateFinite.toFinset
  have hWF : ∀ z∈E, originalFineState c b z∈WF := by
    intro z hz
    exact hstateFinite.mem_toFinset.mpr ⟨z,hz,rfl⟩
  let IF := hworldFinite.toFinset.image coarse
  have hIF : ∀ z∈E, coarse (world z.1)∈IF := by
    intro z hz
    exact Finset.mem_image.mpr ⟨_,hworldFinite.mem_toFinset.mpr ⟨z,hz,rfl⟩,rfl⟩
  have hcenter (z : Λ × ℝ) (hz : z∈E) :
      |parameterCenter ρ (world z.1) 1| ≤ H+1 ∧
      |parameterCenter ρ (world z.1) 2| ≤ H+1 ∧
      |parameterCenter ρ (world z.1) 4| ≤ H+1 ∧
      |parameterCenter ρ (world z.1) 6| ≤ H+1 := by
    have hh (j : Fin 7) (hj : |c z.1 j| ≤ H) :
        |parameterCenter ρ (world z.1) j| ≤ H+1 := by
      have hd := original_parameter_center_distance ρ hρ (c z.1) j
      have ha := abs_sub_le (parameterCenter ρ (world z.1) j) (c z.1 j) 0
      rw [sub_zero,sub_zero,abs_sub_comm _ (c z.1 j)] at ha
      change |c z.1 j-parameterCenter ρ (world z.1) j| ≤ ρ at hd
      linarith
    exact ⟨hh 1 (hjets z hz).1,hh 2 (hjets z hz).2.1,
      hh 4 (hjets z hz).2.2.1,hh 6 (hjets z hz).2.2.2⟩
  have hex (i : σ) := exists_original_fine_state_zoom_cells_of_jets E c world
    (parameterCenter ρ) b ρ (s i) (H+1) hb hρ hρ1 (hs i) (by linarith)
    hcenter ht (hsmall i)
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
