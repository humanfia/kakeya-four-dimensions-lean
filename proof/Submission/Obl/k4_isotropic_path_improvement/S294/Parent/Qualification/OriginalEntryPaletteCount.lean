-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.OriginalEntryPaletteCount, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/OriginalEntryPaletteCount.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/OriginalEntryPaletteCount.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/OriginalEntryPaletteCount.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Lib.K4OutputReferenceMenus


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory

noncomputable section

/-- Count a family of actual original entry laws using their COMMON
original palette. The entries may overlap in the source. Positive
supporting velocity bins and their palette floors are constructed here. -/
theorem original_entry_palette_count {Ω V I : Type*}
    [MeasurableSpace Ω] [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
    (π : Measure V) [IsProbabilityMeasure π] (entry : I → Measure Ω)
    [∀ i, IsFiniteMeasure (entry i)] (control : Ω → V) (hm : Measurable control)
    (S : Finset I) (K L : ENNReal)
    (hpositive : ∀ i ∈ S, entry i univ ≠ 0)
    (hcap : ∀ i ∈ S, ∀ A : Set V, MeasurableSet A →
      entry i (control ⁻¹' A) ≤ K * entry i univ * π A)
    (hlist : ∀ v, ((S.filter fun i => entry i (control ⁻¹' {v}) ≠ 0).card : ENNReal) ≤ L) :
    (S.card : ENNReal) ≤ K * L := by
  let C : I → Set V := fun i => {v | entry i (control ⁻¹' {v}) ≠ 0}
  have hCm (i : I) : MeasurableSet (C i) := (Set.to_countable _).measurableSet
  apply Submission.Lib.K4OutputReferenceMenus.palette_support_count π S C
    (fun i _ => hCm i) K L ?_ ?_
  · intro i hi
    have hmap : ∀ᵐ v ∂(entry i).map control, ((entry i).map control) {v} ≠ 0 :=
      ae_iff_of_countable.mpr (fun v hv => hv)
    have hpull := ae_of_ae_map hm.aemeasurable hmap
    have hcompat : ∀ᵐ p ∂entry i, control p ∈ C i := by
      filter_upwards [hpull] with p hp
      simpa only [C,mem_ofPred_eq,Measure.map_apply hm (measurableSet_singleton _)] using hp
    have hfull : entry i (control ⁻¹' C i) = entry i univ := by
      apply measure_congr
      filter_upwards [hcompat] with p hp
      simp only [mem_preimage,hp,mem_univ]
    have hmass := hcap i hi (C i) (hCm i)
    rw [hfull] at hmass
    calc
      1 = (entry i univ)⁻¹ * entry i univ :=
        (ENNReal.inv_mul_cancel (hpositive i hi) (measure_ne_top _ _)).symm
      _ ≤ (entry i univ)⁻¹ * (K * entry i univ * π (C i)) := mul_le_mul' le_rfl hmass
      _ = K * π (C i) := by
        rw [show K * entry i univ * π (C i) = entry i univ * (K * π (C i)) by ac_rfl,
          ← mul_assoc,ENNReal.inv_mul_cancel (hpositive i hi) (measure_ne_top _ _),one_mul]
  · intro v
    simpa only [Submission.Lib.K4OutputReferenceMenus.paletteStates,C,mem_ofPred_eq] using hlist v

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
