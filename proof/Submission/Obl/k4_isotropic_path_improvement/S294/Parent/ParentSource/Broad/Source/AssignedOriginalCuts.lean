-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.AssignedOriginalCuts, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/AssignedOriginalCuts.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/AssignedOriginalCuts.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.AssignedPacketModel

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.FrozenPacket

open Set MeasureTheory
open scoped ENNReal

noncomputable section

theorem measurableEmbedding_forgetAssigned (p : FrozenPacket) :
    MeasurableEmbedding p.forgetAssigned :=
  (MeasurableEmbedding.subtype_coe p.measurable_assigned).prodMap MeasurableEmbedding.id

def originalIncidence (p : FrozenPacket) (z : p.AssignedLine × ℝ) : Incidence :=
  p.timeChange.symm (p.forgetAssigned z)

theorem measurable_originalIncidence (p : FrozenPacket) : Measurable p.originalIncidence :=
  p.timeChange.symm.measurable.comp p.measurable_forgetAssigned

theorem originalIncidence_fst (p : FrozenPacket) (z : p.AssignedLine × ℝ) :
    (p.originalIncidence z).1 = (z.1 : Line) := by
  have hh := congrArg Prod.fst (p.timeChange_apply (p.originalIncidence z))
  calc
    _ = (p.timeChange (p.originalIncidence z)).1 := hh.symm
    _ = (p.forgetAssigned z).1 := congrArg Prod.fst (p.timeChange.apply_symm_apply _)
    _ = _ := rfl

theorem assignedSelectedEvent_originalIncidence (p : FrozenPacket) (J : Set Incidence) :
    p.assignedSelectedEvent J = p.originalIncidence ⁻¹' J := by
  ext z
  constructor
  · rintro ⟨q, hq, heq⟩
    change p.timeChange.symm (p.forgetAssigned z) ∈ J
    rw [← heq, MeasurableEquiv.symm_apply_apply]
    exact hq
  · intro hz
    exact ⟨p.originalIncidence z, hz, p.timeChange.apply_symm_apply _⟩

/-- Push the native selected law all the way back to the original
incidences. Both the indexed line and the full old reference are exact. -/
theorem map_assignedSelectedLaw_original (p : FrozenPacket) (ν : Measure Line)
    [IsFiniteMeasure ν] (hA : ν p.assigned ≠ 0) {J : Set Incidence}
    (hJ : MeasurableSet J) (hJF : J ⊆ p.counted) :
    (p.assignedSelectedLaw ν J).map p.originalIncidence =
      (ENNReal.ofReal p.unitFrame.q * ν p.assigned)⁻¹ • (ν.prod volume).restrict J := by
  change (p.assignedSelectedLaw ν J).map (p.timeChange.symm ∘ p.forgetAssigned) = _
  rw [← Measure.map_map p.timeChange.symm.measurable p.measurable_forgetAssigned,
    p.map_assignedSelectedLaw ν hA hJ, p.selectedLaw_original ν hA hJ hJF,
    Measure.map_smul _ p.timeChange.symm.measurable.aemeasurable,
    Measure.map_map p.timeChange.symm.measurable p.timeChange.measurable]
  have heq : (p.timeChange.symm ∘ p.timeChange) = id := by
    funext z
    exact p.timeChange.symm_apply_apply z
  rw [heq, Measure.map_id]

theorem assignedSelectedLaw_original_apply (p : FrozenPacket) (ν : Measure Line)
    [IsFiniteMeasure ν] (hA : ν p.assigned ≠ 0) {J : Set Incidence}
    (hJ : MeasurableSet J) (hJF : J ⊆ p.counted) {S : Set Incidence} (hS : MeasurableSet S) :
    (p.assignedSelectedLaw ν J) (p.originalIncidence ⁻¹' S) =
      (ENNReal.ofReal p.unitFrame.q * ν p.assigned)⁻¹ * (ν.prod volume) (S ∩ J) := by
  rw [← Measure.map_apply p.measurable_originalIncidence hS,
    p.map_assignedSelectedLaw_original ν hA hJ hJF,
    Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hS]

theorem assignedSelectedLaw_finite (p : FrozenPacket) (ν : Measure Line)
    [IsFiniteMeasure ν] (hA : ν p.assigned ≠ 0) {J : Set Incidence}
    (hJ : MeasurableSet J) (hJF : J ⊆ p.counted) :
    IsFiniteMeasure (p.assignedSelectedLaw ν J) := by
  constructor
  rw [p.assignedSelectedLaw_mass ν hA hJ]
  exact ((p.selectedLaw_le ν hJF univ).trans (p.law_mass_le_one ν hA)).trans_lt (by simp)

/-- Return an arbitrary native incidence cut to the original indexed lines
and original time. The original source and its full prior remain fixed. -/
def originalCut (p : FrozenPacket) (J : Set Incidence)
    (keep : Set (p.AssignedLine × ℝ)) : Set Incidence :=
  J ∩ p.timeChange ⁻¹' (p.forgetAssigned '' keep)

theorem measurable_originalCut (p : FrozenPacket) {J : Set Incidence}
    (hJ : MeasurableSet J) {keep : Set (p.AssignedLine × ℝ)} (hkeep : MeasurableSet keep) :
    MeasurableSet (p.originalCut J keep) :=
  hJ.inter (((p.measurableEmbedding_forgetAssigned.measurableSet_image.mpr hkeep).preimage
    p.timeChange.measurable))

theorem originalCut_subset (p : FrozenPacket) (J : Set Incidence)
    (keep : Set (p.AssignedLine × ℝ)) : p.originalCut J keep ⊆ J := inter_subset_left

theorem assignedSelectedEvent_originalCut (p : FrozenPacket) (J : Set Incidence)
    (keep : Set (p.AssignedLine × ℝ)) :
    p.assignedSelectedEvent (p.originalCut J keep) = p.assignedSelectedEvent J ∩ keep := by
  ext z
  constructor
  · rintro ⟨q, ⟨hq, hkeep⟩, hqz⟩
    refine ⟨⟨q, hq, hqz⟩, ?_⟩
    obtain ⟨y, hy, hyeq⟩ := hkeep
    have hyz : y = z := p.measurableEmbedding_forgetAssigned.injective (hyeq.trans hqz)
    exact hyz ▸ hy
  · rintro ⟨⟨q, hq, hqz⟩, hz⟩
    refine ⟨q, ⟨hq, ?_⟩, hqz⟩
    change p.timeChange q ∈ p.forgetAssigned '' keep
    rw [hqz]
    exact mem_image_of_mem _ hz

theorem assignedSelectedEvent_diff_originalCut (p : FrozenPacket) (J : Set Incidence)
    (keep : Set (p.AssignedLine × ℝ)) :
    p.assignedSelectedEvent (J \ p.originalCut J keep) = p.assignedSelectedEvent J \ keep := by
  ext z
  constructor
  · rintro ⟨q, ⟨hq, hnot⟩, hqz⟩
    refine ⟨⟨q, hq, hqz⟩, ?_⟩
    intro hz
    apply hnot
    refine ⟨hq, ?_⟩
    change p.timeChange q ∈ p.forgetAssigned '' keep
    rw [hqz]
    exact mem_image_of_mem _ hz
  · rintro ⟨⟨q, hq, hqz⟩, hz⟩
    refine ⟨q, ⟨hq, ?_⟩, hqz⟩
    rintro ⟨-, y, hy, hyeq⟩
    have hyz : y = z := p.measurableEmbedding_forgetAssigned.injective (hyeq.trans hqz)
    exact hz (hyz ▸ hy)

theorem assignedSelectedLaw_originalCut (p : FrozenPacket) (ν : Measure Line)
    (J : Set Incidence) {keep : Set (p.AssignedLine × ℝ)} (hkeep : MeasurableSet keep) :
    p.assignedSelectedLaw ν (p.originalCut J keep) =
      (p.assignedSelectedLaw ν J).restrict keep := by
  unfold assignedSelectedLaw
  rw [p.assignedSelectedEvent_originalCut, Measure.restrict_restrict hkeep, inter_comm]

/-- Exact deletion accounting. The denominator is the unchanged full old
assignment times its original clock length. -/
theorem originalCut_loss (p : FrozenPacket) (ν : Measure Line) [IsFiniteMeasure ν]
    (hA : ν p.assigned ≠ 0) {J : Set Incidence} (hJ : MeasurableSet J)
    (hJF : J ⊆ p.counted) {keep : Set (p.AssignedLine × ℝ)} (hkeep : MeasurableSet keep) :
    (p.assignedSelectedLaw ν J) keepᶜ =
      (ENNReal.ofReal p.unitFrame.q * ν p.assigned)⁻¹ *
        (ν.prod volume) (J \ p.originalCut J keep) := by
  have hcut : MeasurableSet (p.originalCut J keep) := p.measurable_originalCut hJ hkeep
  have hdiff : MeasurableSet (J \ p.originalCut J keep) := hJ.diff hcut
  have hmass := (p.assignedSelectedLaw_mass ν hA hdiff).trans
    (p.selectedLaw_mass_original ν hA hdiff (fun z hz => hJF hz.1))
  rw [assignedSelectedLaw, Measure.restrict_apply_univ,
    p.assignedSelectedEvent_diff_originalCut] at hmass
  rw [assignedSelectedLaw, Measure.restrict_apply hkeep.compl]
  simpa only [diff_eq, inter_comm] using hmass

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.FrozenPacket
