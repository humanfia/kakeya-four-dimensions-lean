-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PreparedParameterSnapshots, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/PreparedParameterSnapshots.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalEntrySnapshots
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalParameterEntryPruning

/-! # Original time-fiber caps from one current entry cut

Every tested parameter scale uses the same selected incidence set and
the same full original trajectory prior. Current canonical incidence
caps, rather than full-prior snapshot assumptions, suffice.
-/
set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
open Set MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

/-- One original entry cut transfers all queried current cell ceilings to
original fixed-time ceilings. The ceiling may test any union of full
original coefficient atoms. There is no atom-counting or inverse-scale
cost in a snapshot cap. -/
theorem prepare_original_parameter_snapshots {Λ σ : Type*}
    [MeasurableSpace Λ] [Fintype σ]
    (μ : Measure (Λ × ℝ)) (ν : Measure Λ)
    (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
    (E : Set (Λ × ℝ)) (hE : MeasurableSet E)
    (ht : ∀ z∈E, z.2∈Icc (0 : ℝ) 1)
    (ρ s cut : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (hs : ∀ i, 0 < s i) (hs1 : ∀ i, s i ≤ 1) (hcut : ∀ i, 0 < cut i)
    (hfinite : ∀ i, ((fun z : Λ × ℝ => originalZoomBlock c (ρ i) (s i) z.1) '' E).Finite) :
    ∃ R : Set (Λ × ℝ), MeasurableSet R ∧ R ⊆ E ∧
      μ (E \ R) ≤ (∑ i, ENNReal.ofReal (cut i * zoomBlockVisitConstant)) * ν univ ∧
      ∀ i (t : ℝ) (q : Fin 4 → ℤ)
        (D : Set ((Fin 7 → ℤ) × (Fin 7 → ℤ))) (C amplitude : ℝ) (weight : ℝ≥0∞),
        (μ.restrict E) {z | canonicalZoomCell c (ρ i) (s i) z=q ∧
          originalZoomBlock c (ρ i) (s i) z.1∈D} ≤
            ENNReal.ofReal (C*s i*amplitude)*weight →
        ν {l | (l,t)∈R ∧ canonicalZoomCell c (ρ i) (s i) (l,t)=q ∧
          originalZoomBlock c (ρ i) (s i) l∈D} ≤
            ENNReal.ofReal (C*amplitude/cut i)*weight := by
  obtain ⟨R,hR,hsub,hloss,hfloor⟩ := prepare_original_parameter_cell_entries
    μ ν c hc E hE ht ρ s cut hρ hs hs1 (fun i => (hcut i).le) hfinite
  refine ⟨R,hR,hsub,hloss,?_⟩
  intro i t q D C amplitude weight hcap
  have hblock : Measurable (originalZoomBlock c (ρ i) (s i)) :=
    (((measurable_parameterCode (ρ i)).comp hc).prodMk
      ((measurable_parameterCode (ρ i*s i)).comp hc))
  have hcell := measurable_canonicalZoomCell hc (ρ i) (s i)
  refine original_cell_snapshot_cap ν (μ.restrict R)
    (originalZoomBlock c (ρ i) (s i)) hblock
    (canonicalZoomCell c (ρ i) (s i)) hcell R (hcut i) (hs i) ?_
    t q D weight ?_
  · intro z hz
    have hentry : MeasurableSet {y : Λ×ℝ |
        originalZoomBlock c (ρ i) (s i) y.1=originalZoomBlock c (ρ i) (s i) z.1 ∧
        canonicalZoomCell c (ρ i) (s i) y=canonicalZoomCell c (ρ i) (s i) z} :=
      ((hblock.comp measurable_fst) (measurableSet_singleton _)).inter
        (hcell (measurableSet_singleton _))
    rw [Measure.restrict_apply hentry,inter_comm]
    exact (hfloor i z hz).le
  · exact ((Measure.restrict_mono_set μ hsub) _).trans hcap


/-- One original entry cut transfers every union of queried entries to
its original time fiber. Neither code counts nor current posteriors
enter the original prior on the left. -/
theorem prepare_original_parameter_snapshot_unions {Λ σ : Type*}
    [MeasurableSpace Λ] [Fintype σ]
    (μ : Measure (Λ × ℝ)) (ν : Measure Λ)
    (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
    (E : Set (Λ × ℝ)) (hE : MeasurableSet E)
    (ht : ∀ z∈E, z.2∈Icc (0 : ℝ) 1)
    (ρ s cut : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (hs : ∀ i, 0 < s i) (hs1 : ∀ i, s i ≤ 1) (hcut : ∀ i, 0 ≤ cut i)
    (hfinite : ∀ i, ((fun z : Λ × ℝ => originalZoomBlock c (ρ i) (s i) z.1) '' E).Finite) :
    ∃ R : Set (Λ × ℝ), MeasurableSet R ∧ R ⊆ E ∧
      μ (E \ R) ≤ (∑ i, ENNReal.ofReal (cut i * zoomBlockVisitConstant)) * ν univ ∧
      ∀ i (t : ℝ)
        (D : Set (((Fin 7 → ℤ) × (Fin 7 → ℤ)) × (Fin 4 → ℤ))),
        ENNReal.ofReal (cut i*s i)*ν {l | (l,t)∈R ∧
          (originalZoomBlock c (ρ i) (s i) l,canonicalZoomCell c (ρ i) (s i) (l,t))∈D} ≤
        μ (R ∩ {z | (originalZoomBlock c (ρ i) (s i) z.1,
          canonicalZoomCell c (ρ i) (s i) z)∈D}) := by
  obtain ⟨R,hR,hsub,hloss,hfloor⟩ := prepare_original_parameter_cell_entries
    μ ν c hc E hE ht ρ s cut hρ hs hs1 hcut hfinite
  refine ⟨R,hR,hsub,hloss,?_⟩
  intro i t D
  have hblock : Measurable (originalZoomBlock c (ρ i) (s i)) :=
    (((measurable_parameterCode (ρ i)).comp hc).prodMk
      ((measurable_parameterCode (ρ i*s i)).comp hc))
  have hcell := measurable_canonicalZoomCell hc (ρ i) (s i)
  have h := original_union_snapshot_of_entry_floors ν (μ.restrict R)
    (originalZoomBlock c (ρ i) (s i)) hblock
    (canonicalZoomCell c (ρ i) (s i)) hcell R (ENNReal.ofReal (cut i*s i)) ?_ t D
  · have htest : MeasurableSet {z : Λ×ℝ |
        (originalZoomBlock c (ρ i) (s i) z.1,canonicalZoomCell c (ρ i) (s i) z)∈D} :=
      ((hblock.comp measurable_fst).prodMk hcell) (to_countable D).measurableSet
    rw [Measure.restrict_apply htest,inter_comm] at h
    exact h
  · intro z hz
    have hentry : MeasurableSet {y : Λ×ℝ |
        originalZoomBlock c (ρ i) (s i) y.1=originalZoomBlock c (ρ i) (s i) z.1 ∧
        canonicalZoomCell c (ρ i) (s i) y=canonicalZoomCell c (ρ i) (s i) z} :=
      ((hblock.comp measurable_fst) (measurableSet_singleton _)).inter
        (hcell (measurableSet_singleton _))
    rw [Measure.restrict_apply hentry,inter_comm]
    exact (hfloor i z hz).le

end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
