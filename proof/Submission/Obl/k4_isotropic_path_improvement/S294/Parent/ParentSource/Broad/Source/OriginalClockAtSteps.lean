-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.OriginalClockAtSteps, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/OriginalClockAtSteps.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1046 (branch x0943), commit 1fcc75a78b90aa1b479052c83612b68563af73b6,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/OriginalClockAtSteps.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.CalibratedClockAtSteps
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.OriginalClockGridSource

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Native
open Submission.Lib.K4ParentSignalPreparation.Census
open Submission.Obl.k4_scalar_grid_cartesian_field
open scoped ENNReal

noncomputable section

/-- Prepare actual original clock cells at a prescribed coarsening.
Choosing the physical precision from a preselected MK4 mesh gives exact
dyadic nesting without changing any source reference or prior. -/
theorem original_parent_clock_grid_source_at_steps {W : ℕ}
    (N : ℝ) (p : PathData W) (old : Fin p.C) (P : Po)
    (ν : Measure Ln) (source : Set Ev) (hsource : MeasurableSet source)
    {ε K dimension lossRate : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hK : 1 ≤ K)
    (hθK : δ N (p.r (p.lev old))/(((2:ℝ)^p.T (p.lev old))⁻¹) ≤ K)
    (hcensus : ∀ b w : ℝ, ε ≤ b → b ≤ 1 → ε ≤ w → w ≤ 1 →
      K^(100:ℕ)*b ≤ (δ N (p.r (p.lev old))/(((2:ℝ)^p.T (p.lev old))⁻¹))*w →
      (occupied source (fun z j => unshearedPacketBase p old z j)
        (physicalParentSignal N p old P) b w).Finite ∧
      ((occupied source (fun z j => unshearedPacketBase p old z j)
        (physicalParentSignal N p old P) b w).ncard:ℝ) ≤ K/(b^3*w^dimension))
    (steps : ℕ) (hsteps : K^(100:ℕ) ≤ (2:ℝ)^steps)
    (hresolved : ε*(2:ℝ)^steps ≤ δ N (p.r (p.lev old))/(((2:ℝ)^p.T (p.lev old))⁻¹))
    (hRate : 0 ≤ lossRate) :
    let θ := δ N (p.r (p.lev old))/(((2:ℝ)^p.T (p.lev old))⁻¹)
    let reference := ENNReal.ofReal (((2:ℝ)^p.T (p.lev old))⁻¹)*ν (p.A old)
    let raw := ν.prod (volume : Measure ℝ)
    let mesh := ε*(2:ℝ)^steps
    let code := clockParentCode p old P mesh
    ∃ current : Set Ev, MeasurableSet current ∧ current⊆source ∧
      raw (source\current) ≤ ENNReal.ofReal ((K*((2:ℝ)^steps)^3)*lossRate)*reference ∧
      (activeCodes (raw.restrict current) code).Finite ∧
      (∀ q, (raw.restrict current) (code ⁻¹' {q})=0 ∨
        ENNReal.ofReal (lossRate*θ^(-dimension)*mesh^((3:ℝ)+dimension))*reference ≤
          (raw.restrict current) (code ⁻¹' {q})) ∧
      ∀ x∈current, (raw.restrict current) (code ⁻¹' {code x})=
        (raw.restrict source) (code ⁻¹' {code x}) := by
  classical
  let θ := δ N (p.r (p.lev old))/(((2:ℝ)^p.T (p.lev old))⁻¹)
  let raw := ν.prod (volume : Measure ℝ)
  let μ := raw.restrict source
  let base := fun z j => unshearedPacketBase p old z j
  let X := physicalParentSignal N p old P
  have hbase : Measurable base := by
    apply measurable_pi_iff.mpr
    intro j
    exact (PiLp.continuous_apply 2 _ j).measurable.comp (measurable_unshearedPacketBase p old)
  have hclock : (fun z => θ*X z)=clockParentSignal p old P := by
    funext z
    exact physicalParent_clock_relation N p old P z
  obtain ⟨S,keep,hcover,hkeep,hloss,hfloor,hpoint,hsaturated⟩ :=
    ClockCalibration.pointwise_floors_at_steps μ source (ae_restrict_mem hsource)
      base hbase X (measurable_physicalParentSignal _ _ _ _)
      hε hε1 (by dsimp [θ,δ]; positivity) hK hθK hcensus steps hsteps hresolved hRate
      (ENNReal.ofReal (((2:ℝ)^p.T (p.lev old))⁻¹)*ν (p.A old))
  rw [hclock] at hcover hfloor hpoint hsaturated
  let mesh := ε*(2:ℝ)^steps
  let code := clockParentCode p old P mesh
  let current := source∩keep
  have hcurrent : MeasurableSet current := hsource.inter hkeep
  have hlaw : μ.restrict keep=raw.restrict current := by
    rw [Measure.restrict_restrict hkeep,inter_comm]
  let S₄ := S.image flattenClockCode
  have hfinite : (activeCodes (raw.restrict current) code).Finite := by
    apply (active_codes_finite_of_finite_support (raw.restrict current) code S₄ ?_).1
    filter_upwards [ae_restrict_mem hcurrent] with z hz
    change clockParentCode p old P mesh z∈S₄
    rw [clockParentCode_eq_product]
    exact Finset.mem_image_of_mem _ (hcover z hz.1)
  refine ⟨current,hcurrent,inter_subset_left,?_,hfinite,?_,?_⟩
  · have heq : source\current=keepᶜ∩source := by
      ext z
      simp only [current,mem_diff,mem_inter_iff,mem_compl_iff]
      tauto
    rw [heq]
    simpa only [μ,Measure.restrict_apply hkeep.compl] using hloss
  · intro q
    rw [clockParentCode_fibre]
    have hh := hfloor (splitClockCode q)
    rwa [hlaw] at hh
  · intro x hx
    rw [←hlaw]
    change (μ.restrict keep) (code ⁻¹' {code x})=μ (code ⁻¹' {code x})
    rw [Measure.restrict_apply ((measurable_clockParentCode p old P mesh) (measurableSet_singleton _))]
    congr 1
    apply inter_eq_left.mpr
    intro y hy
    have hxy : code y=code x := hy
    dsimp only [code] at hxy
    rw [clockParentCode_eq_product,clockParentCode_eq_product] at hxy
    exact (hsaturated y x (flattenClockCode_injective hxy)).mpr hx.2

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
