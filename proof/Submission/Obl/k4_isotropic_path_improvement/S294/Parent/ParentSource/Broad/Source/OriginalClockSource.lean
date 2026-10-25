-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.OriginalClockSource, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/OriginalClockSource.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit c1f30c34,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/OriginalClockSource.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.CalibratedClockBreadth
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ParentClockState

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Native
open Submission.Lib.K4ParentSignalPreparation.Census
open scoped ENNReal

noncomputable section

/-- Apply calibrated whole-cell preparation to the literal original
parent signal. The retained set is an original event set, and every
surviving cell keeps its entire earlier original-source law. -/
theorem original_parent_clock_floors_of_census {W : ℕ}
    (N : ℝ) (p : PathData W) (old : Fin p.C) (P : MvPolynomial (Fin 4) ℝ)
    (ν : Measure Ln) (source : Set Ev) (hsource : MeasurableSet source)
    {ε K d ζ lossRate : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hK : 1 ≤ K)
    (hθK : δ N (p.r (p.lev old))/(((2:ℝ)^p.T (p.lev old))⁻¹) ≤ K)
    (hεζ : ε ≤ (δ N (p.r (p.lev old))/(((2:ℝ)^p.T (p.lev old))⁻¹))*ζ)
    (hεζplain : ε ≤ ζ) (hmargin : 2*K^(100:ℕ)*ζ ≤ 1)
    (hcensus : ∀ b w : ℝ, ε ≤ b → b ≤ 1 → ε ≤ w → w ≤ 1 →
      K^(100:ℕ)*b ≤ (δ N (p.r (p.lev old))/(((2:ℝ)^p.T (p.lev old))⁻¹))*w →
      (occupied source (fun z j => unshearedPacketBase p old z j)
        (physicalParentSignal N p old P) b w).Finite ∧
      ((occupied source (fun z j => unshearedPacketBase p old z j)
        (physicalParentSignal N p old P) b w).ncard : ℝ) ≤ K/(b^3*w^d))
    (hRate : 0 ≤ lossRate) :
    let θ := δ N (p.r (p.lev old))/(((2:ℝ)^p.T (p.lev old))⁻¹)
    let reference := ENNReal.ofReal (((2:ℝ)^p.T (p.lev old))⁻¹)*ν (p.A old)
    let raw := ν.prod (volume : Measure ℝ)
    let base := fun z j => unshearedPacketBase p old z j
    ∃ (steps : ℕ) (current : Set Ev), K^(100:ℕ) ≤ (2:ℝ)^steps ∧
      (2:ℝ)^steps ≤ 2*K^(100:ℕ) ∧
      let mesh := ε*(2:ℝ)^steps
      let code := gridCode base (clockParentSignal p old P) mesh mesh
      MeasurableSet current ∧ current⊆source ∧ ε ≤ mesh ∧ mesh ≤ 1 ∧ mesh ≤ θ ∧
      raw (source\current) ≤ ENNReal.ofReal (8*K^(301:ℕ)*lossRate)*reference ∧
      (∀ x∈current,
        ENNReal.ofReal (lossRate*θ^(-d)*mesh^((3:ℝ)+d))*reference ≤
          (raw.restrict current) (code ⁻¹' {code x})) ∧
      (∀ x∈current, (raw.restrict current) (code ⁻¹' {code x})=
        (raw.restrict source) (code ⁻¹' {code x})) ∧
      ∀ band : Set Ev, MeasurableSet band → ∀ η : ENNReal,
        (∀ i, (raw.restrict source)
          ((gridCode base (physicalParentSignal N p old P) ε ε) ⁻¹' {i}∩band) ≤
            η*(raw.restrict source) ((gridCode base (physicalParentSignal N p old P) ε ε) ⁻¹' {i})) →
        ∀ i, (raw.restrict current) (code ⁻¹' {i}∩band) ≤
          η*(raw.restrict current) (code ⁻¹' {i}) := by
  let θ := δ N (p.r (p.lev old))/(((2:ℝ)^p.T (p.lev old))⁻¹)
  let reference := ENNReal.ofReal (((2:ℝ)^p.T (p.lev old))⁻¹)*ν (p.A old)
  let raw := ν.prod (volume : Measure ℝ)
  let μ := raw.restrict source
  let base := fun z j => unshearedPacketBase p old z j
  let X := physicalParentSignal N p old P
  have hθ : 0 < θ := by dsimp [θ,δ]; positivity
  have hbase : Measurable base := by
    apply measurable_pi_iff.mpr
    intro j
    exact (PiLp.continuous_apply 2 _ j).measurable.comp (measurable_unshearedPacketBase p old)
  have hclock : (fun z => θ*X z)=clockParentSignal p old P := by
    funext z
    exact physicalParent_clock_relation N p old P z
  obtain ⟨steps,keep,hlo,hhi,hkeep,heps,hm1,hmθ,hloss,hpoint,hsaturated,hratios⟩ :=
    ClockCalibration.floors_with_state_ratios μ source (ae_restrict_mem hsource)
      base hbase X (measurable_physicalParentSignal N p old P) hε hε1 hθ hK hθK
      hεζ hεζplain hmargin hcensus _ (parent_height_clock_ratio_zpow N p old) hRate reference
  rw [hclock] at hpoint hsaturated hratios
  let mesh := ε*(2:ℝ)^steps
  let code := gridCode base (clockParentSignal p old P) mesh mesh
  let current := source∩keep
  have hcurrent : MeasurableSet current := hsource.inter hkeep
  have hlaw : μ.restrict keep=raw.restrict current := by
    rw [Measure.restrict_restrict hkeep,inter_comm]
  have hcode : Measurable code := ClockCalibration.measurable_product_gridCode base hbase
    _ (measurable_clockParentSignal N p old P) mesh mesh
  refine ⟨steps,current,hlo,hhi,hcurrent,inter_subset_left,heps,hm1,hmθ,?_,?_,?_,?_⟩
  · have heq : source\current=keepᶜ∩source := by
      ext x
      simp only [current,mem_diff,mem_inter_iff,mem_compl_iff]
      tauto
    rw [heq]
    simpa only [μ,Measure.restrict_apply hkeep.compl] using hloss
  · intro x hx
    rw [←hlaw]
    exact hpoint x hx.2
  · intro x hx
    rw [←hlaw,Measure.restrict_apply (hcode (measurableSet_singleton _))]
    congr 1
    apply inter_eq_left.mpr
    intro y hy
    exact (hsaturated y x hy).mpr hx.2
  · intro band hband η hη i
    rw [←hlaw]
    exact hratios band hband η hη i

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
