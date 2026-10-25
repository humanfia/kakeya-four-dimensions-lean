-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.OriginalClockGridSource, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/OriginalClockGridSource.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 83ada3e49b5540f6b00606ae3df6268df68021ab,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/OriginalClockGridSource.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.OriginalClockSource
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ClockGridCoordinates
import Submission.Obl.k4_scalar_grid_cartesian_field.ActiveCodes

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Native
open Submission.Lib.K4ParentSignalPreparation.Census
open Submission.Obl.k4_scalar_grid_cartesian_field
open scoped ENNReal

noncomputable section

def splitClockCode (q : Fin 4 → ℤ) : (Fin 3 → ℤ) × ℤ := (Fin.init q,q (Fin.last 3))

theorem flatten_splitClockCode (q : Fin 4 → ℤ) : flattenClockCode (splitClockCode q)=q :=
  Fin.snoc_init_self q

theorem clockParentCode_fibre {W : ℕ} (p : PathData W) (old : Fin p.C)
    (P : Po) (mesh : ℝ) (q : Fin 4 → ℤ) :
    clockParentCode p old P mesh ⁻¹' {q}=
      (gridCode (fun z j => unshearedPacketBase p old z j)
        (clockParentSignal p old P) mesh mesh) ⁻¹' {splitClockCode q} := by
  ext z
  change clockParentCode p old P mesh z=q ↔ _=splitClockCode q
  rw [clockParentCode_eq_product]
  constructor
  · intro h
    apply flattenClockCode_injective
    simpa only [flatten_splitClockCode] using h
  · intro h
    rw [h,flatten_splitClockCode]

theorem clockParentCode_fibre_self {W : ℕ} (p : PathData W) (old : Fin p.C)
    (P : Po) (mesh : ℝ) (x : Ev) :
    clockParentCode p old P mesh ⁻¹' {clockParentCode p old P mesh x}=
      (gridCode (fun z j => unshearedPacketBase p old z j)
        (clockParentSignal p old P) mesh mesh) ⁻¹'
        {gridCode (fun z j => unshearedPacketBase p old z j)
          (clockParentSignal p old P) mesh mesh x} := by
  ext y
  change clockParentCode p old P mesh y=clockParentCode p old P mesh x ↔ _=_
  rw [clockParentCode_eq_product,clockParentCode_eq_product]
  exact flattenClockCode_injective.eq_iff

/-- The actual parent-clock preparation in the literal four-coordinate
code used by MK4. It supplies finite support and every nonzero-cell
floor from the census, while preserving earlier whole-cell mass and
every original fine-state band ratio. -/
theorem original_parent_clock_grid_source_of_census {W : ℕ}
    (N : ℝ) (p : PathData W) (old : Fin p.C) (P : Po)
    (ν : Measure Ln) (source : Set Ev) (hsource : MeasurableSet source)
    {ε K dimension ζ lossRate : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hK : 1 ≤ K)
    (hθK : δ N (p.r (p.lev old))/(((2:ℝ)^p.T (p.lev old))⁻¹) ≤ K)
    (hεζ : ε ≤ (δ N (p.r (p.lev old))/(((2:ℝ)^p.T (p.lev old))⁻¹))*ζ)
    (hεζplain : ε ≤ ζ) (hmargin : 2*K^(100:ℕ)*ζ ≤ 1)
    (hcensus : ∀ b w : ℝ, ε ≤ b → b ≤ 1 → ε ≤ w → w ≤ 1 →
      K^(100:ℕ)*b ≤ (δ N (p.r (p.lev old))/(((2:ℝ)^p.T (p.lev old))⁻¹))*w →
      (occupied source (fun z j => unshearedPacketBase p old z j)
        (physicalParentSignal N p old P) b w).Finite ∧
      ((occupied source (fun z j => unshearedPacketBase p old z j)
        (physicalParentSignal N p old P) b w).ncard:ℝ) ≤ K/(b^3*w^dimension))
    (hRate : 0 ≤ lossRate) :
    let θ := δ N (p.r (p.lev old))/(((2:ℝ)^p.T (p.lev old))⁻¹)
    let reference := ENNReal.ofReal (((2:ℝ)^p.T (p.lev old))⁻¹)*ν (p.A old)
    let raw := ν.prod (volume : Measure ℝ)
    ∃ (steps : ℕ) (current : Set Ev), K^(100:ℕ) ≤ (2:ℝ)^steps ∧
      (2:ℝ)^steps ≤ 2*K^(100:ℕ) ∧
      let mesh := ε*(2:ℝ)^steps
      let code := clockParentCode p old P mesh
      MeasurableSet current ∧ current⊆source ∧ ε ≤ mesh ∧ mesh ≤ 1 ∧ mesh ≤ θ ∧
      raw (source\current) ≤ ENNReal.ofReal (8*K^(301:ℕ)*lossRate)*reference ∧
      (activeCodes (raw.restrict current) code).Finite ∧
      (∀ q, (raw.restrict current) (code ⁻¹' {q})=0 ∨
        ENNReal.ofReal (lossRate*θ^(-dimension)*mesh^((3:ℝ)+dimension))*reference ≤ 
          (raw.restrict current) (code ⁻¹' {q})) ∧
      (∀ x∈current, (raw.restrict current) (code ⁻¹' {code x})=
        (raw.restrict source) (code ⁻¹' {code x})) ∧
      ∀ band : Set Ev, MeasurableSet band → ∀ η : ENNReal,
        (∀ i, (raw.restrict source)
          ((gridCode (fun z j => unshearedPacketBase p old z j)
            (physicalParentSignal N p old P) ε ε) ⁻¹' {i}∩band) ≤ 
          η*(raw.restrict source) ((gridCode (fun z j => unshearedPacketBase p old z j)
            (physicalParentSignal N p old P) ε ε) ⁻¹' {i})) →
        ∀ i, (raw.restrict current) (code ⁻¹' {i}∩band) ≤ 
          η*(raw.restrict current) (code ⁻¹' {i}) := by
  classical
  let θ := δ N (p.r (p.lev old))/(((2:ℝ)^p.T (p.lev old))⁻¹)
  let base := fun z j => unshearedPacketBase p old z j
  let X := physicalParentSignal N p old P
  let raw := ν.prod (volume : Measure ℝ)
  obtain ⟨steps,current,hlo,hhi,hcurrent,hsub,heps,hm1,hmθ,hloss,hpoint,hwhole,hratios⟩ :=
    original_parent_clock_floors_of_census N p old P ν source hsource hε hε1 hK hθK
      hεζ hεζplain hmargin hcensus hRate
  let mesh := ε*(2:ℝ)^steps
  let code := clockParentCode p old P mesh
  have hclock : (fun z => θ*X z)=clockParentSignal p old P := by
    funext z
    exact physicalParent_clock_relation N p old P z
  obtain ⟨S,hS,hcover⟩ := clock_isotropic_support_height_calibrated source base X hε hε1
    (by dsimp [θ,δ]; positivity) hK hθK hcensus steps hlo hmθ
  rw [hclock] at hcover
  let S₄ := S.image flattenClockCode
  have hfinite : (activeCodes (raw.restrict current) code).Finite := by
    apply (active_codes_finite_of_finite_support (raw.restrict current) code S₄ ?_).1
    filter_upwards [ae_restrict_mem hcurrent] with z hz
    change clockParentCode p old P mesh z∈S₄
    rw [clockParentCode_eq_product]
    exact Finset.mem_image_of_mem _ (hcover z (hsub hz))
  refine ⟨steps,current,hlo,hhi,hcurrent,hsub,heps,hm1,hmθ,hloss,hfinite,?_,?_,?_⟩
  · intro q
    by_cases hz : (raw.restrict current) (code ⁻¹' {q})=0
    · exact Or.inl hz
    · right
      have hcell : MeasurableSet (code ⁻¹' {q}) :=
        (measurable_clockParentCode p old P mesh) (measurableSet_singleton q)
      rw [Measure.restrict_apply hcell] at hz
      obtain ⟨x,hx⟩ := nonempty_of_measure_ne_zero hz
      have hh := hpoint x hx.2
      rw [←clockParentCode_fibre_self p old P mesh x] at hh
      have hqx : clockParentCode p old P mesh x=q := hx.1
      rw [hqx] at hh
      exact hh
  · intro x hx
    rw [clockParentCode_fibre_self]
    exact hwhole x hx
  · intro band hband η hη i
    rw [clockParentCode_fibre]
    exact hratios band hband η hη (splitClockCode i)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
