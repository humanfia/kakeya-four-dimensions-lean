-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.OriginalRootCosts, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.OriginalRootFromData
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalIncidenceCostBounds

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel

open Set MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

/-- The exact physical retention cost, depending only on fixed scale data. -/
def OriginalRootScales.regularityFactor (s : OriginalRootScales) : ENNReal :=
  ∏ i∈Finset.range s.regLength, ((4:ENNReal)^4*((7:ℕ)^4*⌊10^10*s.Areg^27*((1:ℝ)^3+1)⌋₊))

/-- The exact support deletion allowance, in full original root units. -/
def OriginalRootScales.supportLoss (s : OriginalRootScales) : ENNReal :=
  ENNReal.ofReal ((300*7^8*s.H)*(s.W.card:ℝ)/s.Hprior)+
    ENNReal.ofReal ((s.Kcensus*((2:ℝ)^s.steps)^3)*((s.W.card:ℝ)*s.rate))

/-- The canonical pure-cell coefficient constructed by the input factory. -/
def OriginalRootScales.canonicalConstant (s : OriginalRootScales) : ℝ :=
  151200*(12*s.H+3)*s.Cpure*(3:ℝ)^s.dimension

/-- The fixed-length analytic residual choice cost. -/
def OriginalRootScales.residualSelectionFactor (s : OriginalRootScales) : ENNReal :=
  ∏ i∈Finset.range s.incidence.L,
    ((4:ENNReal)^4*(⌈3*((s.canonicalConstant*s.Kcap/s.incidence.entryCut i)*(22*s.Krow^2+5))*
      (s.incidence.Cstate/s.incidence.cut i)⌉₊+1:ℕ))

/-- The source-independent residual entry allowance. -/
def OriginalRootScales.residualEntryLoss (s : OriginalRootScales) : ENNReal :=
  (∑ i : Fin s.incidence.L, ENNReal.ofReal (s.incidence.cut i.val)*
    (⌈256*(12*s.H+4)^7*(s.canonicalConstant*s.Kcap/s.incidence.entryCut0)⌉₊*256:ℕ))+
  (ENNReal.ofReal (s.incidence.entryCut0*Jets2.zoomBlockVisitConstant)+
    ∑ i : Fin s.incidence.L, ENNReal.ofReal (s.incidence.entryCut i.val*Jets2.zoomBlockVisitConstant))

/-- The entire native error allowance uses only scale data; it is
uniform in roots, sources, current masses, priors and external palettes. -/
def OriginalRootScales.nativeFailureBound (s : OriginalRootScales) : ENNReal :=
  ((Jets2.parameterLevel s.zeta+1:ℕ):ENNReal)*ENNReal.ofReal (s.incidence.nativeCut*Jets2.zoomBlockVisitConstant)+
    s.residualSelectionFactor*ENNReal.ofReal (2*s.incidence.N^(-(s.incidence.ch*s.incidence.alpha)))+
      s.residualEntryLoss

/-- Every selected original unit-clock source has mass at most one. -/
theorem original_current_mass_le_one (p : PhysicalModel) (ν : Measure Ln)
    [IsProbabilityMeasure (p.prior ν)] (E : Set Ev) (hEp : E⊆p.event) :
    (((p.prior ν).prod volume).restrict E) univ ≤ 1 := by
  rw [Measure.restrict_apply_univ]
  calc
    _ ≤ ((p.prior ν).prod volume) (univ ×ˢ Icc (0:ℝ) 1) :=
      measure_mono (fun z hz => ⟨mem_univ _,p.event_time z (hEp hz)⟩)
    _ = 1 := by rw [Measure.prod_prod,measure_univ,Real.volume_Icc]; norm_num

section MeasureCongr

variable {p : PhysicalModel} {ν : Measure Ln} [IsProbabilityMeasure (p.prior ν)]
    {μ μ' : Measure Ev} [IsFiniteMeasure μ] [IsFiniteMeasure μ']
    {E : Set Ev} {G : (Fin 4 → ℤ) → Fin 3 → ℝ} {nativeRow : Ev → Fin 3 → ℝ}
    {Label : Type} [MeasurableSpace Label] {lab : Ev → Label}
    (input : RootPreparationInput p ν μ E G nativeRow lab)

/-- Change only the expression for the same current original measure. -/
def RootPreparationInput.measure_congr (h : μ'=μ) : RootPreparationInput p ν μ' E G nativeRow lab := by
  subst μ'
  exact input

/-- Current-measure transport preserves every displayed output scalar
and the exact original mass allowances. -/
theorem RootPreparationInput.measure_congr_values (h : μ'=μ) :
    let out := input.measure_congr h
    out.b=input.b ∧ out.Lp=input.Lp ∧ out.ρ=input.ρ ∧ out.incidence.M=input.incidence.M ∧
      out.T=input.T ∧ out.mesh=input.mesh ∧ out.bound=input.bound ∧ out.err=input.err ∧
      out.duration=input.duration ∧ out.regularityFactor=input.regularityFactor ∧
      out.supportLoss=input.supportLoss ∧ out.incidence.nativeFailureBound=input.incidence.nativeFailureBound := by
  subst μ'
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end MeasureCongr

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel
