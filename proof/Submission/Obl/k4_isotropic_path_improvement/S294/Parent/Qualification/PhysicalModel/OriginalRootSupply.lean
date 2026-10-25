-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.OriginalRootSupply, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.OriginalRootCosts

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel

open Set MeasureTheory
open Submission.Lib.K4ParentSignalPreparation.Census
open Submission.Lib.K4ContinuousKakeya
open Submission.Lib.K4ThreeBaseRows
open Submission.Lib.K4ThreeBaseRows.RowBinLists (rowEval vbin)
open Submission.Lib.K4CommonLocalChoice (cell)
open WangZahlLot.Obl.wz_slab_local_linearity
open scoped ENNReal BigOperators RealInnerProductSpace

noncomputable section

/-- A constructed primitive input and its proved scalar interface.
The interface prevents consumers from unfolding a large native model. -/
structure RootPreparationSupply (p : PhysicalModel) (ν : Measure Ln)
    [IsProbabilityMeasure (p.prior ν)] (μ : Measure Ev) [IsFiniteMeasure μ]
    (E : Set Ev) (G : (Fin 4 → ℤ) → Fin 3 → ℝ)
    (nativeRow : Ev → Fin 3 → ℝ) {Label : Type} [MeasurableSpace Label] (lab : Ev → Label)
    (scales : OriginalRootScales) where
  input : RootPreparationInput p ν μ E G nativeRow lab
  b_eq : input.b=scales.b
  Lp_eq : input.Lp=scales.Lp
  rho_eq : input.ρ=scales.ρ
  M_eq : input.incidence.M=scales.incidence.M
  T_eq : input.T=scales.T
  mesh_eq : input.mesh=scales.mesh
  bound_eq : input.bound=scales.bound
  err_eq : input.err=scales.err
  duration_eq : input.duration=scales.duration
  factor_eq : input.regularityFactor=scales.regularityFactor
  loss_eq : input.supportLoss=scales.supportLoss
  native_le : input.incidence.nativeFailureBound ≤ scales.nativeFailureBound

section Congr

variable {p : PhysicalModel} {ν : Measure Ln} [IsProbabilityMeasure (p.prior ν)]
    {μ μ' : Measure Ev} [IsFiniteMeasure μ] [IsFiniteMeasure μ']
    {E : Set Ev} {G : (Fin 4 → ℤ) → Fin 3 → ℝ} {nativeRow : Ev → Fin 3 → ℝ}
    {Label : Type} [MeasurableSpace Label] {lab : Ev → Label} {scales : OriginalRootScales}

/-- Preserve the constructed scalar interface under the exact native
selected-law/original-restriction identity. -/
def RootPreparationSupply.measure_congr
    (data : RootPreparationSupply p ν μ E G nativeRow lab scales) (h : μ'=μ) :
    RootPreparationSupply p ν μ' E G nativeRow lab scales := by
  subst μ'
  exact data

end Congr

def rootPreparationSupply_of_original_data (p : PhysicalModel) (ν : Measure Ln)
    [IsProbabilityMeasure (p.prior ν)]
    (scales : OriginalRootScales) (hκ : 1 ≤ p.slack)
    (E : Set Ev) (hE : MeasurableSet E) (hEp : E⊆p.event)
    (hcoeff : ∀ l, ∀ j, |p.scalarCoefficients l j| ≤ scales.H)
    (G : (Fin 4 → ℤ) → Fin 3 → ℝ)
    (hG : ∀ z∈E, ∀ j, |G (p.physicalState scales.b z) j| ≤ scales.B)
    (hgraph : ∀ z∈E, |(p.signal z.1).derivative.eval z.2-
      ∑ j, G (p.physicalState scales.b z) j*p.velocity z.1 j| ≤ scales.error)
    (palette : Measure (Fin 2 → ℝ))
    (floors : Jets2.OriginalDyadicFloorData (p.prior ν) p.scalarCoefficients E palette scales.dimension
      scales.floorExponent scales.floorStart scales.floorCount)
    (tables : Jets2.OriginalDerivativeListData p.scalarCoefficients E
      (fun i : Fin scales.regLength => scales.regLevel i.val) (fun _ => scales.KL))
    (hvelocity : ∀ᵐ z ∂((p.prior ν).prod volume).restrict E, ‖p.planarVelocityVector z.1‖ ≤ scales.Uvelocity)
    (hstrip : ∀ q (normal : EuclideanSpace ℝ (Fin 2)) offset, ‖normal‖=1 →
      (((p.prior ν).prod volume).restrict E) {z | p.physicalState scales.b z=q ∧
        |inner ℝ normal (p.planarVelocityVector z.1)-offset| ≤ scales.stripWidth} ≤
      ENNReal.ofReal scales.failure*(((p.prior ν).prod volume).restrict E)
        ((p.physicalState scales.b) ⁻¹' {q}))
    (hstate : ∀ query : ℕ, query ≤ scales.paletteFinest → ∀ q (D : Set (Fin 2 → ℤ)), MeasurableSet D →
      (((p.prior ν).prod volume).restrict E) {z | p.physicalState scales.b z=q ∧
        Jets2.parameterCode (Jets2.dyadicParameterWidth query) (Jets2.zv (p.scalarCoefficients z.1))∈D} ≤
      ENNReal.ofReal scales.incidence.Cstate*(((p.prior ν).prod volume).restrict E)
        ((p.physicalState scales.b) ⁻¹' {q})*
          (palette.map (Jets2.parameterCode (Jets2.dyadicParameterWidth query))) D)
    (hpure : ∀ query : ℕ, query ≤ scales.paletteFinest → ∀ w : ℝ, scales.resolution ≤ w → w ≤ 1 →
      ∀ (base : Fin 3 → ℤ) (hidden : ℤ) (vcode : Fin 2 → ℤ),
      (((p.prior ν).prod volume).restrict E) {z | Jets2.originalBaseCode p.scalarCoefficients scales.resolution z=base ∧
        ⌊Jets2.zx (p.scalarCoefficients z.1) z.2/w⌋=hidden ∧
        Jets2.parameterCode (Jets2.dyadicParameterWidth query) (Jets2.zv (p.scalarCoefficients z.1))=vcode} ≤
      ENNReal.ofReal (scales.Cpure*scales.resolution^3*w^scales.dimension)*
        (palette.map (Jets2.parameterCode (Jets2.dyadicParameterWidth query))) {vcode})
    (hcensus : ∀ a w : ℝ, scales.resolution ≤ a → a ≤ 1 → scales.resolution ≤ w → w ≤ 1 →
      scales.Kcensus^(100:ℕ)*a ≤ w →
      (occupied E (fun z j => p.originalBase z j) (fun z => p.originalPoint z 3) a w).Finite ∧
      ((occupied E (fun z j => p.originalBase z j) (fun z => p.originalPoint z 3) a w).ncard:ℝ) ≤
        scales.Kcensus/(a^3*w^scales.dimension))
    (hband : ∀ R : ℝ, scales.resolution ≤ R → R ≤ 8*scales.ρ →
      ∀ U : Set P3, MeasurableSet U → ∀ center : P3 → ℝ, Measurable center →
      (((p.prior ν).prod volume).restrict E)
        {z | p.originalBase z∈U ∧ |p.originalPoint z 3-center (p.originalBase z)| ≤ R} ≤
        ENNReal.ofReal (scales.Cband*R^scales.dimension)*volume U)
    (nativeRow : Ev → Fin 3 → ℝ) (hNativeRow : Measurable nativeRow)
    (hNativeRowEq : ∀ z∈E, nativeRow z=G (p.physicalState scales.b z))
    {Label : Type} [MeasurableSpace Label] (lab : Ev → Label) (hlab : Measurable lab)
    (hdiag : MeasurableSet {q : Label × Label | q.1=q.2})
    (hlabel : ∀ z∈E, ∀ v, (z.1,v)∈E → v∈Jets2.dyadicBlock scales.T z.2 → lab (z.1,v)=lab z) :
    let μ := (((p.prior ν).prod volume).restrict E)
    letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr
      (Graph.prod_unit_finite (p.prior ν) (fun z hz => ⟨mem_univ _,p.event_time z (hEp hz)⟩)).ne
    RootPreparationSupply p ν μ E G nativeRow lab scales := by
  let μ := (((p.prior ν).prod volume).restrict E)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr
    (Graph.prod_unit_finite (p.prior ν) (fun z hz => ⟨mem_univ _,p.event_time z (hEp hz)⟩)).ne
  let input := rootPreparationInput_of_original_data p ν scales hκ E hE hEp hcoeff G hG hgraph
    palette floors tables hvelocity hstrip hstate hpure hcensus hband nativeRow hNativeRow hNativeRowEq lab hlab hdiag hlabel
  refine ⟨input,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  exact input.incidence.nativeFailureBound_le_unitMass
    (original_current_mass_le_one p ν E hEp) (by simp)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel
