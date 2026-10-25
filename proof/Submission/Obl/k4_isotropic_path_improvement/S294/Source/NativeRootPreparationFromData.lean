-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.NativeRootPreparationFromData, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeRootSupplyFromData
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.PostStateAssembly
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.NativeRootSupplyPreparation

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32768

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Set MeasureTheory
open Parent.ParentSource
open Parent.ParentSource.Native (ProblemData PathData)
open Parent.Qualification
open Parent.Qualification.PhysicalModel
open Parent.Qualification.PhysicalModel.NativeAncestor
open Submission.Lib.K4ParentSignalPreparation.Census
open scoped ENNReal BigOperators RealInnerProductSpace

noncomputable section

local instance nativePreparedRootOptionMeasurableSpace (C : ℕ) : MeasurableSpace (Option (Fin C)) := ⊤
local instance nativePreparedRootOptionMeasurableSingletonClass (C : ℕ) : MeasurableSingletonClass (Option (Fin C)) := ⟨fun _ => trivial⟩

/-- Closed original ancestor preparation from actual P1/P5 data.
The scalar costs are uniform in roots, priors, palettes and current
source masses. The reference is formed from the final whole-code cut. -/
theorem prepare_native_root_from_original_data
    {d : ProblemData} (hd : d.Valid) {k m : ℕ} {p : PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (root : Fin p.C) {Vmax : ℝ} (hVmax : 0 ≤ Vmax)
    (source : Set Ev) (hsource : MeasurableSet source) (hsourceF : source⊆p.F root)
    (hR : (p.R root).totalDegree ≤ 2) (hvelocity : ∀ z∈source, ‖Parent.v z.1‖ ≤ Vmax)
    (S : Set Ev) (hS : MeasurableSet S) (hSsource : S⊆source)
    (scales : OriginalRootScales)
    (hcoeffH : coefficientBound (p:=p) Vmax ≤ scales.H) (hVmaxU : Vmax ≤ scales.Uvelocity)
    (row : (Fin 4 → ℤ) → Fin 3 → ℝ) (hrow : ∀ cd j, |row cd j| ≤ scales.B)
    (hfit : ∀ x∈S,
      |((((2:ℝ)^p.T (p.lev root))⁻¹)/δ (d.N k) (p.r (p.lev root)))*
        Submission.Lib.K4GlobalParentSignal.rate (p.R root) x.1 x.2-
          ∑ j, row (clockParentCode p root (Parent.SignalGraph.ancestorSignal (d.N k) p root) scales.b x) j*
            (![1,Parent.v x.1 0,Parent.v x.1 1] : Fin 3 → ℝ) j| ≤ scales.error)
    (palette : Measure (Fin 2 → ℝ))
    (floors : Jets2.OriginalDyadicFloorData ((hp.frozenPacket root).prior (d.ν k (p.γ root)))
      (coefficientTable (d.N k) p root Vmax) ((hp.frozenPacket root).selectedEvent S)
        palette scales.dimension scales.floorExponent scales.floorStart scales.floorCount)
    (tables : Jets2.OriginalDerivativeListData (coefficientTable (d.N k) p root Vmax)
      ((hp.frozenPacket root).selectedEvent S)
      (fun i : Fin scales.regLength => scales.regLevel i.val) (fun _ => scales.KL))
    (pairPalette : Measure (ℤ×ℤ)) (finePv recordRadius : ℝ) (stripCoeff paletteCoeff : ENNReal)
    (ratios : GraphRecordRatios p (d.N k) root scales.b finePv recordRadius scales.stripWidth
      stripCoeff paletteCoeff ((d.ν k (p.γ root)).prod volume) S pairPalette)
    (hstripCoeff : stripCoeff ≤ ENNReal.ofReal scales.failure)
    (hpaletteCoeff : 4*paletteCoeff ≤ ENNReal.ofReal scales.incidence.Cstate)
    (reference : Jets2.CommonDyadicVelocityReference finePv scales.paletteFinest
      (fun b => (pairPalette.map Parent.OriginalVelocityPalette.palettePairVector) {b}) palette)
    (hfinePv : 0 < finePv) (hfineWidth : finePv ≤ Jets2.dyadicParameterWidth scales.paletteFinest)
    (hpure : ∀ query : ℕ, query ≤ scales.paletteFinest →
      ∀ w : ℝ, scales.resolution ≤ w → w ≤ 1 →
      ∀ (base : Fin 3 → ℤ) (hidden : ℤ) (D : Set (Fin 2 → ℤ)), MeasurableSet D →
      (((d.ν k (p.γ root)).prod volume).restrict S) {z |
        (fun l => ⌊unshearedPacketBase p root z l/scales.resolution⌋)=base ∧
        ⌊physicalParentSignal (d.N k) p root (p.R root) z/w⌋=hidden ∧
        Jets2.parameterCode (Jets2.dyadicParameterWidth query) (fun l => Parent.v z.1 l)∈D} ≤
      (ENNReal.ofReal (scales.Cpure*scales.resolution^3*w^scales.dimension)*
        (palette.map (Jets2.parameterCode (Jets2.dyadicParameterWidth query))) D)*
          (ENNReal.ofReal ((hp.frozenPacket root).unitFrame.q)*d.ν k (p.γ root) (p.A root)))
    (hcensus : ∀ a w : ℝ, scales.resolution ≤ a → a ≤ 1 → scales.resolution ≤ w → w ≤ 1 →
      scales.Kcensus^(100:ℕ)*a ≤ w →
      (occupied S (fun z j => unshearedPacketBase p root z j)
        (physicalParentSignal (d.N k) p root (p.R root)) a w).Finite ∧
      ((occupied S (fun z j => unshearedPacketBase p root z j)
        (physicalParentSignal (d.N k) p root (p.R root)) a w).ncard:ℝ) ≤
          scales.Kcensus/(a^3*w^scales.dimension))
    (hband : ∀ R : ℝ, scales.resolution ≤ R → R ≤ 8*scales.ρ →
      ∀ U : Set P3, MeasurableSet U →
      ∀ center : P3 → ℝ, Measurable center →
      (((d.ν k (p.γ root)).prod volume).restrict S) {z | unshearedPacketBase p root z∈U ∧
        |physicalParentSignal (d.N k) p root (p.R root) z-center (unshearedPacketBase p root z)| ≤ R} ≤
      (ENNReal.ofReal (scales.Cband*R^scales.dimension)*volume U)*
        (ENNReal.ofReal ((hp.frozenPacket root).unitFrame.q)*d.ν k (p.γ root) (p.A root)))
    (level : ℕ) (hlevel : p.lev root ≤ level) (hlast : level ≤ m-1)
    (hend : ∀ z∈S, z∉p.oldEndpoints root ∧ z∉p.levelEndpoints level)
    (hterminal : ∀ z∈S, ∃ terminal : Fin p.C,
      p.lev terminal=m-1 ∧ p.γ terminal=p.γ root ∧ z∈p.F terminal)
    (hT : scales.T=p.T level-p.T (p.lev root)) :
    ∃ U : Set (Fin 4 → ℤ), MeasurableSet U ∧
      let code := clockParentCode p root (Parent.SignalGraph.ancestorSignal (d.N k) p root) scales.b
      let Src := S∩code ⁻¹' U
      MeasurableSet Src ∧
      ((d.ν k (p.γ root)).prod volume) S ≤
        scales.regularityFactor*((d.ν k (p.γ root)).prod volume) Src+
          (scales.regularityFactor*scales.supportLoss)*
            (ENNReal.ofReal ((hp.frozenPacket root).unitFrame.q)*d.ν k (p.γ root) (p.A root)) ∧
      (∀ x∈Src, ∀ y∈Src, ‖row (code x)-row (code y)‖ ≤
        scales.Lp*(‖clockParentCoordinates p root (Parent.SignalGraph.ancestorSignal (d.N k) p root) x-
          clockParentCoordinates p root (Parent.SignalGraph.ancestorSignal (d.N k) p root) y‖+scales.ρ)) ∧
      MeasurableSet (qualBad hp root level Src row scales.b scales.incidence.M scales.T scales.mesh
        scales.bound scales.err scales.duration) ∧
      ((d.ν k (p.γ root)).prod volume)
        (Src∩qualBad hp root level Src row scales.b scales.incidence.M scales.T scales.mesh
          scales.bound scales.err scales.duration) ≤
      scales.nativeFailureBound*
        (ENNReal.ofReal ((hp.frozenPacket root).unitFrame.q)*d.ν k (p.γ root) (p.A root)) := by
  let supply := nativeRootSupply_of_original_data hd hp root hVmax source hsource hsourceF hR hvelocity
    S hS hSsource scales hcoeffH hVmaxU row hrow hfit palette floors tables pairPalette finePv recordRadius
    stripCoeff paletteCoeff ratios hstripCoeff hpaletteCoeff reference hfinePv hfineWidth hpure hcensus hband
    level hlevel hlast hend hterminal hT
  obtain ⟨U,hU,hSrc,hmass,hLip,hbad,hfail⟩ := prepare_native_root_of_supply hp root hVmax
    source hsource hsourceF hR hvelocity hd S hS hSsource level hend row scales supply
  let code := clockParentCode p root (Parent.SignalGraph.ancestorSignal (d.N k) p root) scales.b
  let Src := S∩code ⁻¹' U
  have hbad' : MeasurableSet (qualBad hp root level Src row scales.b scales.incidence.M scales.T
      scales.mesh scales.bound scales.err scales.duration) := by
    simpa only [qualBad,ancCode] using hbad
  refine ⟨U,hU,hSrc,hmass,hLip,hbad',?_⟩
  have hh : ((((d.ν k (p.γ root)).prod volume).restrict Src)
      (qualBad hp root level Src row scales.b scales.incidence.M scales.T scales.mesh scales.bound
        scales.err scales.duration)) ≤
      scales.nativeFailureBound*(ENNReal.ofReal ((hp.frozenPacket root).unitFrame.q)*
        d.ν k (p.γ root) (p.A root)) := by
    simpa only [qualBad,ancCode] using hfail
  rw [Measure.restrict_apply hbad',inter_comm] at hh
  exact hh

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
