-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.NativeSampleScaleBlock, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleNative
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeAuxiliaryScaleBounds
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeMeshFit

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Set MeasureTheory
open Parent.ParentSource
open Parent.ParentSource.Native (ProblemData PathData PreparedAngularPath PaletteFamily BroadResidual
  labelledVelocityPalette)
open Parent.Qualification
open Parent.Qualification.PhysicalModel
open Parent.Qualification.PhysicalModel.NativeAncestor
open Submission.Lib.K4ParentSignalPreparation.Census
open scoped ENNReal BigOperators

noncomputable section

/-- Apply the native root step using the constructed scale package.
All scale projections and auxiliary resolution bounds are discharged
before the original root package is supplied. -/
theorem native_root_step_of_scale_data
    {Test : Type*} {d : ProblemData} (hd : d.Valid) {k m : ℕ} {p : PathData (d.W k)}
    {H : Fin (d.W k) → Set Ev} {u : Test → ℝ} {τ ε₀ : ℝ}
    {Q : PreparedAngularPath d k p m H u τ} (hpure : Q.uniformPureBounds ε₀)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    {design : NativeScaleDesign}
    {i stop : ℕ} {meshF envF : ℝ} {θF : ENNReal} {F : PaletteFamily Q i stop meshF envF θF}
    {rF frF : ℝ} {Rp : BroadResidual F rF frF} {c : ℕ} {K θ ε aA q h' a' : ℝ}
    {Krecord baseRef hiddenRef finePv paletteRatio cut frontRadius fraction Kcap : ℝ}
    {original : Fin (d.W k) → Set Event} {n : ℕ} {depth : Fin n → ℕ} {Kcore : ℝ} {e R : ℕ}
    {core : BroadMultiscaleCoreSource d k p original n depth Kcore e R}
    {sigmaNative Kcensus stripWidth : ℝ} {Tnative nmesh steps : ℕ}
    (native : NativeScaleData design (d.N k) sigmaNative Tnative (3*nmesh) steps Kcensus stripWidth θ)
    (hN : 1 < d.N k) (hib : i+c ≤ m-1) (hT : Tnative=p.T (i+c)-p.T i)
    {Kg fineMesh Vmax : ℝ}
    (hKg : 1 ≤ Kg) (hBrow : 28*Kg^6 ≤ d.N k^(design.regularity/1000))
    (hqaA : q/aA=((2:ℝ)^p.T i)⁻¹/δ (d.N k) (p.r i))
    (herror : 80*Kg^7*Submission.Lib.K4DyadicRowScales.mesh nmesh^((1-design.dimension)/24) ≤
      d.N k^(-design.target))
    (hFine : fineMesh=Submission.Lib.K4DyadicRowScales.mesh nmesh/(2:ℝ)^steps)
    (hsteps : (2:ℝ)^steps ≤ d.N k^(design.coefficient/5))
    (hgraph : d.N k^(-(NativeDesign.graphLowerCoeff design.kappa1 design.dimension design.Ep
      design.precision*design.gainL)) ≤ Submission.Lib.K4DyadicRowScales.mesh nmesh)
    (hVmax : 0 ≤ Vmax) (hvelocity : ∀ w, ∀ z ∈ Rp.residual w, ‖Parent.v z.1‖ ≤ Vmax)
    (hcoeffH : coefficientBound (p:=p) Vmax ≤ d.N k^design.coefficient)
    (hVmaxU : Vmax ≤ d.N k^design.coefficient)
    (radius : ℝ) (beta : ENNReal)
    (hstripCoeff : ENNReal.ofReal ((8*fraction)/cut)/beta ≤ ENNReal.ofReal (1/2:ℝ))
    (hpaletteCoeff : 4*(ENNReal.ofReal ((8*paletteRatio)/cut)/beta) ≤
      ENNReal.ofReal (d.N k^design.coefficient))
    (hfinePv : 0 < finePv) (hfineWidth : finePv ≤ d.N k^(-design.floor))
    (histop : i ≤ stop) (hri : 0 ≤ p.r i) (hrLi : p.r i ≤ d.L)
    (hdepth : p.r i+(NativeDesign.auxiliaryChiCoeff design.kappa1 design.dimension design.Ep
      design.precision design.loss*design.gainL)*
      (NativeDesign.auxiliaryFinest design.kappa1 design.dimension design.Ep design.precision design.loss:ℝ) ≤ d.L)
    (hbaseRef : 3*baseRef ≤
      (d.N k^(NativeDesign.auxiliaryChiCoeff design.kappa1 design.dimension design.Ep
        design.precision design.loss*design.gainL))^
      (-(NativeDesign.auxiliaryFinest design.kappa1 design.dimension design.Ep design.precision design.loss:ℝ)))
    (hhiddenRef : 3*hiddenRef ≤
      (d.N k^(NativeDesign.auxiliaryChiCoeff design.kappa1 design.dimension design.Ep
        design.precision design.loss*design.gainL))^
      (-(NativeDesign.auxiliaryFinest design.kappa1 design.dimension design.Ep design.precision design.loss:ℝ)))
    (hRatio : 0 ≤ paletteRatio) (hcut : 0 < cut) (hKcap : 0 ≤ Kcap)
    (hCpure : 4*625*((8*paletteRatio)/cut)*Kcap ≤ d.N k^design.coefficient)
    {f₀ perror : ℝ}
    (hprofile : ∀ r, 0 ≤ r → r ≤ d.L → |d.f r-f₀-design.dimension*r| ≤ perror)
    (hCband : 64*(max p.κ (d.K k))^2*p.κ*4^design.dimension*
      d.N k^(2*perror+(τ+2*δ₀*d.L)+ε₀) ≤ d.N k^design.coefficient) :
    let chi := NativeDesign.auxiliaryChiCoeff design.kappa1 design.dimension design.Ep
      design.precision design.loss*design.gainL
    let finest : ℝ := NativeDesign.auxiliaryFinest design.kappa1 design.dimension design.Ep
      design.precision design.loss
    ∀ RP : RootPackage Q F Rp c K θ ε aA q design.dimension h' a' Krecord baseRef hiddenRef
      finePv paletteRatio cut frontRadius fraction chi finest design.dimension Kcap core,
      RP.graphMesh=Submission.Lib.K4DyadicRowScales.mesh nmesh → RP.Brow=28*Kg^6 →
      (∀ a, F.active a → ∀ x ∈ RP.E1 (p.γ a) ∩ p.F a,
        |q/aA*Submission.Lib.K4GlobalParentSignal.rate (p.R a) x.1 x.2-
          ∑ j : Fin 3, RP.row a (ancCode (d.N k) p a RP.graphMesh x) j*
            (![1,x.1.2 3,x.1.2 4] : Fin 3 → ℝ) j| ≤
        80*Kg^7*Submission.Lib.K4DyadicRowScales.mesh nmesh^((1-design.dimension)/24)) →
      (∀ a, F.active a → ∀ b w : ℝ, fineMesh ≤ b → b ≤ 1 → fineMesh ≤ w → w ≤ 1 →
        Kcensus^(100:ℕ)*b ≤ 1*w →
        (occupied (RP.E1 (p.γ a) ∩ p.F a) (fun z j => unshearedPacketBase p a z j)
          (physicalParentSignal (d.N k) p a (p.R a)) b w).Finite ∧
        ((occupied (RP.E1 (p.γ a) ∩ p.F a) (fun z j => unshearedPacketBase p a z j)
          (physicalParentSignal (d.N k) p a (p.R a)) b w).ncard:ℝ) ≤
          Kcensus/(b^3*w^design.dimension)) →
      ∃ (E1' : Fin (d.W k) → Set Ev) (hmeas : ∀ w, MeasurableSet (E1' w))
        (hsub : ∀ w, E1' w ⊆ RP.E1 w),
        (∑ w, ENNReal.ofReal (d.ω k w)*((d.ν k w).prod volume) (RP.E1 w)) ≤
          (∑ w, ENNReal.ofReal (d.ω k w)*((d.ν k w).prod volume) (E1' w))+native.pre.charge ∧
        SampleHbox hp (RP.restrict E1' hmeas hsub) radius stripWidth beta design.degree Tnative
          native.scales.mesh θ native.scales.duration native.scales.bound native.scales.regularityFactor
          (native.scales.regularityFactor*native.scales.supportLoss) native.scales.nativeFailureBound
          native.scales.Lp native.scales.ρ := by
  intro chi finest RP hMesh hBrowEq hFitRaw hCensusRaw
  have hb : native.scales.b=Submission.Lib.K4DyadicRowScales.mesh nmesh := by
    rw [native.b_eq,←Jets2.mk4_mesh_dyadic]
  have hGraphUpper : native.scales.b ≤ d.N k^(-design.target) := by
    rw [native.b_eq]
    exact native_dyadic_width_le_fit nmesh hKg design.valid.1 herror
  obtain ⟨haux,hbaseLo,hbaseHi,hstartHi⟩ := native_auxiliary_resolution_bounds native hN
    (by simpa only [hb] using hgraph) hGraphUpper hsteps
  have hFineResolution : fineMesh ≤ native.scales.resolution := by
    rw [hFine,native.resolution_eq,←Jets2.mk4_mesh_dyadic]
  have hKc0 : 0 ≤ Kcensus := by
    have hh := native.scales.hKcensus
    rw [native.Kcensus_eq] at hh
    exact zero_le_one.trans hh
  have hResolved := auxiliary_resolution_resolves_end hN.le hdepth hbaseLo
  obtain ⟨E1',hmeas,hsub,hmass,hbox⟩ := native_root_step hd hpure hp hHE hH
    native.scales native.pre hib (native.T_eq.trans hT) hb
    (by simpa only [native.B_eq] using hBrow) hqaA
    (by simpa only [native.fitError_eq] using herror)
    hKc0 (by rw [native.Kcensus_eq]) hFineResolution native.dimension_eq
    hVmax hvelocity (by simpa only [native.H_eq] using hcoeffH)
    (by simpa only [native.U_eq] using hVmaxU) radius beta
    (by simpa only [native.failure_eq] using hstripCoeff)
    (by simpa only [native.Cstate_eq] using hpaletteCoeff)
    hfinePv (hfineWidth.trans native.paletteWidth_lower) haux histop hri hrLi hdepth
    hbaseRef hhiddenRef hRatio hcut hKcap hbaseLo hbaseHi hstartHi
    (by simpa only [native.Cpure_eq] using hCpure) native.dimension_eq
    (by simpa only [native.dimension_eq] using hprofile)
    (by simpa only [native.dimension_eq,native.Cband_eq] using hCband)
    hResolved RP hMesh hBrowEq hFitRaw hCensusRaw
  refine ⟨E1',hmeas,hsub,hmass,?_⟩
  simpa only [native.stripWidth_eq,native.M_eq,native.T_eq,native.qerror_eq] using hbox

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
