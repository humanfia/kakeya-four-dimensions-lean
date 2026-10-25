-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.NativePreStateFromScales, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.OriginalPreStateScales

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.NativeAncestor

open Set MeasureTheory
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent
open ParentSource ParentSource.Native
open Submission.Lib.K4ParentSignalPreparation.Census
open scoped ENNReal BigOperators

noncomputable section

/-- Scalar-only P1 requirements construct the original floors and
actual derivative tables from the original raw pure-cell numerators. -/
theorem prepare_native_pre_state_from_scales
    {d : ProblemData} (hd : d.Valid) {k m : ℕ} {p : PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (root : Fin p.C) {Vmax : ℝ} (hVmax : 0 ≤ Vmax)
    (source : Set Ev) (hsource : MeasurableSet source) (hsourceF : source⊆p.F root)
    (hR : (p.R root).totalDegree ≤ 2) (hvelocity : ∀ z∈source, ‖v z.1‖ ≤ Vmax)
    (S : Set Ev) (hS : MeasurableSet S) (hSsource : S⊆source)
    (a : OriginalRootScales) (ps : OriginalPreStateScales a)
    (hcoeff : coefficientBound (p:=p) Vmax ≤ a.H)
    (palette : Measure (Fin 2 → ℝ)) (hpalette : IsProbabilityMeasure palette)
    (hcensus : ∀ b w : ℝ, a.resolution ≤ b → b ≤ 1 → a.resolution ≤ w → w ≤ 1 →
      a.Kcensus^(100:ℕ)*b ≤ w →
      (occupied S (fun z j => unshearedPacketBase p root z j)
        (physicalParentSignal (d.N k) p root (p.R root)) b w).Finite ∧
      ((occupied S (fun z j => unshearedPacketBase p root z j)
        (physicalParentSignal (d.N k) p root (p.R root)) b w).ncard:ℝ) ≤
          a.Kcensus/(b^3*w^a.dimension))
    (hpure : ∀ query : ℕ, query ≤ a.paletteFinest →
      ∀ base w : ℝ, a.resolution ≤ base → base ≤ Jets2.dyadicParameterWidth a.floorStart →
      base ≤ w → w ≤ 1 →
      ∀ (b : Fin 3 → ℤ) (j : ℤ) (D : Set (Fin 2 → ℤ)), MeasurableSet D →
      (((d.ν k (p.γ root)).prod volume).restrict S) {z |
        (fun l => ⌊unshearedPacketBase p root z l/base⌋)=b ∧
        ⌊physicalParentSignal (d.N k) p root (p.R root) z/w⌋=j ∧
        Jets2.parameterCode (Jets2.dyadicParameterWidth query) (fun l => v z.1 l)∈D} ≤
      (ENNReal.ofReal (a.Cpure*base^3*w^a.dimension)*
        (palette.map (Jets2.parameterCode (Jets2.dyadicParameterWidth query))) D)*
          (ENNReal.ofReal ((hp.frozenPacket root).unitFrame.q)*d.ν k (p.γ root) (p.A root))) :
    ∃ R : Set Ev, MeasurableSet R ∧ R⊆S ∧
      ((d.ν k (p.γ root)).prod volume) (S\R) ≤ ps.charge*
        (ENNReal.ofReal ((hp.frozenPacket root).unitFrame.q)*d.ν k (p.γ root) (p.A root)) ∧
      Nonempty (Jets2.OriginalPreStateData ((hp.frozenPacket root).prior (d.ν k (p.γ root)))
        (coefficientTable (d.N k) p root Vmax) ((hp.frozenPacket root).selectedEvent R)
        palette a.dimension a.floorExponent a.floorStart a.floorCount
        (fun i : Fin a.regLength => a.regLevel i.val) a.KL) := by
  classical
  let hex := prepare_native_original_pre_state_data (I:=Fin a.regLength)
    a.dimension a.floorExponent a.hdim ps.hdimension ps.hexponent
  let h := Classical.choose_spec hex
  let hp0 := Classical.choose_spec h.2
  have hvalid : 0 ≤ a.dimension ∧ a.dimension < 1 ∧ 0 < a.floorExponent :=
    ⟨a.hdim,ps.hdimension,ps.hexponent⟩
  have hEta : originalPreStateEta a.dimension a.floorExponent a.regLength=Classical.choose hex := by
    simp only [originalPreStateEta,dite_eq_left hvalid,hex]
  have hWidth : originalPreStateWidth a.dimension a.floorExponent a.regLength=Classical.choose h.2 := by
    simp only [originalPreStateWidth,dite_eq_left hvalid,hex,h]
  have hresb : a.resolution ≤ a.b := by
    rw [a.hb_eq]
    exact le_mul_of_one_le_right a.hresolution.le (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
  have hresStart : a.resolution ≤ Jets2.dyadicParameterWidth a.floorStart :=
    hresb.trans (ps.hresolved.trans (Jets2.dyadicParameterWidth_antitone (by have hc := ps.hcount; omega)))
  have hFloorWidth (i : Fin a.floorCount) : a.resolution ≤ Jets2.dyadicParameterWidth (a.floorStart+i.val) :=
    hresb.trans (ps.hresolved.trans (Jets2.dyadicParameterWidth_antitone (by omega)))
  have hregWidth (i : Fin a.regLength) : a.resolution ≤ Jets2.dyadicParameterWidth (a.regLevel i.val) :=
    hresb.trans (a.hbreg i.val i.isLt)
  have hh := hp0.2 d hd k m p κ₁ δ₀ σ s Mp Dp hp root Vmax hVmax source hsource hsourceF
    hR hvelocity S hS hSsource a.floorStart a.floorCount ps.hcount
    (by rw [←hWidth]; exact ps.hstart)
    a.H a.Cpure ps.Kfloor a.Kcensus a.resolution a.steps a.hH hcoeff a.hCpure ps.hKfloor
    a.hresolution a.hKcensus a.hsteps (by rw [←a.hb_eq]; exact ps.hresolved)
    palette hpalette
    (by rw [←hEta]; exact ps.hcoeffBudget)
    (by rw [←hEta]; exact ps.hcapBudget)
    (by rw [←hEta]; exact ps.hsupportBudget) hcensus
    (fun i w hw hw1 b j D hD => hpure (a.floorStart+i.val)
      (by have hf := ps.hfloorFinest; omega) _ w (hFloorWidth i)
        (Jets2.dyadicParameterWidth_antitone (by omega)) hw hw1 b j D hD)
    ps.Hnat ps.hHnat (fun i : Fin a.regLength => a.regLevel i.val) ps.hregEnd ps.cut ps.hcut
    a.resolution a.Cpure a.KL a.hresolution a.hCpure hregWidth ps.hsmall ps.hKL
    (fun i w hw hw1 b j D hD => hpure (a.regLevel i.val) (a.hregFinest i.val i.isLt)
      _ w le_rfl hresStart hw hw1 b j D hD)
  simpa only [OriginalPreStateScales.charge,hEta] using hh

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.NativeAncestor
