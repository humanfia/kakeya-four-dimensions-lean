-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.NativeAncestorDerivativeSource, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.NativeAncestorOriginalFloors
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.DerivativeListsFromDyadicFloors

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.NativeAncestor

open Set MeasureTheory
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent
open ParentSource ParentSource.Native
open scoped ENNReal

noncomputable section

/-- Prepare every derivative table on an ORIGINAL source before the
child-state stage. The coarse prefix is supplied by the actual scalar
quadratic, and all finer entries by original coefficient floors and
current pure-cell numerators. The full original prior is unchanged. -/
theorem prepare_native_original_derivative_source {I : Type*} [Fintype I]
    {d : ProblemData} (hd : d.Valid) {k m : ℕ} {p : PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (root : Fin p.C) {Vmax : ℝ} (hVmax : 0 ≤ Vmax)
    (source : Set Ev) (hsource : MeasurableSet source) (hsourceF : source⊆p.F root)
    (hR : (p.R root).totalDegree ≤ 2) (hvelocity : ∀ z∈source, ‖v z.1‖ ≤ Vmax)
    (S : Set Ev) (hS : MeasurableSet S) (hSsource : S⊆source)
    (H : ℕ) (hH : 1 ≤ (H:ℝ)) (hcoeffH : coefficientBound (p:=p) Vmax ≤ H)
    {palette : Measure (Fin 2 → ℝ)} {dimension exponent : ℝ} {start count : ℕ}
    (floors : Jets2.OriginalDyadicFloorData ((hp.frozenPacket root).prior (d.ν k (p.γ root)))
      (coefficientTable (d.N k) p root Vmax) ((hp.frozenPacket root).selectedEvent S)
        palette dimension exponent start count)
    (hdim : 0 ≤ dimension)
    (level : I → ℕ) (hstop : ∀ i, level i < start+count)
    (cut : I → ℝ) (hcut : ∀ i, 0 < cut i)
    {δ C : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C)
    (hδlevel : ∀ i, δ ≤ Jets2.dyadicParameterWidth (level i))
    (hsmall : ∀ i, 3*((H:ℝ)+1)*δ ≤ Jets2.dyadicParameterWidth (level i))
    (hpure : ∀ (i : I) (w : ℝ), δ ≤ w → w ≤ 1 →
      ∀ (b : Fin 3 → ℤ) (j : ℤ) (D : Set (Fin 2 → ℤ)), MeasurableSet D →
      (((d.ν k (p.γ root)).prod volume).restrict S) {z |
        (fun l => ⌊unshearedPacketBase p root z l/δ⌋)=b ∧
        ⌊physicalParentSignal (d.N k) p root (p.R root) z/w⌋=j ∧
        Jets2.parameterCode (Jets2.dyadicParameterWidth (level i)) (fun l => v z.1 l)∈D} ≤
          (ENNReal.ofReal (C*δ^3*w^dimension)*
            (palette.map (Jets2.parameterCode (Jets2.dyadicParameterWidth (level i)))) D)*
              (ENNReal.ofReal ((hp.frozenPacket root).unitFrame.q)*d.ν k (p.γ root) (p.A root))) :
    ∃ R : Set Ev, MeasurableSet R ∧ R⊆S ∧
      ((d.ν k (p.γ root)).prod volume) (S\R) ≤
        (∑ i : {i : I // start ≤ level i}, ENNReal.ofReal (cut i.val*Jets2.zoomBlockVisitConstant))*
          (ENNReal.ofReal ((hp.frozenPacket root).unitFrame.q)*d.ν k (p.γ root) (p.A root)) ∧
      Nonempty (Jets2.OriginalDerivativeListData (coefficientTable (d.N k) p root Vmax)
        ((hp.frozenPacket root).selectedEvent R) level (fun i =>
          max (6*(H:ℝ)/Jets2.dyadicParameterWidth start+2)
            ((2*(H:ℝ)+3)^7*(6*(H:ℝ)+12)^4*
              ((151200*(12*(H:ℝ)+3)*C*(3:ℝ)^dimension)*
                (Jets2.dyadicParameterWidth (level i))^(-exponent)/cut i)*
                  (2*(⌈2*(H:ℝ)+5⌉:ℝ)+1)))) := by
  let packet := hp.frozenPacket root
  let ν := d.ν k (p.γ root)
  let νA := packet.prior ν
  let pm := model hp root Vmax hVmax source hsource hsourceF
  let Eclock := packet.selectedEvent S
  letI : IsProbabilityMeasure ν := (hd.weights k).2.2 _
  letI : IsProbabilityMeasure νA := hp.frozenPacket_prior_probability (by linarith [hd.1 k]) root
  have hA : ν (p.A root)≠0 := (hp.assignment_mass_pos (by linarith [hd.1 k]) root).ne'
  have hEclock : MeasurableSet Eclock := packet.measurable_selectedEvent hS
  have ht : ∀ z∈Eclock, z.2∈Icc (0:ℝ) 1 := fun z hz =>
    (packet.event_unit_time ((packet.selectedEvent_subset (hSsource.trans hsourceF)) hz)).2
  have hcoeff : ∀ z∈Eclock, ∀ j, |pm.scalarCoefficients z.1 j| ≤ H := fun z _ j =>
    (model_global_coefficients hp root hVmax source hsource hsourceF z.1 j).trans hcoeffH
  have hpureClock (i : I) (w : ℝ) (hw : δ ≤ w) (hw1 : w ≤ 1)
      (b : Fin 3 → ℤ) (j : ℤ) (vcode : Fin 2 → ℤ) :
      ((νA.prod volume).restrict Eclock) {z |
        Jets2.originalBaseCode pm.scalarCoefficients δ z=b ∧
        ⌊Jets2.zx (pm.scalarCoefficients z.1) z.2/w⌋=j ∧
        Jets2.parameterCode (Jets2.dyadicParameterWidth (level i))
          (Jets2.zv (pm.scalarCoefficients z.1))=vcode} ≤
      ENNReal.ofReal (C*δ^3*w^dimension)*
        (palette.map (Jets2.parameterCode (Jets2.dyadicParameterWidth (level i)))) {vcode} := by
    exact model_scalar_pure_cap hp root hVmax source hsource hsourceF hR hvelocity ν hA
      S hS hSsource δ w (Jets2.dyadicParameterWidth (level i)) b j {vcode}
      (measurableSet_singleton _) _ (hpure i w hw hw1 b j {vcode} (measurableSet_singleton _))
  have hfloors : Jets2.OriginalDyadicFloorData νA pm.scalarCoefficients Eclock
      palette dimension exponent start count := by
    simpa only [pm,model_coefficientTable] using floors
  obtain ⟨Rclock,hRclock,hRE,hloss,⟨tables⟩⟩ :=
    Jets2.prepare_all_derivative_lists_of_dyadic_floors (νA.prod volume) νA pm.scalarCoefficients
      pm.measurable_scalarCoefficients Eclock hEclock ht H hH hcoeff hfloors hdim level hstop cut hcut
      hδ hC hδlevel hsmall hpureClock
  let loss : ENNReal := ∑ i : {i : I // start ≤ level i},
    ENNReal.ofReal (cut i.val*Jets2.zoomBlockVisitConstant)
  have hloss' : (νA.prod volume) (Eclock\Rclock) ≤ loss := by
    simpa only [measure_univ,mul_one] using hloss
  obtain ⟨R,hRmeas,hRS,hselected,hlossOriginal⟩ := original_good_source_of_clock packet ν hA
    S hS (hSsource.trans hsourceF) Rclock hRclock loss hloss'
  have hselectedR : packet.selectedEvent R=Rclock := hselected.trans (inter_eq_right.mpr hRE)
  refine ⟨R,hRmeas,hRS,hlossOriginal,?_⟩
  rw [show (hp.frozenPacket root).selectedEvent R=Rclock from hselectedR]
  simpa only [pm,model_coefficientTable] using (Nonempty.intro tables)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.NativeAncestor
