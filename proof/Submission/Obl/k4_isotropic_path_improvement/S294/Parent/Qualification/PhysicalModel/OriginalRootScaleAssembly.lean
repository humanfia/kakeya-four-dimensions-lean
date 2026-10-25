-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.OriginalRootScaleAssembly, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.OriginalRootFromData
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.OriginalRootGrid
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.RootGeometryBudgets
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.NativeClockScales
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PencilRadiusScales

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel

open Set MeasureTheory
open Jets2
open Submission.Lib.K4ContinuousKakeya
open WangZahlLot.Obl.wz_slab_local_linearity
open scoped ENNReal

noncomputable section

/-- Assemble the full original scalar record from the actual finite
grids and scalar power budgets. All values are fixed explicit powers;
no coefficient, incidence source, row or output certificate is used. -/
def originalRootScales_of_grid
    {b : ℝ} {nr ns : ℕ} (g : OriginalRootGrid b nr ns)
    (N e h a E target ar dimension Cmk Kcensus stripWidth : ℝ)
    (steps T M : ℕ) (analyticEpsilon cZeta alpha Q0 : ℝ)
    (mesh err duration : ℝ) (bound : ℤ)
    (hN : 1 < N) (he : 0 < e) (hh : 0 < h) (ha : 0 < a) (hE : 0 < E)
    (har : 0 ≤ ar) (hsmall : h ≤ a/100000000) (hae : a ≤ e)
    (htarget : E+2*h ≤ target) (hHlarge : 32 ≤ N^h) (hAconstant : 2 ≤ N^a)
    (hdim : 0 ≤ dimension) (hdim1 : dimension ≤ 1)
    (hKcensus : 1 ≤ Kcensus) (hsteps : Kcensus^(100:ℕ) ≤ (2:ℝ)^steps)
    (hCmk : 0 ≤ Cmk) (hMK : FiniteMK 3 Cmk)
    (hwidth : N^(-h) ≤ stripWidth)
    (hfloor : N^(-E) ≤ dyadicParameterWidth g.paletteFinest)
    (hRegA : (2:ℝ)^g.regStep ≤ N^(e/4))
    (hResA : (2:ℝ)^g.resStep ≤ N^ar)
    (hgeometryR : rootGeometryConstant (N^h) (N^(a/1000)) (6*(N^(e/4)+3*N^(a/1000)))*g.rho ≤
      dyadicParameterWidth g.lastLevel)
    (hgeometryB : rootGeometryConstant (N^h) (N^(a/1000)) (6*(N^(e/4)+3*N^(a/1000)))*b ≤
      g.rho*dyadicParameterWidth g.lastLevel)
    (hgeometryE : 16*N^(-target) ≤ g.rho*dyadicParameterWidth g.lastLevel)
    (hrow : 3*((3*N^h+1)*(6*(N^(e/4)+3*N^(a/1000)))) ≤ N^(2*e))
    (hNative : 2*e ≤ nativeClockExponent N T*alpha)
    (hqualification : NativeQualificationAt dimension M analyticEpsilon cZeta alpha Q0)
    (halpha : 0 ≤ alpha) (hQ : Q0 ≤ N^(nativeClockExponent N T)) (hT : 0 < T)
    (hcutoff : g.zeta ≤ (((2:ℝ)^T)⁻¹)^cZeta)
    (hNativeNum : 625*(151200*(12*N^h+3)*N^h*(3:ℝ)^dimension)/N^(-4*e) ≤ N^(8*e))
    (hfill : (8*Cmk*7^3)^2*(3*N^(4*e))^3 ≤
      (((originalPencilRadius (N^h) stripWidth)/2)^3/2*(1-(1/2:ℝ))^3)*N^(16*e))
    (hss : worldScalarSupportConstant (N^(a/1000)) (N^h) (N^(-4*e)) (N^(16*e)) 2 ≤
      N^(nativeClockExponent N T*alpha))
    (hcap : 8*(N^(8*e))^2 ≤ N^(nativeClockExponent N T*alpha))
    (hresNative : 2*(N^ar+5*(N^(2*e))^2) ≤ N^(nativeClockExponent N T*alpha))
    (hmesh : 0 < mesh)
    (hbound : 3*N^h+(1+2*N^h)*N^(nativeClockExponent N T*analyticEpsilon) ≤ mesh*((bound:ℝ)-1))
    (herror : N^(-target)+(1+2*N^h)*
      (2*((3*N^h+1)*(6*(N^(e/4)+3*N^(a/1000))))*g.rho+((2:ℝ)^T)⁻¹^((M:ℝ)+1/8))+
        (M+1)*mesh ≤ err)
    (hduration : duration ≤ ((2:ℝ)^T)⁻¹*N^(-(nativeClockExponent N T*analyticEpsilon))) :
    OriginalRootScales := by
  let H := N^h
  let B := N^(a/1000)
  let Ar := N^(e/4)
  let Lp := 6*(Ar+3*B)
  let error := N^(-target)
  let resolution := b/(2:ℝ)^steps
  let radius := originalPencilRadius H stripWidth
  let eta := 2*((3*H+1)*Lp)*g.rho
  let ch := nativeClockExponent N T
  have hNp : 0 < N := zero_lt_one.trans hN
  have hH : 1 ≤ H := by dsimp only [H]; linarith only [hHlarge]
  have hB : 1 ≤ B := Real.one_le_rpow hN.le (by positivity : 0 ≤ a/1000)
  have hAr : 1 ≤ Ar := Real.one_le_rpow hN.le (by positivity : 0 ≤ e/4)
  have hLp : 0 ≤ Lp := by dsimp only [Lp]; positivity
  have hHB : H ≤ B := Real.rpow_le_rpow_of_exponent_le hN.le (by linarith only [hsmall,ha])
  have hb : 0 < b := by rw [g.b_eq]; exact dyadicParameterWidth_pos _
  have hres : 0 < resolution := by dsimp only [resolution]; positivity
  have hresb : resolution ≤ b := div_le_self hb.le (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  have hlast : dyadicParameterWidth g.lastLevel ≤ g.zeta :=
    (dyadicParameterWidth_antitone (g.resMax ns (by omega))).trans g.resFloor
  have hgeometry := root_geometry_bounds hH hB hLp hb g.rho_pos g.rho_one
    (dyadicParameterWidth_pos g.lastLevel) hlast g.zeta_one hres.le hresb
    (Real.rpow_nonneg hNp.le (-target)) hgeometryR hgeometryB hgeometryE
  have hpencil := originalPencilRadius_bounds hHlarge (by
    simpa only [Real.rpow_neg hNp.le] using hwidth)
  have hradius : 0 < radius := hpencil.1
  have hPencilLower : (H^4)⁻¹ ≤ radius := hpencil.2.2.2.2.2
  have hRadiusA : radius⁻¹ ≤ N^a := by
    have hh' : radius⁻¹ ≤ H^4 := by
      have hhp : 0 < H^4 := by positivity
      simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hhp) hPencilLower
    calc
      _ ≤ H^4 := hh'
      _ = N^(4*h) := by
        dsimp only [H]
        rw [←Real.rpow_mul_natCast hNp.le]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN.le (by linarith only [hsmall,ha])
  have hregWidth (i : ℕ) (hi : i < nr+1) :
      N^(-E) ≤ dyadicParameterWidth (i*g.regStep) :=
    hfloor.trans (dyadicParameterWidth_antitone (g.regFinest i hi))
  have hErrorReg (i : ℕ) (hi : i < nr+1) :
      error/dyadicParameterWidth (i*g.regStep) ≤ N^a := by
    have hw : error ≤ dyadicParameterWidth (i*g.regStep) := by
      exact (Real.rpow_le_rpow_of_exponent_le hN.le (by linarith only [htarget,hh])).trans (hregWidth i hi)
    exact (div_le_one (dyadicParameterWidth_pos _)).mpr hw |>.trans
      (Real.one_le_rpow hN.le ha.le)
  have hFloorExponent : 0 ≤ a/(10000*E) := by positivity
  have hreserve : 1/N^(8*e) ≤ (dyadicParameterWidth g.paletteFinest)^(a/(10000*E)) := by
    have hp := Real.rpow_le_rpow (Real.rpow_nonneg hNp.le (-E)) hfloor hFloorExponent
    have heq : (N^(-E))^(a/(10000*E))=N^(-(a/10000)) := by
      rw [←Real.rpow_mul hNp.le]
      congr 1
      field_simp
    rw [heq] at hp
    calc
      _=N^(-(8*e)) := by rw [Real.rpow_neg hNp.le,one_div]
      _≤N^(-(a/10000)) := Real.rpow_le_rpow_of_exponent_le hN.le (by linarith only [hae,he])
      _≤_ := hp
  have htime := nativeClockExponent_time_range hN T hT halpha
  let inc : OriginalIncidenceScales b g.rho H (N^(2*e)) eta error g.zeta dimension
      (worldScalarSupportConstant B (N^h) (N^(-4*e)) (N^(16*e)) 2)
      (N^(ch*alpha)) (N^(8*e)) (N^h) g.floorStart g.floorCount (a/(10000*E)) := {
    L := ns+1
    hL := by omega
    level := fun i => i*g.resStep
    hlevel0 := by simp
    A := N^ar
    hA := Real.one_le_rpow hN.le har
    hratio := fun i _ => (le_of_eq (g.resRatio i)).trans
      (mul_le_mul_of_nonneg_right hResA (dyadicParameterWidth_pos _).le)
    hfloorScale := by simpa only [Nat.add_sub_cancel] using g.resFloor
    hsmall := fun i hi => (hgeometry.2.2.2.1 _ (dyadicParameterWidth_antitone (g.resMax i hi))).1
    hρs := fun i hi => (hgeometry.2.2.2.1 _ (dyadicParameterWidth_antitone (g.resMax i hi))).2.1
    hosc := fun i hi => (hgeometry.2.2.2.1 _ (dyadicParameterWidth_antitone (g.resMax i hi))).2.2
    n0 := g.worldLevel
    hρdyadic := g.rho_eq
    lastLevel := g.lastLevel
    hlevelMax := g.resMax
    hqueryMax := g.queryMax
    hfloorStart := g.floorStart_world
    hfloorEnd := g.floorEnd
    hexponent := hFloorExponent
    hreserve := by simpa only [g.floorFinest] using hreserve
    resolution := resolution
    hresolution := hres
    hcanonical := hgeometry.2.2.2.2
    entryCut0 := N^(-4*e)
    hentryCut0 := Real.rpow_pos_of_pos hNp _
    entryCut := fun _ => N^(-4*e)
    hentryCut := fun _ _ => Real.rpow_pos_of_pos hNp _
    Cstate := N^h
    hCstate := Real.rpow_nonneg hNp.le _
    cut := fun _ => N^(-32*e)
    hcut := fun _ _ => Real.rpow_pos_of_pos hNp _
    analyticEpsilon := analyticEpsilon
    cZeta := cZeta
    alpha := alpha
    Q0 := Q0
    N := N
    ch := ch
    nativeCut := N^(-4*e)
    M := M
    hqualification := hqualification
    hN := hNp
    hch := nativeClockExponent_pos hN hT
    hQ := hQ
    hHtarget := rfl
    hζ := g.zeta_pos
    hζ1 := g.zeta_one
    hρζ := g.rho_zeta
    hnativeCut := Real.rpow_pos_of_pos hNp _
    hnativeNum := hNativeNum
    hcapH := hcap
    hssH := hss
    hresH := hresNative
  }
  exact {
    b := b
    ρ := g.rho
    H := H
    B := B
    error := error
    Lp := Lp
    Uvelocity := H
    stripWidth := stripWidth
    radius := radius
    failure := 1/2
    hb := hb
    hρ := g.rho_pos
    hρ1 := g.rho_one
    hbρ := hgeometry.1
    hH := hH
    hB := hB
    hHB := hHB
    he := Real.rpow_nonneg hNp.le _
    hLp := hLp
    hUvelocity := zero_le_one.trans hH
    hfailure := by norm_num
    hfailure1 := by norm_num
    regLength := nr+1
    hregLength := by omega
    regLevel := fun i => i*g.regStep
    hreg0 := by simp
    regSteps := fun i => g.fineLevel-i*g.regStep
    hregEq := g.regWidth
    hbreg := g.regFine
    Ar := Ar
    hAr := hAr
    hregRatio := fun i _ => (le_of_eq (g.regRatio i)).trans
      (mul_le_mul_of_nonneg_right hRegA (dyadicParameterWidth_pos _).le)
    hregFloor := by simpa only [Nat.add_sub_cancel] using g.regFloor
    rhoBroad := radius
    D := N^h
    KL := N^(a/2)
    Areg := N^a
    hBroadRadius := hradius
    hBroadSmall := hpencil.2.1
    hBroadWidth := hpencil.2.2.1
    hD := Real.rpow_pos_of_pos hNp _
    hAreg := Real.one_le_rpow hN.le ha.le
    hBA := Real.rpow_le_rpow_of_exponent_le hN.le (by linarith only [ha])
    hKLA := Real.rpow_le_rpow_of_exponent_le hN.le (by linarith only [ha])
    hDA := Real.rpow_le_rpow_of_exponent_le hN.le (by linarith only [hsmall,ha])
    hcA := by norm_num; exact hAconstant
    hρA := hRadiusA
    heA := hErrorReg
    hLpReg := le_rfl
    W := g.W
    resolution := resolution
    Kcensus := Kcensus
    dimension := dimension
    Cband := N^h
    rate := N^(-4*e)
    Hprior := N^(4*e)
    hresolution := hres
    hKcensus := hKcensus
    hCband := Real.rpow_nonneg hNp.le _
    hrate := Real.rpow_pos_of_pos hNp _
    hHprior := Real.rpow_pos_of_pos hNp _
    steps := steps
    hsteps := hsteps
    hb_eq := by dsimp only [resolution]; field_simp
    fineSteps := g.fineSteps
    columnSteps := g.columnSteps
    hwidth := g.width
    hcolumn := g.column
    hbw := g.bw
    hwρ := g.wrho
    hround := fun w hw => (hgeometry.2.2.1 w (g.wlower w hw)).1
    hgraphWidth := fun w hw => (hgeometry.2.2.1 w (g.wlower w hw)).2.1
    hrowWidth := fun w hw => (hgeometry.2.2.1 w (g.wlower w hw)).2.2.1
    Cmk := Cmk
    Kfill := N^(16*e)
    hradius := hradius
    hCmk := hCmk
    hMK := hMK
    hKfill := Real.rpow_pos_of_pos hNp _
    hdim := hdim
    hdim1 := hdim1
    hfillBudget := hfill
    hPencilWidth := hpencil.2.2.2.1
    hPencilSmall := hpencil.2.2.2.2.1
    zeta := g.zeta
    hzeta := g.zeta_pos
    hzeta1 := g.zeta_one
    hworldSmall := fun w hw => (hgeometry.2.2.1 w (g.wlower w hw)).2.2.2
    hworldScales := g.cover
    Krow := N^(2*e)
    eta := eta
    Htarget := N^(ch*alpha)
    Kcap := N^(8*e)
    Cpure := N^h
    hCpure := Real.rpow_nonneg hNp.le _
    hKcap := Real.rpow_pos_of_pos hNp _
    hBKrow := Real.rpow_le_rpow_of_exponent_le hN.le (by linarith only [hae,ha,he])
    hRCKrow := hrow
    hFitEta := le_rfl
    hrowTarget := Real.rpow_le_rpow_of_exponent_le hN.le hNative
    floorStart := g.floorStart
    floorCount := g.floorCount
    floorExponent := a/(10000*E)
    incidence := inc
    hincResolution := rfl
    paletteFinest := g.paletteFinest
    hincFinest := g.incFinest
    hregFinest := g.regFinest
    hstateD := le_rfl
    T := T
    hTlo := htime.1
    hThi := htime.2
    hζT := hcutoff
    mesh := mesh
    err := err
    duration := duration
    bound := bound
    hmesh := hmesh
    hbound := hbound
    herror := herror
    hduration := hduration
  }

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel
