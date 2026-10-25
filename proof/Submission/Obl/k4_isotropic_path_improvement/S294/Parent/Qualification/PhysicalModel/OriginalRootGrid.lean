-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.OriginalRootGrid, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.RootDyadicScales

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel

open Set MeasureTheory
open Jets2

noncomputable section

/-- The actual finite original grids used by root preparation. Their
two snapshot counts are fixed before the sample. The support widths
alone may have logarithmic cardinality. -/
structure OriginalRootGrid (b : ℝ) (regIntervals resIntervals : ℕ) where
  rho : ℝ
  zeta : ℝ
  worldLevel : ℕ
  rho_eq : rho=dyadicParameterWidth worldLevel
  rho_pos : 0<rho
  rho_one : rho≤1
  zeta_pos : 0<zeta
  zeta_one : zeta≤1
  rho_zeta : rho≤zeta
  fineLevel : ℕ
  b_eq : b=dyadicParameterWidth fineLevel
  regStep : ℕ
  regStep_pos : 0<regStep
  regWidth : ∀ i<regIntervals+1,
    dyadicParameterWidth (i*regStep)=b*(2:ℝ)^(fineLevel-i*regStep)
  regFine : ∀ i<regIntervals+1, b≤dyadicParameterWidth (i*regStep)
  regRatio : ∀ i, dyadicParameterWidth (i*regStep)=
    (2:ℝ)^regStep*dyadicParameterWidth ((i+1)*regStep)
  regFloor : dyadicParameterWidth (regIntervals*regStep)≤rho
  regLower : rho/(2:ℝ)^(regIntervals+1)≤dyadicParameterWidth (regIntervals*regStep)
  regIndex : regIntervals*regStep≤worldLevel+regIntervals+1
  resStep : ℕ
  resStep_pos : 0<resStep
  resRatio : ∀ i, dyadicParameterWidth (i*resStep)=
    (2:ℝ)^resStep*dyadicParameterWidth ((i+1)*resStep)
  resFloor : dyadicParameterWidth (resIntervals*resStep)≤zeta
  resLower : zeta/(2:ℝ)^(resIntervals+1)≤dyadicParameterWidth (resIntervals*resStep)
  resIndex : resIntervals*resStep≤parameterLevel zeta+resIntervals
  lastLevel : ℕ
  lastLevel_eq : lastLevel=max (resIntervals*resStep) (parameterLevel zeta)
  resMax : ∀ i<resIntervals+1, i*resStep≤lastLevel
  queryMax : parameterLevel zeta≤lastLevel
  floorStart : ℕ
  floorCount : ℕ
  floorCount_pos : 0<floorCount
  floorStart_world : floorStart≤worldLevel
  floorEnd : worldLevel+lastLevel<floorStart+floorCount
  paletteFinest : ℕ
  paletteFinest_eq : paletteFinest=worldLevel+lastLevel+(regIntervals+1)+2
  floorFinest : floorStart+floorCount-1=paletteFinest
  regFinest : ∀ i<regIntervals+1, i*regStep≤paletteFinest
  incFinest : worldLevel+lastLevel≤paletteFinest
  floorResolved : b≤dyadicParameterWidth paletteFinest
  W : Finset ℝ
  fineSteps : ℝ→ℕ
  columnSteps : ℝ→ℕ
  card : W.card≤parameterLevel zeta+1
  width : ∀ w∈W, w=b*(2:ℝ)^(fineSteps w)
  column : ∀ w∈W, rho=w*(2:ℝ)^(columnSteps w)
  bw : ∀ w∈W, b≤w
  wrho : ∀ w∈W, w≤rho
  wlower : ∀ w∈W, rho*zeta/2≤w
  cover : ∀ r : ℝ, zeta≤r → r≤1 → ∃ w∈W, w≤rho*r ∧ rho*r≤2*w

/-- Assemble all exact original grids from the two sparse snapshot
sequences and a sufficiently fine original graph mesh. -/
theorem exists_original_root_grid_of_sparse_scales
    (fine world start regIntervals regStep resIntervals resStep : ℕ)
    {zeta : ℝ} (hzeta : 0<zeta) (hzeta1 : zeta≤1)
    (hrhozeta : dyadicParameterWidth world≤zeta)
    (hregStep : 0<regStep)
    (hregRatio : ∀ i, dyadicParameterWidth (i*regStep)=
      (2:ℝ)^regStep*dyadicParameterWidth ((i+1)*regStep))
    (hregFloor : dyadicParameterWidth (regIntervals*regStep)≤dyadicParameterWidth world)
    (hregLower : dyadicParameterWidth world/(2:ℝ)^(regIntervals+1)≤
      dyadicParameterWidth (regIntervals*regStep))
    (hregIndex : regIntervals*regStep≤world+regIntervals+1)
    (hresStep : 0<resStep)
    (hresRatio : ∀ i, dyadicParameterWidth (i*resStep)=
      (2:ℝ)^resStep*dyadicParameterWidth ((i+1)*resStep))
    (hresFloor : dyadicParameterWidth (resIntervals*resStep)≤zeta)
    (hresLower : zeta/(2:ℝ)^(resIntervals+1)≤dyadicParameterWidth (resIntervals*resStep))
    (hresIndex : resIntervals*resStep≤parameterLevel zeta+resIntervals)
    (hstart : start≤world)
    (hfine : world+max (resIntervals*resStep) (parameterLevel zeta)+(regIntervals+1)+2≤fine) :
    ∃ g : OriginalRootGrid (dyadicParameterWidth fine) regIntervals resIntervals,
      g.worldLevel=world ∧ g.zeta=zeta ∧ g.regStep=regStep ∧ g.resStep=resStep ∧
      g.floorStart=start ∧ g.fineLevel=fine := by
  let last := max (resIntervals*resStep) (parameterLevel zeta)
  let lastFloor := world+last+(regIntervals+1)+2
  have hfloorFine : lastFloor≤fine := hfine
  have hstartFloor : start≤lastFloor := by dsimp only [lastFloor]; omega
  have hregFine : regIntervals*regStep≤fine := by dsimp only [lastFloor] at hfloorFine; omega
  have hworldFine : world+parameterLevel zeta≤fine := by
    have hh := le_max_right (resIntervals*resStep) (parameterLevel zeta)
    dsimp only [lastFloor,last] at hfloorFine
    omega
  obtain ⟨W,fineSteps,columnSteps,hcard,hwidth,hcolumn,hbw,hwrho,hwlower,hcover⟩ :=
    exists_world_support_at_dyadic_mesh hzeta hzeta1 fine world hworldFine
  have hreg := sparse_regular_grid_at_mesh fine regIntervals regStep hregFine
  refine ⟨{
    rho := dyadicParameterWidth world
    zeta := zeta
    worldLevel := world
    rho_eq := rfl
    rho_pos := dyadicParameterWidth_pos world
    rho_one := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
    zeta_pos := hzeta
    zeta_one := hzeta1
    rho_zeta := hrhozeta
    fineLevel := fine
    b_eq := rfl
    regStep := regStep
    regStep_pos := hregStep
    regWidth := hreg.1
    regFine := hreg.2
    regRatio := hregRatio
    regFloor := hregFloor
    regLower := hregLower
    regIndex := hregIndex
    resStep := resStep
    resStep_pos := hresStep
    resRatio := hresRatio
    resFloor := hresFloor
    resLower := hresLower
    resIndex := hresIndex
    lastLevel := last
    lastLevel_eq := rfl
    resMax := ?_
    queryMax := le_max_right _ _
    floorStart := start
    floorCount := lastFloor-start+1
    floorCount_pos := Nat.succ_pos _
    floorStart_world := hstart
    floorEnd := ?_
    paletteFinest := lastFloor
    paletteFinest_eq := rfl
    floorFinest := by omega
    regFinest := ?_
    incFinest := by dsimp only [lastFloor]; omega
    floorResolved := dyadicParameterWidth_antitone hfloorFine
    W := W
    fineSteps := fineSteps
    columnSteps := columnSteps
    card := hcard
    width := hwidth
    column := hcolumn
    bw := hbw
    wrho := hwrho
    wlower := hwlower
    cover := hcover
  },rfl,rfl,rfl,rfl,rfl,rfl⟩
  · intro i hi
    exact (Nat.mul_le_mul_right resStep (by omega)).trans (le_max_left _ _)
  · dsimp only [lastFloor]
    omega
  · intro i hi
    have hh := (Nat.mul_le_mul_right regStep (by omega : i≤regIntervals)).trans hregIndex
    dsimp only [lastFloor]
    omega

/-- The last query width has only the fixed sparse-grid rounding cost. -/
theorem OriginalRootGrid.last_width_lower {b : ℝ} {nr ns : ℕ}
    (g : OriginalRootGrid b nr ns) :
    g.zeta/(2:ℝ)^(ns+1)≤dyadicParameterWidth g.lastLevel := by
  rw [g.lastLevel_eq]
  by_cases h : parameterLevel g.zeta≤ns*g.resStep
  · rw [max_eq_left h]
    exact g.resLower
  · rw [max_eq_right (by omega : ns*g.resStep≤parameterLevel g.zeta)]
    have hp : (2:ℝ)≤(2:ℝ)^(ns+1) := by
      simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2)
        (by omega : 1≤ns+1)
    exact (div_le_div_of_nonneg_left g.zeta_pos.le (by norm_num) hp).trans
      (parameterLevel_width g.zeta g.zeta_pos g.zeta_one).1

/-- The entire coefficient floor grid has only fixed dyadic rounding
beyond the two polynomial scalar cutoffs. -/
theorem OriginalRootGrid.floor_width_lower {b : ℝ} {nr ns : ℕ}
    (g : OriginalRootGrid b nr ns) :
    g.rho*g.zeta/(2:ℝ)^(nr+ns+4)≤dyadicParameterWidth g.paletteFinest := by
  have heq : dyadicParameterWidth g.paletteFinest=
      g.rho*dyadicParameterWidth g.lastLevel*dyadicParameterWidth (nr+3) := by
    rw [g.paletteFinest_eq,
      show g.worldLevel+g.lastLevel+(nr+1)+2=(g.worldLevel+g.lastLevel)+(nr+3) by omega,
      dyadicParameterWidth_add,dyadicParameterWidth_add,←g.rho_eq]
  rw [heq]
  calc
    _=g.rho*(g.zeta/(2:ℝ)^(ns+1))*dyadicParameterWidth (nr+3) := by
      rw [show nr+ns+4=(ns+1)+(nr+3) by omega,pow_add]
      simp only [dyadicParameterWidth,div_eq_mul_inv,mul_inv_rev]
      ring
    _≤_ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left g.last_width_lower g.rho_pos.le) (dyadicParameterWidth_pos _).le

/-- Counts are logarithmic scalar counts plus fixed interval counts. -/
theorem OriginalRootGrid.floor_count_bound {b : ℝ} {nr ns : ℕ}
    (g : OriginalRootGrid b nr ns) :
    g.floorCount≤g.worldLevel+parameterLevel g.zeta+nr+ns+4 := by
  have hc := g.floorCount_pos
  have hf := g.floorFinest
  have hp := g.paletteFinest_eq
  have hr := g.resIndex
  have hl := g.lastLevel_eq
  have hmax : g.lastLevel≤parameterLevel g.zeta+ns := by
    rw [hl]
    exact max_le hr (by omega)
  omega

/-- The exact world index is controlled by the same original scalar
cutoff count, including dyadic endpoints. -/
theorem OriginalRootGrid.world_level_bound {b : ℝ} {nr ns : ℕ}
    (g : OriginalRootGrid b nr ns) : g.worldLevel≤parameterLevel g.rho := by
  have hh : dyadicParameterWidth (parameterLevel g.rho)≤dyadicParameterWidth g.worldLevel :=
    (parameterLevel_width g.rho g.rho_pos g.rho_one).2.trans_eq g.rho_eq
  exact (dyadicParameterWidth_le_iff _ _).mp hh

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel
