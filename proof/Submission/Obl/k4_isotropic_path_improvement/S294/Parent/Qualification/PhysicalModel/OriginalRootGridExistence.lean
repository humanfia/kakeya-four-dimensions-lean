-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.OriginalRootGridExistence, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.OriginalRootGrid
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.NativeClockCutoffs
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.DyadicGridCount

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel

open Set Filter MeasureTheory
open Jets2

noncomputable section

/-- Fixed exponent comparisons for the actual original grids. No
sample, measure, coefficient table or source occurs in this profile. -/
structure OriginalRootGridPowers where
  lower : ℝ
  upper : ℝ
  D : ℝ
  margin : ℝ
  lower_pos : 0 < lower
  upper_lower : lower ≤ upper
  D_one : 1 ≤ D
  margin_pos : 0 < margin
  rhoPower : ℕ
  rhoPower_one : 1 ≤ rhoPower
  regIntervals : ℕ
  resIntervals : ℕ
  regIntervals_pos : 0 < regIntervals
  resIntervals_pos : 0 < resIntervals
  regRatio : ℝ
  resRatio : ℝ
  regRatio_pos : 0 < regRatio
  resRatio_pos : 0 < resRatio
  regRoom : (rhoPower:ℝ)*(upper*D+margin)+margin < regRatio*(regIntervals:ℝ)
  resRoom : upper*D+margin < resRatio*(resIntervals:ℝ)
  start : ℝ
  target : ℝ
  count : ℝ
  start_pos : 0 < start
  startRoom : start < (rhoPower:ℝ)*lower*D
  targetRoom : ((rhoPower:ℝ)*(upper*D+margin)+margin)+(upper*D+margin)+margin < target
  count_pos : 0 < count

def OriginalRootGridPowers.zetaExponent (p : OriginalRootGridPowers) : ℝ := p.upper*p.D+p.margin
def OriginalRootGridPowers.rhoExponent (p : OriginalRootGridPowers) : ℝ :=
  (p.rhoPower:ℝ)*p.zetaExponent+p.margin
def OriginalRootGridPowers.floorExponent (p : OriginalRootGridPowers) : ℝ :=
  p.rhoExponent+p.zetaExponent+p.margin

/-- Uniform actual finite grids, chosen at the original child clock
and the actual dyadic graph mesh. All lower floors, query counts and
sparse ratios fit fixed pre-data polynomial powers. -/
theorem eventually_exists_original_root_grid
    (N : ℕ→ℝ) (hN : Tendsto N atTop atTop) (p : OriginalRootGridPowers) :
    ∀ᶠ k in atTop, ∀ T : ℕ,
      p.lower ≤ nativeClockExponent (N k) T → nativeClockExponent (N k) T ≤ p.upper →
      ∀ fine : ℕ, dyadicParameterWidth fine ≤ (N k)^(-p.target) →
      ∃ g : OriginalRootGrid (dyadicParameterWidth fine) p.regIntervals p.resIntervals,
        g.floorStart=parameterLevel ((N k)^(-p.start)) ∧
        g.zeta ≤ (((2:ℝ)^T)⁻¹)^p.D ∧
        (N k)^(-p.zetaExponent) ≤ g.zeta ∧ g.zeta ≤ (N k)^(-(p.lower*p.D)) ∧
        (N k)^(-p.rhoExponent) ≤ g.rho ∧ g.rho ≤ (N k)^(-((p.rhoPower:ℝ)*p.lower*p.D)) ∧
        (N k)^(-p.floorExponent) ≤ dyadicParameterWidth g.paletteFinest ∧
        (N k)^(-(p.zetaExponent+p.margin)) ≤ dyadicParameterWidth g.lastLevel ∧
        (2:ℝ)^g.regStep ≤ (N k)^p.regRatio ∧
        (2:ℝ)^g.resStep ≤ (N k)^p.resRatio ∧
        (g.floorCount:ℝ) ≤ (N k)^p.count ∧ (g.W.card:ℝ) ≤ (N k)^p.count := by
  have hD : 0 < p.D := zero_lt_one.trans_le p.D_one
  have hupper : 0 < p.upper := p.lower_pos.trans_le p.upper_lower
  have hmpos := p.margin_pos
  have hZ : 0 < p.zetaExponent := by unfold OriginalRootGridPowers.zetaExponent; positivity
  have hR : 0 < p.rhoExponent := by unfold OriginalRootGridPowers.rhoExponent; positivity
  have hregRoom : p.rhoExponent < p.regRatio*(p.regIntervals:ℝ) := p.regRoom
  have hresRoom : p.zetaExponent < p.resRatio*(p.resIntervals:ℝ) := p.resRoom
  have hstartGap : 0 < (p.rhoPower:ℝ)*p.lower*p.D-p.start := sub_pos.mpr p.startRoom
  have hSparseReg := eventually_sparse_scales_at_length N hN p.regRatio_pos p.regIntervals
    p.regIntervals_pos hregRoom
  have hSparseRes := eventually_sparse_scales_at_length N hN p.resRatio_pos p.resIntervals
    p.resIntervals_pos hresRoom
  have hMargin := ((tendsto_rpow_atTop p.margin_pos).comp hN).eventually_ge_atTop
    ((2:ℝ)^(p.regIntervals+p.resIntervals+4))
  have hStart := ((tendsto_rpow_atTop hstartGap).comp hN).eventually_ge_atTop 2
  have hCountR := eventually_parameterLevel_add_one_le N hN hR.le (half_pos p.count_pos)
  have hCountZ := eventually_parameterLevel_add_one_le N hN hZ.le (half_pos p.count_pos)
  have hCountFixed := ((tendsto_rpow_atTop (half_pos p.count_pos)).comp hN).eventually_ge_atTop
    (max 4 ((p.regIntervals+p.resIntervals+4:ℕ):ℝ))
  filter_upwards [hN.eventually_gt_atTop 1,hSparseReg,hSparseRes,hMargin,hStart,
    hCountR,hCountZ,hCountFixed] with k hk hReg hRes hmargin hstart hcountR hcountZ hfixed
  have hNp : 0 < N k := zero_lt_one.trans hk
  change (2:ℝ)^(p.regIntervals+p.resIntervals+4) ≤ (N k)^p.margin at hmargin
  change 2 ≤ (N k)^((p.rhoPower:ℝ)*p.lower*p.D-p.start) at hstart
  change max 4 ((p.regIntervals+p.resIntervals+4:ℕ):ℝ) ≤ (N k)^(p.count/2) at hfixed
  have hmargin2 : 2 ≤ (N k)^p.margin := by
    have hh : (2:ℝ) ≤ (2:ℝ)^(p.regIntervals+p.resIntervals+4) := by
      simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2)
        (by omega : 1 ≤ p.regIntervals+p.resIntervals+4)
    exact hh.trans hmargin
  intro T hclockLo hclockHi fine hfine
  obtain ⟨zeta,world,hzeta,hzeta1,hzetaClock,hzetaLo,hzetaHi,hrhoLo,hrhoHi,hrhozeta⟩ :=
    exists_native_clock_cutoffs hk T p.lower_pos p.D_one hclockLo hclockHi
      p.rhoPower p.rhoPower_one hmargin2
  change (N k)^(-p.zetaExponent) ≤ zeta at hzetaLo
  change (N k)^(-p.rhoExponent) ≤ dyadicParameterWidth world at hrhoLo
  let rho := dyadicParameterWidth world
  have hrho : 0 < rho := dyadicParameterWidth_pos world
  have hrho1 : rho ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  obtain ⟨regStep,hregStep,hregRatio,hregA,hregFloor,hregLower,hregLast⟩ :=
    hReg rho hrhoLo hrho1
  obtain ⟨resStep,hresStep,hresRatio,hresA,hresFloor,hresLower,hresLast⟩ :=
    hRes zeta hzetaLo hzeta1
  have hregIndex : p.regIntervals*regStep ≤ world+p.regIntervals+1 := by
    have hh := parameterLevel_dyadic_upper world
    dsimp only [rho] at hregLast
    omega
  let start := parameterLevel ((N k)^(-p.start))
  have hstartQuery : (N k)^(-p.start) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hk.le (by linarith [p.start_pos])
  have hstartWidth := parameterLevel_width ((N k)^(-p.start))
    (Real.rpow_pos_of_pos hNp _) hstartQuery
  have hstartWorld : start ≤ world := by
    apply (dyadicParameterWidth_le_iff world start).mp
    calc
      _ ≤ (N k)^(-((p.rhoPower:ℝ)*p.lower*p.D)) := hrhoHi
      _=(N k)^(-p.start)/(N k)^((p.rhoPower:ℝ)*p.lower*p.D-p.start) := by
        rw [←Real.rpow_sub hNp]
        congr 1
        ring
      _ ≤ (N k)^(-p.start)/2 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hstart
      _ ≤ _ := hstartWidth.1
  let last := max (p.resIntervals*resStep) (parameterLevel zeta)
  let endpoint := world+last+(p.regIntervals+1)+2
  obtain ⟨g0,hw0,hz0,hr0,hs0,hstart0,hfine0⟩ := exists_original_root_grid_of_sparse_scales
    endpoint world start p.regIntervals regStep p.resIntervals resStep hzeta hzeta1 hrhozeta
    hregStep hregRatio hregFloor hregLower hregIndex hresStep hresRatio hresFloor hresLower
    hresLast hstartWorld le_rfl
  have hrho0 : g0.rho=rho := by rw [g0.rho_eq,hw0]
  have hend0 : g0.paletteFinest=endpoint := by
    rw [g0.paletteFinest_eq,g0.lastLevel_eq,hw0,hz0,hs0]
  have hproduct : (N k)^(-(p.rhoExponent+p.zetaExponent)) ≤ rho*zeta := by
    calc
      _=(N k)^(-p.rhoExponent)*(N k)^(-p.zetaExponent) := by
        rw [←Real.rpow_add hNp]
        congr 1
        ring
      _ ≤ _ := mul_le_mul hrhoLo hzetaLo (by positivity) hrho.le
  have hfloorLower : (N k)^(-p.floorExponent) ≤ dyadicParameterWidth endpoint := by
    calc
      _=(N k)^(-(p.rhoExponent+p.zetaExponent))/(N k)^p.margin := by
        rw [←Real.rpow_sub hNp]
        congr 1
        unfold OriginalRootGridPowers.floorExponent
        ring
      _ ≤ (N k)^(-(p.rhoExponent+p.zetaExponent))/(2:ℝ)^(p.regIntervals+p.resIntervals+4) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hmargin
      _ ≤ rho*zeta/(2:ℝ)^(p.regIntervals+p.resIntervals+4) :=
        div_le_div_of_nonneg_right hproduct (by positivity)
      _=g0.rho*g0.zeta/(2:ℝ)^(p.regIntervals+p.resIntervals+4) := by rw [hrho0,hz0]
      _ ≤ dyadicParameterWidth g0.paletteFinest := g0.floor_width_lower
      _=_ := congrArg dyadicParameterWidth hend0
  have hactualFine : endpoint ≤ fine := by
    apply (dyadicParameterWidth_le_iff _ _).mp
    calc
      dyadicParameterWidth fine ≤ (N k)^(-p.target) := hfine
      _ ≤ (N k)^(-p.floorExponent) := Real.rpow_le_rpow_of_exponent_le hk.le
        (by have hh := p.targetRoom; change p.floorExponent < p.target at hh; linarith)
      _ ≤ _ := hfloorLower
  obtain ⟨g,hw,hz,hr,hs,hstartEq,hfineEq⟩ := exists_original_root_grid_of_sparse_scales
    fine world start p.regIntervals regStep p.resIntervals resStep hzeta hzeta1 hrhozeta
    hregStep hregRatio hregFloor hregLower hregIndex hresStep hresRatio hresFloor hresLower
    hresLast hstartWorld hactualFine
  have hrhoEq : g.rho=rho := by rw [g.rho_eq,hw]
  have hend : g.paletteFinest=endpoint := by
    rw [g.paletteFinest_eq,g.lastLevel_eq,hw,hz,hs]
  have hR : (N k)^(-p.rhoExponent) ≤ g.rho := by simpa only [hrhoEq] using hrhoLo
  have hZ : (N k)^(-p.zetaExponent) ≤ g.zeta := by simpa only [hz] using hzetaLo
  have hcountρ := hcountR g.rho hR g.rho_one
  have hcountζ := hcountZ g.zeta hZ g.zeta_one
  let X := (N k)^(p.count/2)
  have hX4 : 4 ≤ X := (le_max_left _ _).trans hfixed
  have hXfixed : ((p.regIntervals+p.resIntervals+4:ℕ):ℝ) ≤ X := (le_max_right _ _).trans hfixed
  have hXeq : X^2=(N k)^p.count := by
    dsimp only [X]
    rw [←Real.rpow_mul_natCast hNp.le]
    congr 1
    ring
  have hcountNat : g.floorCount ≤ parameterLevel g.rho+parameterLevel g.zeta+
      (p.regIntervals+p.resIntervals+4) := by
    have hh := g.floor_count_bound
    have hw' := g.world_level_bound
    omega
  have hcountReal : (g.floorCount:ℝ) ≤ (parameterLevel g.rho:ℝ)+(parameterLevel g.zeta:ℝ)+
      ((p.regIntervals+p.resIntervals+4:ℕ):ℝ) := by exact_mod_cast hcountNat
  have hcountReal' : (g.floorCount:ℝ) ≤ (N k)^p.count := by
    push_cast at hcountρ hcountζ
    rw [←hXeq]
    change (parameterLevel g.rho:ℝ)+1 ≤ X at hcountρ
    change (parameterLevel g.zeta:ℝ)+1 ≤ X at hcountζ
    nlinarith only [hcountReal,hcountρ,hcountζ,hXfixed,hX4]
  have hcardReal : (g.W.card:ℝ) ≤ (N k)^p.count := by
    have hc : (g.W.card:ℝ) ≤ ((parameterLevel g.zeta+1:ℕ):ℝ) := by exact_mod_cast g.card
    have hh := hc.trans hcountζ
    rw [←hXeq]
    change (g.W.card:ℝ) ≤ X at hh
    nlinarith only [hh,hX4]
  have hlastPower : (N k)^(-(p.zetaExponent+p.margin)) ≤ dyadicParameterWidth g.lastLevel := by
    have hden : (2:ℝ)^(p.resIntervals+1) ≤ (N k)^p.margin :=
      (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega)).trans hmargin
    calc
      _=(N k)^(-p.zetaExponent)/(N k)^p.margin := by
        rw [←Real.rpow_sub hNp]
        congr 1
        ring
      _ ≤ (N k)^(-p.zetaExponent)/(2:ℝ)^(p.resIntervals+1) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ ≤ g.zeta/(2:ℝ)^(p.resIntervals+1) := div_le_div_of_nonneg_right hZ (by positivity)
      _ ≤ _ := g.last_width_lower
  refine ⟨g,hstartEq,?_,hZ,?_,hR,?_,?_,hlastPower,?_,?_,hcountReal',hcardReal⟩
  · simpa only [hz] using hzetaClock
  · simpa only [hz] using hzetaHi
  · simpa only [hrhoEq] using hrhoHi
  · simpa only [hend] using hfloorLower
  · simpa only [hr] using hregA
  · simpa only [hs] using hresA

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel
