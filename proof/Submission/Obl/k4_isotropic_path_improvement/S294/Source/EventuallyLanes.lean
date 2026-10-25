-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.EventuallyLanes, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.FinalTune
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleRecordBlock
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleRecordScalarBlock
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleStateBlock
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleMassBlock
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleRecordStateEventual
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeSampleScaleBlock
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeSampleScalarBlock
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeScaleAtPath
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeAuxiliaryScaleBounds
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.MK4MeshBounds
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeListGeometryRate
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.ListLane
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeScaleAtSample
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleFamilyAtChoices
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeSamplePowersAtChoices
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeListScaleBlock
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.CensusMassBudgets
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeCensusPowerBudgets
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleAtNumerics

/-!
# The lanes hold eventually (session x1082)

`eventually_lanes : LanesEventually finalTune`: after the pre-sample choices of `StagesProducer`,
at every late sample and every path exponent below one `σL`, the lanes of `sample_final`
(`Source.LaneData`) are supplied by the record/state/mass blocks (x1095), the native scale
factory and its callback (x1096) and the list block.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Set MeasureTheory Filter
open Parent.ParentSource
open Parent.ParentSource.Native (ProblemData PathData PreparedAngularPath PaletteFamily BroadResidual
  likelihoodGood labelledSupport finitePacketHistory labelledVelocityPalette)
open scoped ENNReal

noncomputable section

set_option maxHeartbeats 8000000 in
/-- **The lanes hold eventually.** -/
theorem eventually_lanes : LanesEventually finalTune := by
  intro hmk d₁ κ₁ ρ Ep precision loss e0 hd₀ hd₁ hκ hκ1 hρ hdρ hprec hloss hloss1 he0
    m s δ₀ C target indices hgrid hδtol hδm hm8 hgm htarget hstarget hm2 hC1 hCge hCle hCt hind
    d hd hprof Mp Dp budget hbud hbud1
  set gain := gainOf finalTune κ₁ d₁ Ep precision loss e0 with hgaindef
  have hv : NativeDesign.Valid κ₁ d₁ precision loss := ⟨hd₀, hd₁, hκ, hκ1, hprec, hloss, hloss1⟩
  have hL : 0 < d.L := hd.2.2.2.1
  have hNt : Tendsto d.N atTop atTop := hd.2.1
  have hgain : 0 < gain := gainOf_pos (tune := finalTune) (Ep := Ep) hκ hd₁ hprec hloss he0
  have hgainCap : gain ≤ gainCap finalTune κ₁ d₁ Ep precision loss := gainOf_le_cap
  -- the grid
  have hm : 0 < m := by omega
  have hs : ∀ l, s l = ((l : ℝ) + 1) / m := hgrid.2.2.2.2.2.2.2.1
  have hδpos : 0 < δ₀ := hgrid.2.2.2.1
  have hδ0 : 0 ≤ δ₀ := hδpos.le
  have hδg : δ₀ ≤ gain / 100 := hgrid.2.2.2.2.2.2.2.2.2.1
  have hδu0 : δ₀ ≤ (ubOf finalTune κ₁ d₁ Ep precision loss gain / 8) / 100 :=
    hgrid.2.2.2.2.2.2.2.2.2.2.1
  have hgm' : 8 ≤ gain * (m : ℝ) := by
    have := gridFineOf_le_gain finalTune hloss hloss1 hgain (κ₁ := κ₁) (d₁ := d₁) (Ep := Ep)
      (precision := precision)
    have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  -- the native design
  set q : NativeScaleDesign := ⟨κ₁, d₁, Ep, precision, loss, gain * d.L, hv, mul_pos hgain hL⟩
    with hqdef
  obtain ⟨Cmk, hCmk, hMK⟩ := hmk 3 (by norm_num) (by norm_num)
  -- the eventual suppliers
  obtain ⟨σ1, hσ1, -, hσ1c, hE1⟩ := eventually_sample_record_state_block_facts finalTune
    finalTune_slack d.N hNt (96 * coreRowK₀) (Ep := Ep) (m := m) (C := C) hv hgain hL hgainCap hm
    hgm' hδ0 hδg hδtol hδu0 hCle hbud le_rfl (by norm_num)
  obtain ⟨σ2, hσ2, -, hE2⟩ := eventually_native_sample_scale_data finalTune finalTune_censusSlack d hd
    q rfl hgain hδpos hδg rfl hδtol hgm hs Cmk hCmk.le hMK
  obtain ⟨σ3, hσ3, -, hE3⟩ := eventually_native_sample_power_bounds_at_choices finalTune d.N hNt
    (Ep := Ep) (m := m) hv rfl hgain hL hδpos finalTune_censusSlack hδtol hgm hbud
  obtain ⟨σ4, hσ4, -, hE4⟩ := eventually_sample_census_mass_budget finalTune finalTune_slack d.N hNt m
    (κ₁ := κ₁) (d₁ := d₁) (precision := precision) (Ep := Ep) hloss hgain hL hδpos hbud
    (by norm_num : (0 : ℝ) < 1) (by norm_num) hδtol
  obtain ⟨σ5, hσ5, -, hE5⟩ := eventually_geom_le d.N hNt hδpos hL
  set σL := min σ1 (min σ2 (min σ3 (min σ4 σ5))) with hσLdef
  have hσL0 : 0 < σL := lt_min hσ1 (lt_min hσ2 (lt_min hσ3 (lt_min hσ4 hσ5)))
  have hσL1 : σL ≤ σ1 := min_le_left _ _
  have hσL2 : σL ≤ σ2 := (min_le_right _ _).trans (min_le_left _ _)
  have hσL3 : σL ≤ σ3 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hσL4 : σL ≤ σ4 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hσL5 : σL ≤ σ5 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨σL, hσL0, ?_⟩
  filter_upwards [hE1, hE2, hE3, hE4, hE5, hd.2.2.1.2 σL hσL0] with k hk1 hk2 hk3 hk4 hk5 hKdk
  intro σ hσ hσσL p hp H hHm hH hHmass Qp hpure hQres i hi Fp Rp hRmass hgood
  classical
  -- the problem and the path at the sample
  have hN2 : (2 : ℝ) ≤ d.N k := hd.1 k
  have hN1 : (1 : ℝ) < d.N k := by linarith
  have hNp : 0 < d.N k := by linarith
  have hκ1' : 1 ≤ p.κ := hp.1
  have hκσ : p.κ ≤ d.N k ^ σ := hp.2.1
  have hpowL : ∀ σ', σL ≤ σ' → d.N k ^ σL ≤ d.N k ^ σ' :=
    fun σ' h => Real.rpow_le_rpow_of_exponent_le hN1.le h
  have hκL : p.κ ≤ d.N k ^ σL := hκσ.trans (hpowL σL le_rfl |>.trans' (Real.rpow_le_rpow_of_exponent_le hN1.le hσσL))
  have hKd1 : 1 ≤ d.K k := hd.2.2.1.1 k
  have hHE : ∀ w, H w ⊆ d.E k w := hp.residual_subset_event H hH
  have hiC : i + C ≤ target := by rw [hind, Finset.mem_range] at hi; omega
  have hiCm : i + C < m := by omega
  let τ := tauOf finalTune δ₀ d.L budget
  have hτ0 : 0 ≤ τ := by
    show 0 ≤ tauOf finalTune δ₀ d.L budget
    unfold tauOf
    have := zero_le_one.trans finalTune.one_le_slack
    exact le_min (by positivity) (by positivity)
  have hτδ : τ ≤ δ₀ * d.L := min_le_left _ _
  set c := childOffset κ₁ Ep precision gain m with hcdef
  obtain ⟨hgC, hnfamEq, hcfam⟩ := sample_family_at_choices finalTune (Ep := Ep) (m := m) (C := C)
    (precision := precision) hv rfl hgain hδ0 hm hs finalTune_censusSlack hδtol hδg hgm' hCge
  have hcC : c ≤ C := by
    have := hcfam; rw [hnfamEq] at this; omega
  have hib : i + c < m := by omega
  -- the record/state facts at the sample
  obtain ⟨-, h24, h20000, hE1k⟩ := hk1
  obtain ⟨⟨hK2304, hKG, hmaxK, hNG, hconstG⟩, ⟨hstates, hpalPow⟩, hdisplayStrip, hwideStrip⟩ :=
    hE1k p.κ (d.K k) hκ1' (hκL.trans (hpowL _ hσL1)) (hKdk.trans (hpowL _ hσL1))
  -- the native scale data
  obtain ⟨native⟩ := hk2 σ (hσσL.trans hσL2) p Mp Dp hp budget hbud i hib
  -- the native point powers at the choices
  obtain ⟨hBrow, hcoeffH, hVmaxU, hCband, hgraphLower⟩ := hk3 p.κ (d.K k) hκ1' hKd1
    (hκL.trans (hpowL _ hσL3)) (hKdk.trans (hpowL _ hσL3))
  -- the census geometry
  have hgeom := hk5 p.κ (d.K k) τ hκ1' (hκL.trans (hpowL _ hσL5)) (hKdk.trans (hpowL _ hσL5)) hτ0 hτδ
  -- the records
  let ub := ubOf finalTune κ₁ d₁ Ep precision loss gain
  let nmesh := nmeshAt p.κ (d.K k) (d.N k) δ₀ d.L τ ub d₁ (thetaNAt κ₁ d₁ Ep precision gain (d.N k) d.L) m
  have hmesh0 : 0 < Submission.Lib.K4DyadicRowScales.mesh nmesh :=
    Submission.Lib.K4DyadicRowScales.mesh_pos nmesh
  have hmesh1 : Submission.Lib.K4DyadicRowScales.mesh nmesh ≤ 1 :=
    (Submission.Lib.K4DyadicRowScales.mesh_le_coarse nmesh).trans
      (Submission.Lib.K4DyadicRowScales.coarse_le_one nmesh)
  obtain ⟨jrec, baseRef, hiddenRef, hb0, hh0, -, hjstop, hwidthrec, hbaseSmall, hcoreSmall,
      hheightSmall, hgB, hgH, hauxB, hauxH, hphysB, hphysH⟩ :=
    sample_record_geometry_block finalTune hd hp (d₁ := d₁) (precision := precision) (loss := loss)
      (gain := gain) (divisor := 1) (τ := τ) (graphMesh := Submission.Lib.K4DyadicRowScales.mesh nmesh)
      (G := d.N k ^ (recordGeometryExponent finalTune κ₁ d₁ Ep precision loss gain 1 * d.L))
      (Ep := Ep) (i := i) (C := C) hv rfl hgain hL le_rfl hδ0 hδg hτ0 hm hgm' hs
      finalTune_censusSlack hδtol hCge hiCm hib hKG hNG le_rfl h24 hmesh0 hmesh1 hgraphLower
  obtain ⟨hcut0, hKcap0, hχ0, hbudgetRec, hCpure, hpalCoeff⟩ :=
    sample_record_scalar_block finalTune (N := d.N k) (κ := p.κ) (source := d.K k) (κ₁ := κ₁)
      (d₁ := d₁) (precision := precision) (loss := loss) (gain := gain) (L := d.L) (δ₀ := δ₀)
      (front := budget) (divisor := 1) (gap := σ1) (Ep := Ep) (m := m) (C := C)
      hv rfl hN1.le hgain hL hgainCap hm hgm' hδ0 hδg hδtol hCle hbud le_rfl (by norm_num) hκ1'
      (hκL.trans (hpowL _ hσL1)) (hKdk.trans (hpowL _ hσL1)) hσ1c h20000
  -- the states
  obtain ⟨radiusP, hrad0, hNormalizedWidth, hstripWidth, hOriginalWidth⟩ :=
    sample_state_strip_block finalTune hd hp (d₁ := d₁) (precision := precision) (loss := loss)
      (gain := gain) (Ep := Ep) (i := i) (c := c) hv rfl hgain hL hδ0 finalTune_censusSlack hδtol hgm
      hdisplayStrip hwideStrip
  obtain ⟨hpv0, hpvP, hbeta0, hbetaTop, hphysicalBase, hphysicalHidden, hstripRatio,
      hpaletteRatio⟩ :=
    sample_state_mesh_block finalTune hd hp (d₁ := d₁) (precision := precision) (loss := loss)
      (gain := gain) (front := budget) (Ep := Ep) (i := i) hv hgain hL hδ0 hδg hm hgm' hs (by omega)
      hib (by linarith) hstates hphysB hphysH
  -- the census constant, its steps and the MK4 fit at the choices
  have hτ2 : 2 * τ = τ + τ := two_mul τ
  have hcoreK : coreK p τ ≤ KgeomAt p.κ (d.K k) (d.N k) δ₀ d.L τ := (geomOf_ge).1
  have hKgeomN : KgeomAt p.κ (d.K k) (d.N k) δ₀ d.L τ ≤ d.N k ^ (3 * δ₀ * d.L) := by
    have h := hgeom; rw [hτ2] at h; exact h
  have hκcore : p.κ ≤ coreK p τ := (le_max_left _ _).trans hmaxK
  have hKgeom24 : 24 ≤ KgeomAt p.κ (d.K k) (d.N k) δ₀ d.L τ := by
    have := hcoreK; linarith
  have hKcen := censusK_ge (Kgeom := KgeomAt p.κ (d.K k) (d.N k) δ₀ d.L τ) (by linarith)
    FixedSourcePowers.coreRadius FixedSourcePowers.jet
    (stripExpOf (KgeomAt p.κ (d.K k) (d.N k) δ₀ d.L τ) p.κ (d.N k) δ₀ d.L (d.N k ^ (-(ub * d.L))))
    (rowExpOf FixedSourcePowers.coreRadius) (gapExpOf (KgeomAt p.κ (d.K k) (d.N k) δ₀ d.L τ) (d.N k) δ₀ d.L m)
  have hKcenN : KcenAt p.κ (d.K k) (d.N k) δ₀ d.L τ ub m ≤
      d.N k ^ ((NativeDesign.coefficientCoeff κ₁ d₁ Ep precision loss * (gain * d.L)) / 1000) :=
    native_sample_census_power_bound finalTune hv rfl hgain hL hδ0 finalTune_censusSlack hδtol hgm
      hN1.le hKgeom24 hκ1' (hκcore.trans hcoreK) (geomOf_ge).2.1 (by simpa only [mul_assoc] using hKgeomN)
  obtain ⟨-, hstepsN⟩ := native_census_steps_power_budget hN1.le
    (by have := NativeDesign.coefficientCoeff_pos κ₁ d₁ (Ep := Ep) (precision := precision) hloss; positivity)
    h20000 hKcen.1 hKcenN
  -- the MK4 parameters at the choices (as in `sample_at`)
  let θN := thetaNAt κ₁ d₁ Ep precision gain (d.N k) d.L
  have hgt : 0 < NativeDesign.graphTargetCoeff κ₁ d₁ Ep precision := by
    unfold NativeDesign.graphTargetCoeff
    have h1 := NativeDesign.floorEndCoeff_pos κ₁ d₁ (Ep := Ep) hprec
    have h2 := NativeDesign.clockCoeff_pos (Ep := Ep) hprec
    positivity
  have hθN0 : 0 < θN := Real.rpow_pos_of_pos hNp _
  have hθN1 : θN ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos hN1.le
    have : 0 ≤ NativeDesign.graphTargetCoeff κ₁ d₁ Ep precision * gain * d.L := by positivity
    linarith
  have hθNq : θN = d.N k ^ (-q.target) := by
    show d.N k ^ (-(NativeDesign.graphTargetCoeff κ₁ d₁ Ep precision * gain * d.L)) =
      d.N k ^ (-(NativeDesign.graphTargetCoeff κ₁ d₁ Ep precision * (gain * d.L)))
    rw [mul_assoc]
  have hκ0 : 0 < p.κ := by linarith
  have hcMK : 0 < p.κ⁻¹ / 512 := by positivity
  have hcMK1 : p.κ⁻¹ / 512 ≤ 1 := by
    have : p.κ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hκ1'
    linarith
  have hCband0 : 0 ≤ CbandAt p.κ (d.K k) (d.N k) δ₀ d.L τ d₁ := by
    unfold CbandAt
    have : 0 ≤ max p.κ (d.K k) := hκ0.le.trans (le_max_left _ _)
    positivity
  have hub0 : 0 ≤ ub := by
    show 0 ≤ ubOf finalTune κ₁ d₁ Ep precision loss gain
    unfold ubOf
    have := finalTune.budget_pos κ₁ d₁ Ep precision loss
    positivity
  obtain ⟨-, -, -, -, -, hcellRate, hdurationRate, -, hKgJ, -, -, -, -, -, -, -, -, -, -, -, -,
      hθ80N, -, -, -⟩ :=
    mk4_parameters (κ := p.κ) (Vmax := 2 * d.K k) (Kc := KcenAt p.κ (d.K k) (d.N k) δ₀ d.L τ ub m)
      (Cband := CbandAt p.κ (d.K k) (d.N k) δ₀ d.L τ d₁)
      (c := p.κ⁻¹ / 512) (cE := p.κ⁻¹ / 512) (ratio := 1 / 2000000000000) (θ := θN) (d := d₁)
      (N := d.N k) (δL := δ₀ * d.L) (frontRadius := d.N k ^ (-(ub * d.L))) (meshCap := 1)
      hκ1' (by linarith) hKcen.1 hCband0 hcMK hcMK1 hcMK hcMK1 (by norm_num) (by norm_num)
      hθN0 hθN1 hd₀ hd₁ hN1.le (by positivity) (Real.rpow_pos_of_pos hNp _)
      (Real.rpow_le_one_of_one_le_of_nonpos hN1.le (by
        have : 0 ≤ ub * d.L := by positivity
        linarith)) one_pos le_rfl
  have hKg1 : 1 ≤ KgAt p.κ (d.K k) (d.N k) δ₀ d.L τ ub d₁ m := by
    have h := hKgJ
    have h' : (1 : ℝ) ≤ 6 * (1 + 24 * p.κ + p.κ ^ 2 + 2 * d.K k) := by nlinarith
    exact h'.trans h
  have herror : 80 * KgAt p.κ (d.K k) (d.N k) δ₀ d.L τ ub d₁ m ^ 7 *
      Submission.Lib.K4DyadicRowScales.mesh nmesh ^ ((1 - d₁) / 24) ≤ d.N k ^ (-q.target) := by
    rw [← hθNq]; exact hθ80N
  -- the remaining scalar inputs of the native callback
  have hi' : i < m := by omega
  have hhalf : s i ≤ 1 / 2 := by
    rw [← hstarget, hs, hs]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg m)
    have : (i : ℝ) ≤ target := by exact_mod_cast (show i ≤ target by omega)
    linarith
  have hfineWidth := native_sample_palette_floor finalTune (Ep := Ep) hv rfl hN1.le hgain hL hδ0
    (κ₁ := κ₁) (d₁ := d₁) (precision := precision) (loss := loss) (L := d.L) (delta := δ₀)
  have hdepthAux := native_sample_auxiliary_depth_room finalTune hp (Ep := Ep) (i := i) hv rfl he0 hL
    hi' hhalf hδg
  have hrpos : ∀ l, l < m → 0 < p.r l := fun l hl => (hp.2.2.2.2.1 l hl).2.1
  have hrLe : ∀ l, l < m → p.r l ≤ d.L := by
    intro l hl
    have h := path_r_le hp hL hm hs hδm hκ1 (show l ≤ m - 1 by omega) (by omega)
    rw [hp.2.2.2.1] at h
    exact h
  have hTlb : p.T i ≤ p.T (i + c) := path_T_le hp hN1 hL hm hs hδm hκ (by omega) hib
  have hstripCoeff : ENNReal.ofReal ((8 * (2 * ((d.N k ^ budget) ^ 1)⁻¹)) /
      d.N k ^ (-RecordBudgets.cutExponent budget
        (finalTune.budget κ₁ d₁ Ep precision loss * (loss * gain * d.L / ((Ep : ℝ) + 1)) / 1))) /
      ENNReal.ofReal (d.N k ^ (-RecordBudgets.cutExponent budget
        (finalTune.budget κ₁ d₁ Ep precision loss * (loss * gain * d.L / ((Ep : ℝ) + 1)) / 1))) ≤
      ENNReal.ofReal (1 / 2 : ℝ) := by
    refine hstripRatio.trans ?_
    rw [show (1 / 2 : ℝ) = ((2 : ℝ))⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos (by norm_num)]
    rw [ENNReal.ofReal_ofNat, one_div]
    exact ENNReal.inv_le_inv.mpr (by norm_num)
  -- the native scalars, the list lane and the census mass
  have hscal := native_sample_scalar_block native (gain := gain) (L := d.L) rfl hκ1' hκσ
  have hKcore3 : coreK p τ ≤ d.N k ^ (3 * δ₀ * d.L) := hcoreK.trans hKgeomN
  obtain ⟨jmid, hmidb, hmida, hrmid, hrLmid, hwidthmid, hsmallList⟩ :=
    native_list_lane_of_scale_data finalTune finalTune_slack hd hp hs hδ0 hδm hgain rfl hgm' rfl hδtol
      native hib hcfam hτ0 rfl (O204.Tangent.δ_pos _ _) (by positivity) h20000 hKcore3 (by linarith)
      (aA := O204.Split.δ (d.N k) (p.r i)) (q := ((2 : ℝ) ^ p.T i)⁻¹)
  have hnfamm : nfamAt κ₁ δ₀ ub m C ≤ m := by rw [hnfamEq]; omega
  have hcensus := hk4 p.κ (d.K k) (2 * ((d.N k ^ budget) ^ 1)⁻¹) hκ1'
    (hκL.trans (hpowL _ hσL4)) (hKdk.trans (hpowL _ hσL4)) (by positivity)
    (by rw [pow_one, Real.rpow_neg hNp.le])
    (KgeomAt p.κ (d.K k) (d.N k) δ₀ d.L τ) (by rw [hτ2]; exact hcoreK)
    (nfamAt κ₁ δ₀ ub m C) hnfamm
  rw [hτ2] at hcensus
  have hKcenPos : 0 < KcenAt p.κ (d.K k) (d.N k) δ₀ d.L τ ub m := lt_of_lt_of_le one_pos hKcen.1
  have hrates : (KcenAt p.κ (d.K k) (d.N k) δ₀ d.L τ ub m *
        ((2 : ℝ) ^ stepsAt p.κ (d.K k) (d.N k) δ₀ d.L τ ub m) ^ 3) *
        cellRateAt p.κ (d.K k) (d.N k) δ₀ d.L τ ub m +
      durationRateAt p.κ (d.K k) * (3 * (1 + 24 * p.κ + p.κ ^ 2 + 2 * d.K k) + 3) * (7 : ℝ) ^ 4 ≤
      p.κ⁻¹ / 256 := by
    unfold cellRateAt durationRateAt
    have h1 : 0 < KcenAt p.κ (d.K k) (d.N k) δ₀ d.L τ ub m *
        ((2 : ℝ) ^ stepsAt p.κ (d.K k) (d.N k) δ₀ d.L τ ub m) ^ 3 := by positivity
    have h2 : 0 < (3 * (1 + 24 * p.κ + p.κ ^ 2 + 2 * d.K k) + 3) * (7 : ℝ) ^ 4 := by positivity
    rw [mul_div_cancel₀ _ h1.ne', show (p.κ⁻¹ / 512) / ((3 * (1 + 24 * p.κ + p.κ ^ 2 + 2 * d.K k) + 3) *
      (7 : ℝ) ^ 4) * (3 * (1 + 24 * p.κ + p.κ ^ 2 + 2 * d.K k) + 3) * (7 : ℝ) ^ 4 = p.κ⁻¹ / 512 by
        field_simp]
    linarith
  have hdisp : q.display = loss * gain * d.L / ((Ep : ℝ) + 1) := by
    show loss / ((Ep : ℝ) + 1) * (gain * d.L) = _
    ring
  have hstatesQ : RecordBudgets.StateBudgetsAt (d.N k) p.κ (coreK p τ)
      (RecordBudgets.cutExponent budget
        (finalTune.budget κ₁ d₁ Ep precision loss * (loss * gain * d.L / ((Ep : ℝ) + 1)) / 1))
      budget q.display
      (entropyOf C m (ueOf finalTune κ₁ d₁ Ep precision loss gain δ₀ d.L)) := by
    rw [hdisp]; exact hstates
  have hmass := sample_mass_block native hκ1' hκσ hstatesQ hKcenPos.le
    (by unfold cellRateAt; positivity) (by unfold durationRateAt; positivity)
    (by positivity) hrates hcensus
  rw [NativeScaleDesign.display_power_eq_KOf q (N := d.N k) (gain := gain) (L := d.L) rfl] at hmass
  refine ⟨{
    jrec := Fin.cast hnfamEq.symm jrec
    hjstop := hjstop
    hwidthrec := hwidthrec
    baseRef := baseRef
    hiddenRef := hiddenRef
    hbase := hb0
    hhidden := hh0
    hbaseSmall := hbaseSmall
    hcoreSmall := hcoreSmall
    hheightSmall := hheightSmall
    pv := d.N k ^ (-ueOf finalTune κ₁ d₁ Ep precision loss gain δ₀ d.L)
    paletteRatio := d.N k ^ entropyOf C m (ueOf finalTune κ₁ d₁ Ep precision loss gain δ₀ d.L)
    hRatio := Real.rpow_nonneg hNp.le _
    hOriginal := hgood
    χ := NativeDesign.auxiliaryChiCoeff κ₁ d₁ Ep precision loss * (gain * d.L)
    finest := (NativeDesign.auxiliaryFinest κ₁ d₁ Ep precision loss : ℝ)
    hχ := hχ0
    dimension' := d₁
    f₀ := d.f 0
    profileError := δ₀ * d.L
    Kcap := d.N k ^ ((NativeDesign.coefficientCoeff κ₁ d₁ Ep precision loss * (gain * d.L)) / 1000)
    hdim := hd₀
    hprofileRec := hprof
    hbudget := hbudgetRec
    cut := d.N k ^ (-RecordBudgets.cutExponent budget
      (finalTune.budget κ₁ d₁ Ep precision loss * (loss * gain * d.L / ((Ep : ℝ) + 1)) / 1))
    hcut := hcut0
    hbaseBudget := by
      unfold fineAt
      rw [div_mul_cancel₀ _ (by positivity)]
      exact hgB
    hhiddenBudget := by
      unfold fineAt
      rw [div_mul_cancel₀ _ (by positivity)]
      exact hgH
    betaR := ENNReal.ofReal (d.N k ^ (-RecordBudgets.cutExponent budget
      (finalTune.budget κ₁ d₁ Ep precision loss * (loss * gain * d.L / ((Ep : ℝ) + 1)) / 1)))
    hbetaR := hbeta0
    hbetaRTop := hbetaTop
    hratio := by
      refine hstripRatio.trans (le_of_eq ?_)
      rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
    hfinePv := hpv0
    pvP := pvOf Ep precision loss gain (d.N k) d.L (p.r i) (p.r (i + c)) (p.T i) (p.T (i + c))
    hpvP := hpvP
    hgraphBase := hgB
    hgraphHidden := hgH
    hphysicalBase := hphysicalBase
    hphysicalHidden := hphysicalHidden
    beta := ENNReal.ofReal (d.N k ^ (-RecordBudgets.cutExponent budget
      (finalTune.budget κ₁ d₁ Ep precision loss * (loss * gain * d.L / ((Ep : ℝ) + 1)) / 1)))
    hbeta := hbeta0
    hbetaTop := hbetaTop
    hstripWidth := hstripWidth
    hstripRatio := hstripRatio
    hpaletteRatio := hpaletteRatio
    radiusP := radiusP
    stripWidth := d.N k ^ (-(NativeDesign.coefficientCoeff κ₁ d₁ Ep precision loss * (gain * d.L)))
    hNormalizedWidth := hNormalizedWidth
    hOriginalWidth := hOriginalWidth
    Mq := q.degree
    Tq := p.T (i + c) - p.T i
    qmesh := native.scales.mesh
    qerror := thetaOf Ep precision loss gain (d.N k) d.L (p.r i) (p.r (i + c)) (p.T i) (p.T (i + c))
    qduration := native.scales.duration
    qbound := native.scales.bound
    Pfac := native.scales.regularityFactor
    chargeR := native.scales.regularityFactor * native.scales.supportLoss
    η := native.scales.nativeFailureBound
    hPfac := hscal.Pfac_ne_top
    hPfac0 := hscal.Pfac_ne_zero
    hchargeR := hscal.chargeR_ne_top
    hη := hscal.eta_ne_top
    Lp := native.scales.Lp
    ρ := native.scales.ρ
    hLp := hscal.Lp_nonneg
    jmid := jmid
    hmidb := hmidb
    hmida := hmida
    hrmid := hrmid
    hrLmid := hrLmid
    hwidthmid := hwidthmid
    hsmallList := hsmallList
    hqmesh := hscal.mesh_nonneg
    hqbound := hscal.bound_nonneg
    hcoeff := hscal.coefficient_cost
    herror := le_rfl
    hduration := fun b hb => native_sample_duration_at_child hp native rfl rfl hTlb b hb
    chargeN := native.pre.charge
    hchargeN := hscal.preCharge_ne_top
    hnative := fun C => native_root_step_of_scale_data hd hpure hp hHE hH (core := C) native hN1
      (by omega) rfl hKg1 hBrow rfl herror rfl hstepsN hgraphLower (by positivity)
      (residual_velocity_le Qp Rp) hcoeffH hVmaxU radiusP _ hstripCoeff hpalCoeff hpv0 hfineWidth
      (by omega) (hrpos i hi').le (hrLe i hi') hdepthAux hauxB hauxH (Real.rpow_nonneg hNp.le _)
      hcut0 hKcap0.le hCpure hprof hCband
    hreserve := hmass
    Mq_eq := rfl
    pvP_eq := rfl }⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
