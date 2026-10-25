-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.NativeSamplePowersAtChoices, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleChoices
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeRowRates
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeOriginalSourceBudgets
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeDesignMeshLower
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeGeometryProfile

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Filter
open Parent.ParentSource

noncomputable section

/-- The literal sample mesh cap one is redundant at a native target. -/
theorem sample_choices_native_mesh_index
    {κ source N delta L tau ub d₁ target : ℝ} {m : ℕ}
    (htarget : target ≤ 1) (hKg : 1 ≤ KgAt κ source N delta L tau ub d₁ m) :
    nmeshAt κ source N delta L tau ub d₁ target m=
      meshIndexOf (mk4MeshTarget target (KgAt κ source N delta L tau ub d₁ m) (κ⁻¹/512)) d₁ := by
  have hKg0 : 0 < KgAt κ source N delta L tau ub d₁ m := zero_lt_one.trans_le hKg
  have hcost : (1:ℝ) ≤ 80*KgAt κ source N delta L tau ub d₁ m^7 := by
    have hh := one_le_pow₀ (n:=7) hKg
    linarith only [hh]
  have hsmall : target/(80*KgAt κ source N delta L tau ub d₁ m^7) ≤ 1 :=
    (div_le_one (by positivity)).mpr (htarget.trans hcost)
  unfold nmeshAt TmAt mk4MeshTarget
  rw [min_eq_left hsmall]

/-- One uniform pre-path threshold gives all actual native row,
coefficient, velocity, band and graph-floor inputs at SampleChoices. -/
theorem eventually_native_sample_power_bounds_at_choices
    (tune : Tuning) (N : ℕ → ℝ) (hN : Tendsto N atTop atTop)
    {κ₁ d₁ precision loss gain L delta front : ℝ} {Ep m : ℕ}
    (hv : NativeDesign.Valid κ₁ d₁ precision loss)
    (hbudget : tune.budget κ₁ d₁ Ep precision loss=NativeDesign.budget κ₁ d₁ Ep precision loss)
    (hgain : 0 < gain) (hL : 0 < L) (hdelta : 0 < delta)
    (hslack : censusSlack ≤ tune.slack)
    (hdeltaTol : delta ≤ tolOf tune κ₁ d₁ Ep precision loss gain)
    (hgrid : 8 ≤ gridFineOf tune κ₁ d₁ Ep precision loss gain*m) (hfront : 0 < front) :
    let tau := tauOf tune delta L front
    let ub := ubOf tune κ₁ d₁ Ep precision loss gain
    let h := NativeDesign.coefficientCoeff κ₁ d₁ Ep precision loss*(gain*L)
    ∃ sigma : ℝ, 0 < sigma ∧ sigma ≤ 1 ∧ ∀ᶠ k in atTop,
      ∀ κ source : ℝ, 1 ≤ κ → 1 ≤ source → κ ≤ N k^sigma → source ≤ N k^sigma →
        28*KgAt κ source (N k) delta L tau ub d₁ m^6 ≤
          N k^((NativeDesign.regularityCoeff κ₁ d₁ Ep precision loss*(gain*L))/1000) ∧
        κ+24*κ+κ^2+2*source ≤ N k^h ∧ 2*source ≤ N k^h ∧
        CbandAt κ source (N k) delta L tau d₁ ≤ N k^h ∧
        N k^(-(NativeDesign.graphLowerCoeff κ₁ d₁ Ep precision*(gain*L))) ≤
          Submission.Lib.K4DyadicRowScales.mesh
            (nmeshAt κ source (N k) delta L tau ub d₁
              (thetaNAt κ₁ d₁ Ep precision gain (N k) L) m) := by
  have hSourceExponents := native_design_original_source_exponents tune hv hbudget hgain hL hdelta.le hdeltaTol (by norm_num : (1:ℝ) ≤ 1)
  have hv0 := hv
  obtain ⟨hd0,hd1,hκ₁,hκ₁1,hprecision,hloss,hloss1⟩ := hv0
  let a := gain*L
  let h := NativeDesign.coefficientCoeff κ₁ d₁ Ep precision loss*a
  let tau := tauOf tune delta L front
  let ub := ubOf tune κ₁ d₁ Ep precision loss gain
  have ha : 0 < a := mul_pos hgain hL
  have hh : 0 < h := hSourceExponents.1
  have htau : 0 ≤ tau := by
    dsimp only [tau,tauOf]
    have hS := tune.one_le_slack
    exact le_min (mul_nonneg hdelta.le hL.le) (by positivity)
  have htauL : tau ≤ delta*L := min_le_left _ _
  have hub : 0 ≤ ub := by
    dsimp only [ub,ubOf]
    have hB := tune.budget_pos κ₁ d₁ Ep precision loss
    positivity
  have hMassOne := NativeDesign.massCoeff_le_one κ₁ d₁ (Ep:=Ep) (precision:=precision) hloss1
  have hRegMass := NativeDesign.regularityCoeff_le_mass κ₁ d₁ (Ep:=Ep) (precision:=precision) hloss
  have hRegOne : NativeDesign.regularityCoeff κ₁ d₁ Ep precision loss ≤ 1 := by linarith only [hMassOne,hRegMass]
  have hReg : 0 < NativeDesign.regularityCoeff κ₁ d₁ Ep precision loss := NativeDesign.regularityCoeff_pos κ₁ d₁ hloss
  have hTarget : 0 < NativeDesign.graphTargetCoeff κ₁ d₁ Ep precision := by
    unfold NativeDesign.graphTargetCoeff
    have hE := NativeDesign.floorEndCoeff_pos κ₁ d₁ (Ep:=Ep) hprecision
    have hClock := NativeDesign.clockCoeff_pos (Ep:=Ep) hprecision
    positivity
  obtain ⟨sg,hsg,hsg1,hGeom⟩ := eventually_geom_le N hN hdelta hL
  obtain ⟨sb,hsb,hsb1,hBrow⟩ := eventually_native_sample_brow_le tune N hN hv hbudget hgain hL hdelta.le hslack hdeltaTol hgrid
  obtain ⟨sm,hsm,hsm1,hMesh⟩ := eventually_native_design_graph_mesh_lower N hN Ep hκ₁ hd0 hd1 hprecision ha
  let sigma := min sg (min sb (min sm (min 1 (h/1000000))))
  have hsigma : 0 < sigma := lt_min hsg (lt_min hsb (lt_min hsm (lt_min one_pos (by positivity))))
  have hsgle : sigma ≤ sg := min_le_left _ _
  have hsble : sigma ≤ sb := (min_le_right _ _).trans (min_le_left _ _)
  have hsmle : sigma ≤ sm := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hCap : sigma ≤ min 1 (h/1000000) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hLarge := ((tendsto_rpow_atTop (by positivity : 0 < h/1000000)).comp hN).eventually_ge_atTop 20000
  refine ⟨sigma,hsigma,hCap.trans (min_le_left _ _),?_⟩
  filter_upwards [hGeom,hBrow,hMesh,hLarge,hN.eventually (eventually_ge_atTop 1)] with k hGeo hRow hFloor hConstant hk
  intro κ source hκ hsource hκN hsourceN
  have hκpow {x : ℝ} (hx : sigma ≤ x) : κ ≤ N k^x := hκN.trans (Real.rpow_le_rpow_of_exponent_le hk hx)
  have hsourcepow {x : ℝ} (hx : sigma ≤ x) : source ≤ N k^x := hsourceN.trans (Real.rpow_le_rpow_of_exponent_le hk hx)
  have hEnvelope := Native.native_pre_geometry_envelope_bounds (source:=source) hκ hk (add_nonneg htau htau)
  have hG24 : 24 ≤ KgeomAt κ source (N k) delta L tau :=
    (by norm_num : (24:ℝ) ≤ 2304).trans (hEnvelope.1.trans ((le_max_left _ _).trans (le_max_left _ _)))
  have hκG : κ ≤ KgeomAt κ source (N k) delta L tau :=
    (le_max_left κ source).trans (hEnvelope.2.2.1.trans ((le_max_left _ _).trans (le_max_left _ _)))
  have hGeometry : N k^(2*delta*L) ≤ KgeomAt κ source (N k) delta L tau :=
    (le_max_right _ _).trans (le_max_left _ _)
  have hGPower : KgeomAt κ source (N k) delta L tau ≤ N k^((3*delta)*L) := by
    simpa only [KgeomAt,two_mul] using hGeo κ source tau hκ (hκpow hsgle) (hsourcepow hsgle) htau htauL
  have hKcen : 1 ≤ KcenAt κ source (N k) delta L tau ub m :=
    one_le_pow₀ ((by norm_num : (1:ℝ) ≤ 24).trans hG24)
  have hKcenPower := censusK_le_rpow (R:=FixedSourcePowers.coreRadius) (J:=FixedSourcePowers.jet) (m:=m)
    hG24 hκ hκG hk hGeometry (mul_nonneg hdelta.le hL.le) hL.le (mul_nonneg hub hL.le) hGPower
  have hRowBound := hRow κ source (KcenAt κ source (N k) delta L tau ub m) tau hκ (hκpow hsble)
    hsource (hsourcepow hsble) hKcen hKcenPower htau htauL
  change 28*KgAt κ source (N k) delta L tau ub d₁ m^6 ≤
    N k^((NativeDesign.regularityCoeff κ₁ d₁ Ep precision loss*gain/1000)*L) at hRowBound
  have hKg : 1 ≤ KgAt κ source (N k) delta L tau ub d₁ m := by
    have hJ : 6*(1+24*κ+κ^2+2*source) ≤ KgAt κ source (N k) delta L tau ub d₁ m := le_max_left _ _
    nlinarith only [hJ,hκ,hsource,sq_nonneg κ]
  have hKgPower : KgAt κ source (N k) delta L tau ub d₁ m ≤ N k^a := by
    calc
      _ ≤ 28*KgAt κ source (N k) delta L tau ub d₁ m^6 := by
        have hh' := le_self_pow₀ hKg (by norm_num : 6 ≠ 0)
        have hz := pow_nonneg (zero_le_one.trans hKg) 6
        nlinarith only [hh',hz]
      _ ≤ _ := hRowBound
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hk (by
        have hh' := mul_le_mul_of_nonneg_right hRegOne ha.le
        dsimp only [a] at hh' ⊢
        nlinarith only [hh',mul_pos hReg ha])
  have hGraph := hFloor κ (KgAt κ source (N k) delta L tau ub d₁ m) hκ (hκpow hsmle) hKg hKgPower
  have hTheta1 : thetaNAt κ₁ d₁ Ep precision gain (N k) L ≤ 1 := by
    unfold thetaNAt
    exact Real.rpow_le_one_of_one_le_of_nonpos hk (by nlinarith only [mul_pos hTarget ha])
  have hIndex := sample_choices_native_mesh_index hTheta1 hKg
  have hCoefficients := native_original_source_envelope_bounds hk hh hsigma.le (hCap.trans (min_le_right _ _))
    hκ (zero_le_one.trans hsource) hκN hsourceN hSourceExponents.2.2 htauL hd1.le hConstant
  have hVelocity : 2*source ≤ N k^h := by nlinarith only [hCoefficients.1,hκ,sq_nonneg κ]
  refine ⟨?_,hCoefficients.1,hVelocity,?_,?_⟩
  · convert hRowBound using 1 <;> ring
  · have hBand := hCoefficients.2.trans (Real.rpow_le_rpow_of_exponent_le hk (by linarith only [hh] : h/1000 ≤ h))
    simpa only [CbandAt,mul_assoc] using hBand
  · rw [hIndex]
    simpa only [thetaNAt,a,mul_assoc] using hGraph

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
