-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.SampleRecordStateEventual, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleRecordBlock
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleStateBlock
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleStripBudgets

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Filter
open Parent.ParentSource
open scoped ENNReal

noncomputable section

/-- One pre-path exponent and common threshold for every primitive
record, state, geometry and strip fact used by the sample blocks. -/
theorem eventually_sample_record_state_block_facts
    (tune : Tuning) (hslack : FixedSourcePowers.slack ≤ tune.slack)
    (N : ℕ → ℝ) (hN : Tendsto N atTop atTop) (fixedConstant : ℝ)
    {κ₁ d₁ precision loss gain L delta front divisor : ℝ} {Ep m C : ℕ}
    (hv : NativeDesign.Valid κ₁ d₁ precision loss) (hgain : 0 < gain) (hL : 0 < L)
    (hgainCap : gain ≤ gainCap tune κ₁ d₁ Ep precision loss)
    (hm : 0 < m) (hgm : 8 ≤ gain*(m:ℝ)) (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ gain/100)
    (hdeltaTol : delta ≤ tolOf tune κ₁ d₁ Ep precision loss gain)
    (hdeltaStrip : delta ≤ (ubOf tune κ₁ d₁ Ep precision loss gain/8)/100)
    (hC : (C:ℝ) ≤ windowOf tune κ₁ d₁ Ep precision loss gain*(m:ℝ)+1)
    (hfront : 0 < front) (hdivisor : 1 ≤ divisor) (hdivisorMax : divisor ≤ 5000) :
    let display := loss*gain*L/((Ep:ℝ)+1)
    let internal := tune.budget κ₁ d₁ Ep precision loss*display/divisor
    let coefficient := NativeDesign.coefficientCoeff κ₁ d₁ Ep precision loss*(gain*L)
    let entropy := entropyOf C m (ueOf tune κ₁ d₁ Ep precision loss gain delta L)
    let b := RecordBudgets.cutExponent front internal
    let tau := tauOf tune delta L front
    ∃ sigma : ℝ, 0 < sigma ∧ sigma ≤ 1 ∧ sigma ≤ coefficient/1000000 ∧ ∀ᶠ k in atTop,
      1 < N k ∧ 24 ≤ N k^(gain*L) ∧ 20000 ≤ N k^(coefficient/1000000) ∧
      ∀ κ source : ℝ, 1 ≤ κ → κ ≤ N k^sigma → source ≤ N k^sigma →
        let Krecord := Native.nativePreGeometryEnvelope κ source (N k) (tau+tau)
        let G := N k^(recordGeometryExponent tune κ₁ d₁ Ep precision loss gain divisor*L)
        (2304 ≤ Krecord ∧ Krecord ≤ G ∧ max κ source ≤ Krecord ∧
          N k^(2*delta*L) ≤ G ∧ fixedConstant ≤ G) ∧
        (RecordBudgets.StateBudgetsAt (N k) κ Krecord b front display entropy ∧
          ENNReal.ofReal ((8*N k^entropy)/N k^(-b))/ENNReal.ofReal (N k^(-b)) ≤
            ENNReal.ofReal (N k^(internal/2))) ∧
        (KOf Ep loss gain (N k) L/4)^(-100:ℝ)*κ*N k^(2*delta*L) ≤
          N k^(-(ubOf tune κ₁ d₁ Ep precision loss gain*L)) ∧
        N k^(-(2*(ubOf tune κ₁ d₁ Ep precision loss gain*L)))*κ*N k^(2*delta*L) ≤
          N k^(-(ubOf tune κ₁ d₁ Ep precision loss gain*L)) := by
  have hv0 := hv
  obtain ⟨_hd0,_hd1,hκ,hκ1,hprecision,hloss,_hloss1⟩ := hv0
  let coefficient := NativeDesign.coefficientCoeff κ₁ d₁ Ep precision loss*(gain*L)
  have hcoefficient : 0 < coefficient :=
    mul_pos (NativeDesign.coefficientCoeff_pos κ₁ d₁ hloss) (mul_pos hgain hL)
  have hdivisor0 : 0 < divisor := zero_lt_one.trans_le hdivisor
  have htau : 0 ≤ tauOf tune delta L front := by
    unfold tauOf
    have hS := tune.one_le_slack
    exact le_min (mul_nonneg hdelta0 hL.le) (by positivity)
  obtain ⟨sg,hsg,hsg1,hgeometry⟩ := eventually_sample_record_geometry_envelope tune hslack N hN fixedConstant
    hloss hgain hL hdelta0 hfront hdivisor0 hdivisorMax hdeltaTol htau
  obtain ⟨ss,hss,hss1,hstates⟩ := eventually_sample_record_state_budgets tune hslack N hN
    hκ hκ1 hv.1 hv.2.1 hprecision hloss hgain hL hgainCap hm hgm hdelta hdeltaTol hC hfront
    hdivisor hdivisorMax htau
  obtain ⟨sw,hsw,hsw1,hstrips⟩ := eventually_sample_original_strip_budgets tune N hN
    hκ hκ1 hloss hgain hL hdeltaStrip
  let sigma := min sg (min ss (min sw (min 1 (coefficient/1000000))))
  have hsigma : 0 < sigma := lt_min hsg (lt_min hss (lt_min hsw (lt_min one_pos (by positivity))))
  have hsgle : sigma ≤ sg := min_le_left _ _
  have hssle : sigma ≤ ss := (min_le_right _ _).trans (min_le_left _ _)
  have hswle : sigma ≤ sw := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hminle : sigma ≤ min 1 (coefficient/1000000) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hlargeGain := ((tendsto_rpow_atTop (mul_pos hgain hL)).comp hN).eventually_ge_atTop 24
  have hlargeSource := ((tendsto_rpow_atTop (by positivity : 0 < coefficient/1000000)).comp hN).eventually_ge_atTop 20000
  have hGExponent : (tune.budget κ₁ d₁ Ep precision loss*(loss*gain*L/((Ep:ℝ)+1))/divisor)/
      (256*(FixedSourcePowers.power:ℝ))=recordGeometryExponent tune κ₁ d₁ Ep precision loss gain divisor*L := by
    unfold recordGeometryExponent
    ring
  refine ⟨sigma,hsigma,hminle.trans (min_le_left _ _),hminle.trans (min_le_right _ _),?_⟩
  filter_upwards [hgeometry,hstates,hstrips,hN.eventually (eventually_gt_atTop 1),hlargeGain,hlargeSource]
    with k hg hs hw hk hgainLarge hsourceLarge
  refine ⟨hk,hgainLarge,hsourceLarge,?_⟩
  intro κ source hκone hκN hsourceN
  have hκpow {a : ℝ} (ha : sigma ≤ a) : κ ≤ N k^a :=
    hκN.trans (Real.rpow_le_rpow_of_exponent_le hk.le ha)
  have hsourcepow {a : ℝ} (ha : sigma ≤ a) : source ≤ N k^a :=
    hsourceN.trans (Real.rpow_le_rpow_of_exponent_le hk.le ha)
  have hgeo := hg κ source hκone (hκpow hsgle) (hsourcepow hsgle)
  have hstate := hs κ source hκone (hκpow hssle) (hsourcepow hssle)
  have hstrip := hw κ hκone (hκpow hswle)
  refine ⟨?_,?_,hstrip.1,hstrip.2⟩
  · simpa only [hGExponent,two_mul] using hgeo
  · simpa only [two_mul] using hstate

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
