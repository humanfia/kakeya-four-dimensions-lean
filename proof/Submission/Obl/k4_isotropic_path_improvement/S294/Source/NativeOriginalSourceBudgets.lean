-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.NativeOriginalSourceBudgets, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeDesignPowers
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleRecordBudgets

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Filter
open scoped ENNReal

noncomputable section

/-- The actual original coefficient and moving-band numerators fit
the native coefficient power, uniformly in the later path and datum. -/
theorem native_original_source_envelope_bounds
    {N κ source h gap deltaL tau dimension : ℝ}
    (hN : 1 ≤ N) (hh : 0 < h) (hgap0 : 0 ≤ gap) (hgap : gap ≤ h/1000000)
    (hκ : 1 ≤ κ) (_hsource0 : 0 ≤ source) (hκN : κ ≤ N^gap) (hsourceN : source ≤ N^gap)
    (hdelta : deltaL ≤ h/10000000) (htau : tau ≤ deltaL) (hdimension : dimension ≤ 1)
    (hlarge : 20000 ≤ N^(h/1000000)) :
    κ+24*κ+κ^2+2*source ≤ N^h ∧
      64*(max κ source)^2*κ*4^dimension*N^(2*deltaL+(tau+2*deltaL)+tau) ≤ N^(h/1000) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hκ0 : 0 ≤ κ := zero_le_one.trans hκ
  have hN2 : N^gap ≤ N^(2*gap) := Real.rpow_le_rpow_of_exponent_le hN (by linarith only [hgap0])
  have hκ2 : κ^2 ≤ N^(2*gap) := by
    calc
      _ ≤ (N^gap)^2 := pow_le_pow_left₀ hκ0 hκN 2
      _ = _ := by rw [←Real.rpow_natCast,←Real.rpow_mul hNp.le]; congr 1; ring
  have hcoefficient : κ+24*κ+κ^2+2*source ≤ 28*N^(2*gap) := by
    nlinarith only [hκN.trans hN2,hsourceN.trans hN2,hκ2]
  have h28 : (28:ℝ) ≤ N^(h/1000000) := by linarith only [hlarge]
  have h256 : (256:ℝ) ≤ N^(h/1000000) := by linarith only [hlarge]
  have hmax0 : 0 ≤ max κ source := hκ0.trans (le_max_left _ _)
  have hmax : max κ source ≤ N^gap := max_le hκN hsourceN
  have h4 : (4:ℝ)^dimension ≤ 4 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 4) hdimension
  constructor
  · calc
      _ ≤ 28*N^(2*gap) := hcoefficient
      _ ≤ N^(h/1000000)*N^(2*gap) :=
        mul_le_mul_of_nonneg_right h28 (Real.rpow_nonneg hNp.le _)
      _ = N^(h/1000000+2*gap) := (Real.rpow_add hNp _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith only [hgap,hh])
  · have hraw : 64*(max κ source)^2*κ*4^dimension*N^(2*deltaL+(tau+2*deltaL)+tau) ≤
        256*N^(3*gap+4*deltaL+2*tau) := by
      calc
        _ ≤ 64*(N^gap)^2*N^gap*4*N^(2*deltaL+(tau+2*deltaL)+tau) := by gcongr
        _ = 256*((N^gap)^3*N^(2*deltaL+(tau+2*deltaL)+tau)) := by ring
        _ = _ := by
          rw [←Real.rpow_natCast,←Real.rpow_mul hNp.le,←Real.rpow_add hNp]
          congr 2
          norm_num
          ring
    calc
      _ ≤ 256*N^(3*gap+4*deltaL+2*tau) := hraw
      _ ≤ N^(h/1000000)*N^(3*gap+4*deltaL+2*tau) :=
        mul_le_mul_of_nonneg_right h256 (Real.rpow_nonneg hNp.le _)
      _ = N^(h/1000000+(3*gap+4*deltaL+2*tau)) := (Real.rpow_add hNp _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith only [hgap,hdelta,htau,hh])

/-- The original record constructor uses the literal factor 512,
which fits the same cap as the native factor 64 at the same threshold. -/
theorem native_original_record_envelope_bound
    {N κ source h gap deltaL tau dimension : ℝ}
    (hN : 1 ≤ N) (hh : 0 < h) (hgap : gap ≤ h/1000000)
    (hκ : 1 ≤ κ) (hκN : κ ≤ N^gap) (hsourceN : source ≤ N^gap)
    (hdelta : deltaL ≤ h/10000000) (htau : tau ≤ deltaL) (hdimension : dimension ≤ 1)
    (hlarge : 20000 ≤ N^(h/1000000)) :
    512*(max κ source)^2*κ*4^dimension*N^(2*deltaL+(tau+2*deltaL)+tau) ≤ N^(h/1000) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hκ0 : 0 ≤ κ := zero_le_one.trans hκ
  have h2048 : (2048:ℝ) ≤ N^(h/1000000) := by linarith only [hlarge]
  have hmax0 : 0 ≤ max κ source := hκ0.trans (le_max_left _ _)
  have hmax : max κ source ≤ N^gap := max_le hκN hsourceN
  have h4 : (4:ℝ)^dimension ≤ 4 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 4) hdimension
  have hraw : 512*(max κ source)^2*κ*4^dimension*N^(2*deltaL+(tau+2*deltaL)+tau) ≤
      2048*N^(3*gap+4*deltaL+2*tau) := by
    calc
      _ ≤ 512*(N^gap)^2*N^gap*4*N^(2*deltaL+(tau+2*deltaL)+tau) := by gcongr
      _ = 2048*((N^gap)^3*N^(2*deltaL+(tau+2*deltaL)+tau)) := by ring
      _ = _ := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hNp.le,←Real.rpow_add hNp]
        congr 2
        norm_num
        ring
  calc
    _ ≤ 2048*N^(3*gap+4*deltaL+2*tau) := hraw
    _ ≤ N^(h/1000000)*N^(3*gap+4*deltaL+2*tau) :=
      mul_le_mul_of_nonneg_right h2048 (Real.rpow_nonneg hNp.le _)
    _ = N^(h/1000000+(3*gap+4*deltaL+2*tau)) := (Real.rpow_add hNp _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith only [hgap,hdelta,htau,hh])

/-- Exact retained-record and post-state palette numerators are
small native constants at the already chosen internal allowance. -/
theorem native_original_palette_power_budgets
    {N h internal entropy b Kcap : ℝ}
    (hN : 1 ≤ N) (hh : 0 < h) (hlarge : 20000 ≤ N^(h/1000000))
    (hinternal : internal ≤ h/1000000) (hentropy : entropy ≤ internal/4)
    (hb : 64*b ≤ internal) (_hKcap0 : 0 ≤ Kcap) (hKcap : Kcap ≤ N^(h/1000)) :
    4*625*((8*N^entropy)/N^(-b))*Kcap ≤ N^h ∧
      (4:ENNReal)*(ENNReal.ofReal ((8*N^entropy)/N^(-b))/ENNReal.ofReal (N^(-b))) ≤
        ENNReal.ofReal (N^h) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hcut : 0 < N^(-b) := Real.rpow_pos_of_pos hNp _
  have hratio : (8*N^entropy)/N^(-b)=8*N^(entropy+b) := by
    rw [Real.rpow_neg hNp.le,div_inv_eq_mul,Real.rpow_add hNp]
    ring
  have hratio2 : (8*N^entropy)/N^(-b)/N^(-b)=8*N^(entropy+2*b) := by
    rw [Real.rpow_neg hNp.le,div_inv_eq_mul,div_inv_eq_mul,
      show entropy+2*b=(entropy+b)+b by ring,Real.rpow_add hNp,Real.rpow_add hNp]
    ring
  constructor
  · calc
      _ = 20000*N^(entropy+b)*Kcap := by rw [hratio]; ring
      _ ≤ 20000*N^(entropy+b)*N^(h/1000) := by gcongr
      _ ≤ N^(h/1000000)*N^(entropy+b)*N^(h/1000) := by gcongr
      _ = N^(h/1000000+(entropy+b)+h/1000) := by rw [←Real.rpow_add hNp,←Real.rpow_add hNp]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith only [hinternal,hentropy,hb,hh])
  · rw [←ENNReal.ofReal_div_of_pos hcut]
    have h4 : (4:ENNReal)=ENNReal.ofReal (4:ℝ) := by norm_num
    rw [h4,←ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ = 32*N^(entropy+2*b) := by rw [hratio2]; ring
      _ ≤ N^(h/1000000)*N^(entropy+2*b) := mul_le_mul_of_nonneg_right
        (by linarith only [hlarge] : (32:ℝ) ≤ N^(h/1000000)) (Real.rpow_nonneg hNp.le _)
      _ = N^(h/1000000+(entropy+2*b)) := (Real.rpow_add hNp _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith only [hinternal,hentropy,hb,hh])

/-- The literal native design supplies the coefficient reserve for
the internal allowance and the original profile-error exponent. -/
theorem native_design_original_source_exponents
    (tune : Tuning) {κ₁ dimension precision loss gain L delta divisor : ℝ} {Ep : ℕ}
    (hv : NativeDesign.Valid κ₁ dimension precision loss)
    (hbudget : tune.budget κ₁ dimension Ep precision loss=NativeDesign.budget κ₁ dimension Ep precision loss)
    (hgain : 0 < gain) (hL : 0 < L) (hdelta0 : 0 ≤ delta)
    (hdelta : delta ≤ tolOf tune κ₁ dimension Ep precision loss gain) (hdivisor : 1 ≤ divisor) :
    let h := NativeDesign.coefficientCoeff κ₁ dimension Ep precision loss*(gain*L)
    let internal := tune.budget κ₁ dimension Ep precision loss*(loss*gain*L/((Ep:ℝ)+1))/divisor
    0 < h ∧ internal ≤ h/1000000 ∧ delta*L ≤ h/10000000 := by
  have hNativeFront := NativeDesign.front_budget_room (Ep:=Ep) hv
  obtain ⟨_hd0,_hd1,_hκ,_hκ1,_hprecision,hloss,hloss1⟩ := hv
  let h := NativeDesign.coefficientCoeff κ₁ dimension Ep precision loss*(gain*L)
  let display := loss*gain*L/((Ep:ℝ)+1)
  let B := tune.budget κ₁ dimension Ep precision loss
  have hB : 0 < B := tune.budget_pos _ _ _ _ _
  have hS : 0 < tune.slack := zero_lt_one.trans_le tune.one_le_slack
  have hEp : (1:ℝ) ≤ (Ep:ℝ)+1 := by linarith only [Nat.cast_nonneg (α := ℝ) Ep]
  have hdivisor0 : 0 < divisor := zero_lt_one.trans_le hdivisor
  have hgL : 0 < gain*L := mul_pos hgain hL
  have hpos : 0 < h := mul_pos (NativeDesign.coefficientCoeff_pos κ₁ dimension hloss) hgL
  have hdisplay0 : 0 < display := by dsimp only [display]; positivity
  have hdisplay : display ≤ gain*L := by
    dsimp only [display]
    rw [div_le_iff₀ (zero_lt_one.trans_le hEp)]
    have h1 := mul_le_mul_of_nonneg_right hloss1 hgL.le
    have h2 := mul_le_mul_of_nonneg_left hEp hgL.le
    nlinarith only [h1,h2]
  have hBroom : 1000000*B ≤ NativeDesign.coefficientCoeff κ₁ dimension Ep precision loss := by
    simpa only [B,hbudget] using hNativeFront
  have hBsmall : B*(gain*L) ≤ h/1000000 := by
    have hh := mul_le_mul_of_nonneg_right hBroom hgL.le
    dsimp only [h]
    linarith only [hh]
  have hAmp : B*display ≤ B*(gain*L) := mul_le_mul_of_nonneg_left hdisplay hB.le
  have hinternal : B*display/divisor ≤ h/1000000 := by
    apply le_trans _ (hAmp.trans hBsmall)
    rw [div_le_iff₀ hdivisor0]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hdivisor (mul_nonneg hB.le hdisplay0.le)
  have hdeltaS : delta*L*tune.slack ≤ (B*display)/10000 := by
    have hh := mul_le_mul_of_nonneg_right hdelta (by positivity : (0:ℝ) ≤ L*tune.slack)
    have heq : tolOf tune κ₁ dimension Ep precision loss gain*(L*tune.slack)=(B*display)/10000 := by
      dsimp only [tolOf,B,display]
      field_simp
    nlinarith only [hh,heq]
  have hdeltaCost : delta*L ≤ h/10000000 := by
    calc
      _ ≤ delta*L*tune.slack := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left tune.one_le_slack (mul_nonneg hdelta0 hL.le)
      _ ≤ (B*display)/10000 := hdeltaS
      _ ≤ (B*(gain*L))/10000 := div_le_div_of_nonneg_right hAmp (by norm_num)
      _ ≤ (h/1000000)/10000 := div_le_div_of_nonneg_right hBsmall (by norm_num)
      _ ≤ _ := by linarith only [hpos]
  exact ⟨hpos,hinternal,hdeltaCost⟩

/-- One common tail bounds every actual original source numerator;
the later conditional palette and record cap use the same power. -/
theorem eventually_native_original_source_budgets
    (N : ℕ → ℝ) (hN : Tendsto N atTop atTop)
    {h deltaL tau dimension : ℝ} (hh : 0 < h)
    (hdelta : deltaL ≤ h/10000000) (htau : tau ≤ deltaL) (hdimension : dimension ≤ 1) :
    ∃ sigma : ℝ, 0 < sigma ∧ sigma ≤ 1 ∧ ∀ᶠ k in atTop,
      20000 ≤ N k^(h/1000000) ∧
      (∀ κ source : ℝ, 1 ≤ κ → 0 ≤ source → κ ≤ N k^sigma → source ≤ N k^sigma →
        κ+24*κ+κ^2+2*source ≤ N k^h ∧
        64*(max κ source)^2*κ*4^dimension*N k^(2*deltaL+(tau+2*deltaL)+tau) ≤ N k^(h/1000)) ∧
      ∀ internal entropy b Kcap : ℝ, internal ≤ h/1000000 → entropy ≤ internal/4 →
        64*b ≤ internal → 0 ≤ Kcap → Kcap ≤ N k^(h/1000) →
        4*625*((8*N k^entropy)/N k^(-b))*Kcap ≤ N k^h ∧
        (4:ENNReal)*(ENNReal.ofReal ((8*N k^entropy)/N k^(-b))/ENNReal.ofReal (N k^(-b))) ≤
          ENNReal.ofReal (N k^h) := by
  let sigma := min 1 (h/1000000)
  have hsigma : 0 < sigma := lt_min one_pos (by positivity)
  have hsigmaH : sigma ≤ h/1000000 := min_le_right _ _
  have hlarge := ((tendsto_rpow_atTop (by positivity : 0 < h/1000000)).comp hN).eventually_ge_atTop 20000
  refine ⟨sigma,hsigma,min_le_left _ _,?_⟩
  filter_upwards [hN.eventually (eventually_ge_atTop 1),hlarge] with k hk hc
  refine ⟨hc,?_,?_⟩
  · intro κ source hκ hsource0 hκN hsourceN
    exact native_original_source_envelope_bounds hk hh hsigma.le hsigmaH hκ hsource0 hκN hsourceN
      hdelta htau hdimension hc
  · intro internal entropy b Kcap hinternal hentropy hb hKcap0 hKcap
    exact native_original_palette_power_budgets hk hh hc hinternal hentropy hb hKcap0 hKcap

/-- The literal original-record factor 512 also has a common tail
before the later path; it uses the same native coefficient exponent. -/
theorem eventually_native_original_record_envelope_bound
    (N : ℕ → ℝ) (hN : Tendsto N atTop atTop)
    {h deltaL tau dimension : ℝ} (hh : 0 < h)
    (hdelta : deltaL ≤ h/10000000) (htau : tau ≤ deltaL) (hdimension : dimension ≤ 1) :
    ∃ sigma : ℝ, 0 < sigma ∧ sigma ≤ 1 ∧ ∀ᶠ k in atTop,
      ∀ κ source : ℝ, 1 ≤ κ → κ ≤ N k^sigma → source ≤ N k^sigma →
        512*(max κ source)^2*κ*4^dimension*N k^(2*deltaL+(tau+2*deltaL)+tau) ≤ N k^(h/1000) := by
  let sigma := min 1 (h/1000000)
  have hsigma : 0 < sigma := lt_min one_pos (by positivity)
  have hsigmaH : sigma ≤ h/1000000 := min_le_right _ _
  have hlarge := ((tendsto_rpow_atTop (by positivity : 0 < h/1000000)).comp hN).eventually_ge_atTop 20000
  refine ⟨sigma,hsigma,min_le_left _ _,?_⟩
  filter_upwards [hN.eventually (eventually_ge_atTop 1),hlarge] with k hk hc
  intro κ source hκ hκN hsourceN
  exact native_original_record_envelope_bound hk hh hsigmaH hκ hκN hsourceN hdelta htau hdimension hc

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
