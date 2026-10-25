-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.NativeCensusPowerBudgets, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeRowRates

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

noncomputable section

/-- The actual census exponent fits the small coefficient budget,
with the tuning factor retained throughout the rate calculation. -/
theorem native_sample_census_rate
    (tune : Tuning) {κ₁ dimension precision loss gain delta : ℝ} {Ep m : ℕ}
    (hv : NativeDesign.Valid κ₁ dimension precision loss)
    (hbudget : tune.budget κ₁ dimension Ep precision loss=NativeDesign.budget κ₁ dimension Ep precision loss)
    (hgain : 0 < gain) (hdelta0 : 0 ≤ delta) (hslack : censusSlack ≤ tune.slack)
    (hdelta : delta ≤ tolOf tune κ₁ dimension Ep precision loss gain)
    (hgrid : 8 ≤ gridFineOf tune κ₁ dimension Ep precision loss gain*m) :
    3*delta*(censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet:ℝ)+
      ubOf tune κ₁ dimension Ep precision loss gain+1/(m:ℝ) ≤
      NativeDesign.coefficientCoeff κ₁ dimension Ep precision loss*gain/1000000000 := by
  have hFront := NativeDesign.front_budget_room (Ep:=Ep) hv
  obtain ⟨_hd0,_hd1,_hκ,hκ1,_hprecision,hloss,hloss1⟩ := hv
  obtain ⟨hub,hgridRate,hdeltaRate⟩ := sample_budget_rate_bounds tune hκ1 hloss hgain hslack hdelta hgrid
  let A := tune.budget κ₁ dimension Ep precision loss*(loss*gain/((Ep:ℝ)+1))
  let F := (censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet:ℝ)
  have hB := tune.budget_pos κ₁ dimension Ep precision loss
  have hA0 : 0 ≤ A := by dsimp only [A]; positivity
  have hEp : (1:ℝ) ≤ (Ep:ℝ)+1 := by linarith only [Nat.cast_nonneg (α := ℝ) Ep]
  have hdisplay : loss*gain/((Ep:ℝ)+1) ≤ gain := by
    rw [div_le_iff₀ (zero_lt_one.trans_le hEp)]
    have h1 := mul_le_mul_of_nonneg_right hloss1 hgain.le
    have h2 := mul_le_mul_of_nonneg_left hEp hgain.le
    nlinarith only [h1,h2]
  have hBsmall : tune.budget κ₁ dimension Ep precision loss ≤
      NativeDesign.coefficientCoeff κ₁ dimension Ep precision loss/1000000 := by
    rw [←hbudget] at hFront
    linarith only [hFront]
  have hA : A ≤ NativeDesign.coefficientCoeff κ₁ dimension Ep precision loss*gain/1000000 := by
    calc
      _ ≤ tune.budget κ₁ dimension Ep precision loss*gain := mul_le_mul_of_nonneg_left hdisplay hB.le
      _ ≤ _ := by simpa only [div_mul_eq_mul_div] using mul_le_mul_of_nonneg_right hBsmall hgain.le
  have hdeltaF : delta*F ≤ delta*(F+1) := by linarith only [hdelta0]
  have hsmall : 3*delta*F+ubOf tune κ₁ dimension Ep precision loss gain+1/(m:ℝ) ≤ A/1000 := by
    change _ ≤ A/4096 at hub hgridRate
    change delta*(F+1) ≤ A/640000 at hdeltaRate
    linarith only [hub,hgridRate,hdeltaRate,hdeltaF,hA0]
  exact hsmall.trans (by linarith only [hA])

/-- The literal original census constant fits the P1 charge budget. -/
theorem native_sample_census_power_bound
    (tune : Tuning) {κ₁ dimension precision loss gain delta N L Kgeom κ : ℝ} {Ep m : ℕ}
    (hv : NativeDesign.Valid κ₁ dimension precision loss)
    (hbudget : tune.budget κ₁ dimension Ep precision loss=NativeDesign.budget κ₁ dimension Ep precision loss)
    (hgain : 0 < gain) (hL : 0 < L) (hdelta0 : 0 ≤ delta) (hslack : censusSlack ≤ tune.slack)
    (hdelta : delta ≤ tolOf tune κ₁ dimension Ep precision loss gain)
    (hgrid : 8 ≤ gridFineOf tune κ₁ dimension Ep precision loss gain*m)
    (hN : 1 ≤ N) (hK : 24 ≤ Kgeom) (hκ : 1 ≤ κ) (hκK : κ ≤ Kgeom)
    (hNK : N^(2*delta*L) ≤ Kgeom) (hG : Kgeom ≤ N^((3*delta)*L)) :
    let ub := ubOf tune κ₁ dimension Ep precision loss gain
    censusKOf Kgeom FixedSourcePowers.coreRadius FixedSourcePowers.jet
      (stripExpOf Kgeom κ N delta L (N^(-(ub*L)))) (rowExpOf FixedSourcePowers.coreRadius)
      (gapExpOf Kgeom N delta L m) ≤ N^((NativeDesign.coefficientCoeff κ₁ dimension Ep precision loss*(gain*L))/1000) := by
  have hrate := native_sample_census_rate tune hv hbudget hgain hdelta0 hslack hdelta hgrid
  have hcoef := NativeDesign.coefficientCoeff_pos κ₁ dimension (Ep:=Ep) (precision:=precision) hv.2.2.2.2.2.1
  have hub : 0 ≤ ubOf tune κ₁ dimension Ep precision loss gain := by
    dsimp only [ubOf]
    have hB := tune.budget_pos κ₁ dimension Ep precision loss
    have hκ0 := hv.2.2.1
    have hloss := hv.2.2.2.2.2.1
    positivity
  have hC := censusK_le_rpow (R:=FixedSourcePowers.coreRadius) (J:=FixedSourcePowers.jet)
    (m:=m) hK hκ hκK hN hNK (mul_nonneg hdelta0 hL.le) hL.le (mul_nonneg hub hL.le) hG
  refine hC.trans (Real.rpow_le_rpow_of_exponent_le hN ?_)
  have hh := mul_le_mul_of_nonneg_right hrate hL.le
  have hp := mul_pos hcoef (mul_pos hgain hL)
  nlinarith only [hh,hp]

/-- Both bounds used by the P1 mass estimate hold at the actual
census logarithmic ceiling, with the existing source threshold. -/
theorem native_census_steps_power_budget
    {N h Kc : ℝ} (hN : 1 ≤ N) (hh : 0 < h)
    (hlarge : 20000 ≤ N^(h/1000000)) (hKc : 1 ≤ Kc) (hKpower : Kc ≤ N^(h/1000)) :
    Kc ≤ N^(h/1000) ∧ (2:ℝ)^stepsOf Kc ≤ N^(h/5) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have h2 : (2:ℝ) ≤ N^(h/1000000) := by linarith only [hlarge]
  have hpow : Kc^(100:ℕ) ≤ N^(h/10) := by
    calc
      _ ≤ (N^(h/1000))^(100:ℕ) := pow_le_pow_left₀ (zero_le_one.trans hKc) hKpower _
      _ = _ := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hNp.le]
        congr 1
        norm_num
        ring
  refine ⟨hKpower,?_⟩
  calc
    _ ≤ 2*Kc^(100:ℕ) := (two_pow_stepsOf hKc).2
    _ ≤ N^(h/1000000)*N^(h/10) := mul_le_mul h2 hpow (by positivity) (Real.rpow_nonneg hNp.le _)
    _ = N^(h/1000000+h/10) := (Real.rpow_add hNp _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith only [hh])

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
