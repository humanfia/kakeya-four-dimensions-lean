-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.NativeRowRates, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleRates
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeDesignPowers
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.BrowNumerics

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Filter

noncomputable section

/-- Keep the actual tuning budget in the three front rates. -/
theorem sample_budget_rate_bounds
    (tune : Tuning) {κ₁ dimension precision loss gain delta : ℝ} {Ep m : ℕ}
    (hκ1 : κ₁ ≤ 1) (hloss : 0 < loss) (hgain : 0 < gain)
    (hslack : censusSlack ≤ tune.slack)
    (hdelta : delta ≤ tolOf tune κ₁ dimension Ep precision loss gain)
    (hgrid : 8 ≤ gridFineOf tune κ₁ dimension Ep precision loss gain*m) :
    let A := tune.budget κ₁ dimension Ep precision loss*(loss*gain/((Ep:ℝ)+1))
    ubOf tune κ₁ dimension Ep precision loss gain ≤ A/4096 ∧
      1/(m:ℝ) ≤ A/4096 ∧
      delta*((censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet:ℝ)+1) ≤ A/640000 := by
  let A := tune.budget κ₁ dimension Ep precision loss*(loss*gain/((Ep:ℝ)+1))
  have hA : 0 < A := by dsimp only [A]; exact mul_pos (tune.budget_pos _ _ _ _ _) (by positivity)
  have hEp : 0 < (Ep:ℝ)+1 := by positivity
  have hubEq : ubOf tune κ₁ dimension Ep precision loss gain=κ₁*A/4096 := by
    dsimp only [ubOf,A]
    field_simp
  have hgridEq : gridFineOf tune κ₁ dimension Ep precision loss gain=A/512 := by
    dsimp only [gridFineOf,A]
    field_simp
  have hm : (0:ℝ) < m := by
    by_contra hn
    have hzero : (m:ℝ)=0 := le_antisymm (not_lt.mp hn) (Nat.cast_nonneg _)
    rw [hzero,mul_zero] at hgrid
    norm_num at hgrid
  have hS : 0 < tune.slack := zero_lt_one.trans_le tune.one_le_slack
  have htolEq : tolOf tune κ₁ dimension Ep precision loss gain=A/(10000*tune.slack) := by
    dsimp only [tolOf,A]
    field_simp
  refine ⟨?_,?_,?_⟩
  · rw [hubEq]
    have hκA : κ₁*A ≤ A := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hκ1 hA.le
    exact div_le_div_of_nonneg_right hκA (by norm_num)
  · rw [div_le_iff₀ hm]
    rw [hgridEq] at hgrid
    nlinarith only [hgrid]
  · let F := (censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet:ℝ)
    have hF : 0 ≤ F := Nat.cast_nonneg _
    have hSlack : 64*(F+1) ≤ tune.slack := hslack
    rw [htolEq] at hdelta
    calc
      _ ≤ A/(10000*tune.slack)*(F+1) := mul_le_mul_of_nonneg_right hdelta (by linarith only [hF])
      _ ≤ _ := by
        rw [div_mul_eq_mul_div,div_le_div_iff₀ (by positivity) (by norm_num)]
        have hh := mul_le_mul_of_nonneg_left hSlack hA.le
        nlinarith only [hh]

/-- The actual front census rate fits the much smaller native row
allowance, rather than only the final display coefficient allowance. -/
theorem native_sample_brow_rate
    (tune : Tuning) {κ₁ dimension precision loss gain delta : ℝ} {Ep m : ℕ}
    (hv : NativeDesign.Valid κ₁ dimension precision loss)
    (hbudget : tune.budget κ₁ dimension Ep precision loss=NativeDesign.budget κ₁ dimension Ep precision loss)
    (hgain : 0 < gain) (hdelta0 : 0 ≤ delta) (hslack : censusSlack ≤ tune.slack)
    (hdelta : delta ≤ tolOf tune κ₁ dimension Ep precision loss gain)
    (hgrid : 8 ≤ gridFineOf tune κ₁ dimension Ep precision loss gain*m) :
    72*delta+1806*(3*delta*(censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet:ℝ)+
      ubOf tune κ₁ dimension Ep precision loss gain+1/(m:ℝ))+
      18*ubOf tune κ₁ dimension Ep precision loss gain ≤
      98/100*(NativeDesign.regularityCoeff κ₁ dimension Ep precision loss*gain/1000) := by
  have hFront := NativeDesign.front_budget_room (Ep:=Ep) hv
  obtain ⟨_hd0,_hd1,_hκ,hκ1,_hprecision,hloss,hloss1⟩ := hv
  obtain ⟨hub,hgridRate,hdeltaRate⟩ := sample_budget_rate_bounds tune hκ1 hloss hgain hslack hdelta hgrid
  let A := tune.budget κ₁ dimension Ep precision loss*(loss*gain/((Ep:ℝ)+1))
  let B := tune.budget κ₁ dimension Ep precision loss
  let F := (censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet:ℝ)
  have hF : 0 ≤ F := Nat.cast_nonneg _
  have hD : 0 < NativeDesign.regularityCoeff κ₁ dimension Ep precision loss :=
    NativeDesign.regularityCoeff_pos κ₁ dimension hloss
  have hB := tune.budget_pos κ₁ dimension Ep precision loss
  have hcoef := NativeDesign.coefficient_le_regularity κ₁ dimension (Ep:=Ep) (precision:=precision) hloss
  have hEp : (1:ℝ) ≤ (Ep:ℝ)+1 := by linarith only [Nat.cast_nonneg (α := ℝ) Ep]
  have hdisplay : loss*gain/((Ep:ℝ)+1) ≤ gain := by
    rw [div_le_iff₀ (zero_lt_one.trans_le hEp)]
    have h1 := mul_le_mul_of_nonneg_right hloss1 hgain.le
    have h2 := mul_le_mul_of_nonneg_left hEp hgain.le
    nlinarith only [h1,h2]
  have hBsmall : B ≤ NativeDesign.regularityCoeff κ₁ dimension Ep precision loss/1000 := by
    change 1000000*NativeDesign.budget κ₁ dimension Ep precision loss ≤ _ at hFront
    rw [←hbudget] at hFront
    dsimp only [B]
    linarith only [hFront,hcoef,hD]
  have hA : A ≤ NativeDesign.regularityCoeff κ₁ dimension Ep precision loss*gain/1000 := by
    calc
      _ ≤ B*gain := mul_le_mul_of_nonneg_left hdisplay hB.le
      _ ≤ _ := by simpa only [div_mul_eq_mul_div] using mul_le_mul_of_nonneg_right hBsmall hgain.le
  have hA0 : 0 ≤ A := by dsimp only [A]; positivity
  have hdeltaCost : 72*delta+5418*(delta*F) ≤ 5418*(delta*(F+1)) := by
    nlinarith only [hdelta0]
  have hrate : 72*delta+1806*(3*delta*F+ubOf tune κ₁ dimension Ep precision loss gain+1/(m:ℝ))+
      18*ubOf tune κ₁ dimension Ep precision loss gain ≤ 98/100*A := by
    change _ ≤ A/4096 at hub hgridRate
    change delta*(F+1) ≤ A/640000 at hdeltaRate
    linarith only [hub,hgridRate,hdeltaRate,hdeltaCost,hA0]
  exact hrate.trans (mul_le_mul_of_nonneg_left hA (by norm_num))

/-- The actual MK4 row bound fits the literal row constant of the
native scale assembly, uniformly before the later path and census. -/
theorem eventually_native_sample_brow_le
    (tune : Tuning) (N : ℕ → ℝ) (hN : Tendsto N atTop atTop)
    {κ₁ dimension precision loss gain delta L : ℝ} {Ep m : ℕ}
    (hv : NativeDesign.Valid κ₁ dimension precision loss)
    (hbudget : tune.budget κ₁ dimension Ep precision loss=NativeDesign.budget κ₁ dimension Ep precision loss)
    (hgain : 0 < gain) (hL : 0 < L) (hdelta0 : 0 ≤ delta) (hslack : censusSlack ≤ tune.slack)
    (hdelta : delta ≤ tolOf tune κ₁ dimension Ep precision loss gain)
    (hgrid : 8 ≤ gridFineOf tune κ₁ dimension Ep precision loss gain*m) :
    let ub := ubOf tune κ₁ dimension Ep precision loss gain
    let rhoC := 3*delta*(censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet:ℝ)+ub+1/(m:ℝ)
    ∃ sigma : ℝ, 0 < sigma ∧ sigma ≤ 1 ∧ ∀ᶠ k in atTop,
      ∀ κ source Kc tau : ℝ, 1 ≤ κ → κ ≤ N k^sigma → 1 ≤ source → source ≤ N k^sigma →
        1 ≤ Kc → Kc ≤ N k^(rhoC*L) → 0 ≤ tau → tau ≤ delta*L →
        28*mk4Kg κ (2*source) Kc
          (64*(max κ source)^2*κ*4^dimension*N k^(2*(delta*L)+(tau+2*delta*L)+tau))
          (κ⁻¹/512) (N k^(-(ub*L))) (delta*L) (N k)^6 ≤
          N k^((NativeDesign.regularityCoeff κ₁ dimension Ep precision loss*gain/1000)*L) := by
  have hrate := native_sample_brow_rate tune hv hbudget hgain hdelta0 hslack hdelta hgrid
  obtain ⟨_hd0,hd1,hκ,_hκ1,_hprecision,hloss,_hloss1⟩ := hv
  have hub : 0 ≤ ubOf tune κ₁ dimension Ep precision loss gain := by
    dsimp only [ubOf]
    have hB := tune.budget_pos κ₁ dimension Ep precision loss
    positivity
  have hrho : 0 ≤ 3*delta*(censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet:ℝ)+
      ubOf tune κ₁ dimension Ep precision loss gain+1/(m:ℝ) := by positivity
  have hD : 0 < NativeDesign.regularityCoeff κ₁ dimension Ep precision loss*gain/1000 :=
    div_pos (mul_pos (NativeDesign.regularityCoeff_pos κ₁ dimension hloss) hgain) (by norm_num)
  exact eventually_brow_le N hN hL hdelta0 hub hrho hD hd1.le hrate

/-- Absorb the factor two from the actual dyadic theta ceiling using
the same native source threshold, including the case of zero precision index. -/
theorem native_theta_le_coefficient_power
    {N h deltaL theta : ℝ} (hN : 1 ≤ N) (hh : 0 < h)
    (hlarge : 20000 ≤ N^(h/1000000)) (hdelta : deltaL ≤ h/10000000)
    (htheta : theta ≤ 2*N^(4*deltaL)) : theta ≤ N^h := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  calc
    _ ≤ 2*N^(4*deltaL) := htheta
    _ ≤ N^(h/1000000)*N^(4*deltaL) := mul_le_mul_of_nonneg_right
      (by linarith only [hlarge] : (2:ℝ) ≤ N^(h/1000000)) (Real.rpow_nonneg hNp.le _)
    _ = N^(h/1000000+4*deltaL) := (Real.rpow_add hNp _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith only [hh,hdelta])

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
