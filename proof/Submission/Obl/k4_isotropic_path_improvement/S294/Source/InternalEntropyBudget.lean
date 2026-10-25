-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.InternalEntropyBudget, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.Skeleton
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.InternalStateBudgets

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

noncomputable section

/-- The actual front entropy is a small multiple of the tunable
internal allowance, including the rounding of C and the grid error.
The depth factor cancels against the gain cap before any path data. -/
theorem front_entropy_le_internal_power
    (tune : Tuning) {κ₁ d₁ precision loss gain L δ₀ : ℝ} {Ep m C : ℕ}
    (hκ : 0 < κ₁) (hκ1 : κ₁ ≤ 1) (hd0 : 0 ≤ d₁) (hd1 : d₁ < 1)
    (hprecision : 1 ≤ precision) (hloss : 0 < loss) (hgain : 0 < gain)
    (hL : 0 ≤ L) (hgainCap : gain ≤ gainCap tune κ₁ d₁ Ep precision loss)
    (hm : 0 < m) (hgm : 8 ≤ gain*(m:ℝ)) (hδ : δ₀ ≤ gain/100)
    (hC : (C:ℝ) ≤ windowOf tune κ₁ d₁ Ep precision loss gain*(m:ℝ)+1) :
    entropyOf C m (ueOf tune κ₁ d₁ Ep precision loss gain δ₀ L) ≤
      tune.budget κ₁ d₁ Ep precision loss*(loss*gain*L/((Ep:ℝ)+1))/2^20 := by
  let E := (Ep:ℝ)+1
  let X := E*precision+3
  let D := tune.depth κ₁ d₁ Ep precision loss
  let B := tune.budget κ₁ d₁ Ep precision loss
  let a := X*gain*D/κ₁
  have hE : 1 ≤ E := by dsimp only [E]; linarith [Nat.cast_nonneg (α := ℝ) Ep]
  have hEp : 0 < E := zero_lt_one.trans_le hE
  have hX : 1 ≤ X := by dsimp only [X]; nlinarith
  have hD : 1 ≤ D := tune.one_le_depth _ _ _ _ _
  have hB : 0 < B := tune.budget_pos _ _ _ _ _
  have hDp : 0 < D := zero_lt_one.trans_le hD
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hap : 0 < a := by dsimp only [a]; positivity
  have hd : 0 < 1-d₁ := by linarith
  have hdle : 1-d₁ ≤ 1 := by linarith
  have hga : gain ≤ a := by
    dsimp only [a]
    rw [le_div_iff₀ hκ]
    have hXD : 1 ≤ X*D := one_le_mul_of_one_le_of_one_le hX hD
    nlinarith only [mul_le_mul_of_nonneg_left hκ1 hgain.le,
      mul_le_mul_of_nonneg_right hXD hgain.le]
  have hcap : gain*(2^48*E*X^2*D^2) ≤ loss*(1-d₁)^2*κ₁^2*B := by
    apply (le_div_iff₀ (by positivity : (0:ℝ)<2^48*E*X^2*D^2)).mp
    simpa only [gainCap,E,X,D,B] using hgainCap
  have hcapA : 2^48*E*a^2 ≤ loss*gain*(1-d₁)^2*B := by
    calc
      _ = (gain*(2^48*E*X^2*D^2))*(gain/κ₁^2) := by
        dsimp only [a]
        field_simp
      _ ≤ (loss*(1-d₁)^2*κ₁^2*B)*(gain/κ₁^2) :=
        mul_le_mul_of_nonneg_right hcap (by positivity)
      _ = _ := by field_simp
  have hwin : windowOf tune κ₁ d₁ Ep precision loss gain=1024*a/(1-d₁) := by
    dsimp only [windowOf,a,X,E,D]
    field_simp
  have hpal : paletteExpOf tune κ₁ d₁ Ep precision loss gain L=4*a*L := by
    dsimp only [paletteExpOf,a,X,E,D]
    ring
  have hwinGain : gain ≤ windowOf tune κ₁ d₁ Ep precision loss gain := by
    rw [hwin,le_div_iff₀ hd]
    have hh : gain*(1-d₁) ≤ gain := mul_le_of_le_one_right hgain.le hdle
    linarith only [hh,hga,hap]
  have hmR : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hstep : 1/(m:ℝ) ≤ gain/8 := by
    rw [div_le_div_iff₀ hmR (by norm_num : (0:ℝ)<8)]
    linarith
  have hCm : (C:ℝ)/(m:ℝ) ≤ 2*windowOf tune κ₁ d₁ Ep precision loss gain := by
    have hround : (C:ℝ)/(m:ℝ) ≤ windowOf tune κ₁ d₁ Ep precision loss gain+1/(m:ℝ) := by
      rw [div_le_iff₀ hmR]
      have heq : (1/(m:ℝ))*(m:ℝ)=1 := by field_simp
      nlinarith only [hC,heq]
    linarith
  have hue : ueOf tune κ₁ d₁ Ep precision loss gain δ₀ L ≤ 8*a*L := by
    rw [ueOf,hpal]
    nlinarith only [mul_le_mul_of_nonneg_right hδ hL,
      mul_le_mul_of_nonneg_right hga hL,mul_nonneg hap.le hL]
  have hentropy : entropyOf C m (ueOf tune κ₁ d₁ Ep precision loss gain δ₀ L) ≤
      2^26*a^2*L/(1-d₁) := by
    unfold entropyOf
    calc
      _ ≤ 4096*((C:ℝ)/(m:ℝ))*(8*a*L) :=
        mul_le_mul_of_nonneg_left hue (by positivity)
      _ ≤ 4096*(2*windowOf tune κ₁ d₁ Ep precision loss gain)*(8*a*L) := by gcongr
      _ = _ := by rw [hwin]; ring
  apply hentropy.trans
  have hden : 0 < E*2^20 := by positivity
  have hbound : 2^26*a^2*L/(1-d₁) ≤ B*loss*gain*L/(E*2^20) := by
    rw [div_le_div_iff₀ hd hden]
    calc
      _ = 2^46*(E*a^2*L) := by ring
      _ ≤ 2^48*(E*a^2*L) := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = (2^48*E*a^2)*L := by ring
      _ ≤ (loss*gain*(1-d₁)^2*B)*L := mul_le_mul_of_nonneg_right hcapA hL
      _ ≤ (loss*gain*(1-d₁)*B)*L := by
        have hh : (1-d₁)^2 ≤ 1-d₁ := by
          rw [pow_two]
          exact mul_le_of_le_one_right hd.le hdle
        gcongr
      _ = _ := by ring
  exact hbound.trans_eq (by dsimp only [E,B]; field_simp)

/-- A divisor up to 5000 leaves the quarter-allowance required by the
actual record/state factory. -/
theorem front_entropy_le_internal_quarter
    {entropy amplitude divisor : ℝ} (hamp : 0 ≤ amplitude)
    (hdivisor : 0 < divisor) (hdivisorMax : divisor ≤ 5000)
    (hentropy : entropy ≤ amplitude/2^20) :
    entropy ≤ (amplitude/divisor)/4 := by
  apply hentropy.trans
  rw [div_div,div_le_div_iff₀ (by positivity : (0:ℝ)<2^20) (by positivity)]
  nlinarith

/-- The actual doubled pure tolerance fits the same small internal
allowance. This uses the budget factor in tolOf, not the final display
allowance, and keeps the arbitrary late front budget separate. -/
theorem doubled_tau_fits_internal_budget
    (tune : Tuning) {κ₁ d₁ precision loss gain L δ₀ front divisor : ℝ} {Ep : ℕ}
    (hloss : 0 < loss) (hgain : 0 < gain) (hL : 0 < L) (hfront : 0 < front)
    (hdivisor : 0 < divisor) (hdivisorMax : divisor ≤ 5000)
    (hδ : δ₀ ≤ tolOf tune κ₁ d₁ Ep precision loss gain) :
    2*tauOf tune δ₀ L front ≤
      2*min front (tune.budget κ₁ d₁ Ep precision loss*
        (loss*gain*L/((Ep:ℝ)+1))/divisor)/tune.slack := by
  have hs : 0 < tune.slack := zero_lt_one.trans_le tune.one_le_slack
  have hB : 0 < tune.budget κ₁ d₁ Ep precision loss := tune.budget_pos _ _ _ _ _
  have hEp : 0 < (Ep:ℝ)+1 := by positivity
  let amplitude := tune.budget κ₁ d₁ Ep precision loss*(loss*gain*L/((Ep:ℝ)+1))
  have hamp : 0 < amplitude := by dsimp only [amplitude]; positivity
  have htFront : tauOf tune δ₀ L front*tune.slack ≤ front/1024 := by
    unfold tauOf
    calc
      _ ≤ (front/(1024*tune.slack))*tune.slack :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hs.le
      _ = _ := by field_simp
  have htInternal : tauOf tune δ₀ L front*tune.slack ≤ amplitude/divisor := by
    have hδL : δ₀*L*tune.slack ≤ amplitude/10000 := by
      have hh := mul_le_mul_of_nonneg_right hδ (by positivity : (0:ℝ)≤L*tune.slack)
      have heq : tolOf tune κ₁ d₁ Ep precision loss gain*(L*tune.slack)=amplitude/10000 := by
        dsimp only [tolOf,amplitude]
        field_simp
      nlinarith
    have hdiv : amplitude/10000 ≤ amplitude/divisor :=
      div_le_div_of_nonneg_left hamp.le hdivisor (by linarith)
    exact (mul_le_mul_of_nonneg_right
      (min_le_left (δ₀*L) (front/(1024*tune.slack))) hs.le).trans (hδL.trans hdiv)
  rw [le_div_iff₀ hs]
  have hh : tauOf tune δ₀ L front*tune.slack ≤ min front (amplitude/divisor) :=
    le_min (htFront.trans (by linarith)) htInternal
  change 2*tauOf tune δ₀ L front*tune.slack ≤ 2*min front (amplitude/divisor)
  nlinarith

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
