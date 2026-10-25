-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.FixedLateClock, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/FixedLateClock.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.RelativeOldClock
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.LateOldPathScales

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent

namespace LateOldScales

/-- The rounded later level has a relative depth in ONE grid step of a
fixed target. This keeps the native clock exponent fixed before the grid. -/
theorem exists_late_level_fixed_clock {m : ℕ} {κ precision gain δ : ℝ}
    (hm : 0 < m) (hκ : 0 < κ) (_hκ1 : κ ≤ 1) (hprecision : 1 ≤ precision)
    (hgain : 0 < gain) (hfirst : (m : ℝ)⁻¹ ≤ gain) (hδ : δ ≤ gain)
    (hsmall : (((precision+2)/κ)+8)*gain ≤ 1/8) :
    ∃ level : ℕ, 0 < level ∧ level < m ∧
      ((precision+2)/κ)*gain ≤ ((level : ℝ)+1)/(m : ℝ) ∧
      ((level : ℝ)+1)/(m : ℝ) ≤ (((precision+2)/κ)+2)*gain ∧
      ((level : ℝ)+1)/(m : ℝ)+2*δ ≤ 1/8 ∧
      precision*gain+gain ≤ κ*(((level : ℝ)+1)/(m : ℝ))-δ ∧
      ((level : ℝ)+1)/(m : ℝ)+δ+2*gain ≤ 1 ∧
      (precision+2)*gain ≤ κ*(((level : ℝ)+1)/(m : ℝ)-(m : ℝ)⁻¹) ∧
      κ*(((level : ℝ)+1)/(m : ℝ)-(m : ℝ)⁻¹) ≤ (precision+2)*gain+κ*(m : ℝ)⁻¹ := by
  let A := (precision+2)/κ
  let level := ⌈A*gain*(m : ℝ)⌉₊
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hA : 0 < A := by dsimp [A]; positivity
  have hceilLo : A*gain*(m : ℝ) ≤ (level : ℝ) := Nat.le_ceil _
  have hceilHi : (level : ℝ) < A*gain*(m : ℝ)+1 := Nat.ceil_lt_add_one (by positivity)
  have hlo : A*gain ≤ (level : ℝ)/(m : ℝ) := (le_div_iff₀ hmR).mpr hceilLo
  have hhi : (level : ℝ)/(m : ℝ) ≤ A*gain+(m : ℝ)⁻¹ := by
    apply (div_le_iff₀ hmR).mpr
    have hi : (m : ℝ)⁻¹*(m : ℝ)=1 := inv_mul_cancel₀ hmR.ne'
    nlinarith only [hceilHi,hi]
  have hrelative : ((level : ℝ)+1)/(m : ℝ)-(m : ℝ)⁻¹=(level : ℝ)/(m : ℝ) := by
    rw [←one_div]
    ring
  have hdepth : ((level : ℝ)+1)/(m : ℝ)=(level : ℝ)/(m : ℝ)+(m : ℝ)⁻¹ := by
    rw [←one_div]
    ring
  have hinv : 0 ≤ (m : ℝ)⁻¹ := by positivity
  have hslo : A*gain ≤ ((level : ℝ)+1)/(m : ℝ) := by rw [hdepth]; linarith only [hlo,hinv]
  have hshi : ((level : ℝ)+1)/(m : ℝ) ≤ (A+2)*gain := by rw [hdepth]; nlinarith only [hhi,hfirst]
  have hlp : 0 < level := by
    have hh : (0 : ℝ) < level := lt_of_lt_of_le (by positivity : 0 < A*gain*(m : ℝ)) hceilLo
    exact_mod_cast hh
  have hlm : level < m := by
    have hh : ((level : ℝ)+1)/(m : ℝ) < 1 := by
      change (A+8)*gain ≤ 1/8 at hsmall
      nlinarith only [hshi,hsmall,hgain]
    rw [div_lt_one hmR] at hh
    exact_mod_cast (show (level : ℝ) < m by linarith only [hh])
  have hκA : κ*(A*gain)=(precision+2)*gain := by dsimp [A]; field_simp
  have hscaled := mul_le_mul_of_nonneg_left hslo hκ.le
  rw [hκA] at hscaled
  refine ⟨level,hlp,hlm,hslo,hshi,?_,?_,?_,?_,?_⟩
  · change (A+8)*gain ≤ 1/8 at hsmall
    nlinarith only [hshi,hsmall,hδ,hgain]
  · nlinarith only [hscaled,hδ]
  · change (A+8)*gain ≤ 1/8 at hsmall
    nlinarith only [hshi,hsmall,hδ,hgain]
  · rw [hrelative]
    simpa only [hκA] using mul_le_mul_of_nonneg_left hlo hκ.le
  · rw [hrelative]
    have hh := mul_le_mul_of_nonneg_left hhi hκ.le
    rw [mul_add,hκA] at hh
    exact hh

end LateOldScales

namespace ParentSource

open Native MeasureTheory

noncomputable section

/-- Choose ONE later level before every actual path. Its qualification
clock exponent is the FIXED precision+2 at analytic base N^(gain L);
only the already small original grid error enters its multiplicative K. -/
theorem WidePreparationGrid.exists_fixed_late_clock
    {κ₁ ρ S η χ windowFactor precision : ℝ}
    (q : WidePreparationGrid κ₁ ρ S η χ windowFactor)
    (hκ : 0 < κ₁) (hκ1 : κ₁ ≤ 1) (hprecision : 1 ≤ precision)
    (_hχ : 0 < χ) (hχ1 : χ ≤ 1)
    (hfirst : (q.m : ℝ)⁻¹+2*q.δ₀ ≤ χ*q.gain)
    (hsmall : (((precision+2)/κ₁)+8)*q.gain ≤ 1/8) :
    ∃ level : ℕ, 0 < level ∧ level < q.m ∧
      ((precision+2)/κ₁)*q.gain ≤ transferScale q.m level ∧
      transferScale q.m level ≤ (((precision+2)/κ₁)+2)*q.gain ∧
      transferScale q.m level+2*q.δ₀ ≤ 1/8 ∧
      precision*q.gain+q.gain ≤ κ₁*transferScale q.m level-q.δ₀ ∧
      transferScale q.m level+q.δ₀+2*q.gain ≤ 1 ∧
      ∀ {W : ℕ} {N L σ : ℝ} {p : PathData W}
        {ω : Fin W → ℝ} {ν : Fin W → Measure Ln} {E : Fin W → Set Ev}
        {B : Fin W → ℝ} {f : ℝ → ℝ} {Mp Dp : ℕ},
      p.Valid N L ω ν E B f κ₁ q.m (transferScale q.m) q.δ₀ Mp Dp σ →
      1 ≤ N → 0 ≤ L → ∀ K : ℝ, N^(χ*q.gain*L) ≤ K →
      p.T 0 ≤ p.T level ∧
        (N^(q.gain*L))^(-(precision+2))/K ≤ ((2 : ℝ)^(p.T level-p.T 0))⁻¹ ∧
        ((2 : ℝ)^(p.T level-p.T 0))⁻¹ ≤ K*(N^(q.gain*L))^(-(precision+2)) := by
  have hg : 0 < q.gain := q.valid.2.1
  have hδ : 0 < q.δ₀ := q.valid.2.2.2.1
  have hmR : (0 : ℝ) < q.m := Nat.cast_pos.mpr q.valid.1.1
  have hinv : 0 ≤ (q.m : ℝ)⁻¹ := by positivity
  have hχg : χ*q.gain ≤ q.gain := mul_le_of_le_one_left hg.le hχ1
  have hfirstg : (q.m : ℝ)⁻¹ ≤ q.gain := by linarith only [hfirst,hδ,hχg]
  have hδg : q.δ₀ ≤ q.gain := by linarith only [hfirst,hδ,hinv,hχg]
  obtain ⟨level,hl0,hlm,hlo,hhi,hearly,hclock,hroom,hrelLo,hrelHi⟩ :=
    LateOldScales.exists_late_level_fixed_clock q.valid.1.1 hκ hκ1 hprecision hg hfirstg hδg hsmall
  have hs0 : transferScale q.m 0=(q.m : ℝ)⁻¹ := by simp [transferScale,one_div]
  change ((precision+2)/κ₁)*q.gain ≤ transferScale q.m level at hlo
  change transferScale q.m level ≤ (((precision+2)/κ₁)+2)*q.gain at hhi
  change transferScale q.m level+2*q.δ₀ ≤ 1/8 at hearly
  change precision*q.gain+q.gain ≤ κ₁*transferScale q.m level-q.δ₀ at hclock
  change transferScale q.m level+q.δ₀+2*q.gain ≤ 1 at hroom
  change (precision+2)*q.gain ≤ κ₁*(transferScale q.m level-(q.m : ℝ)⁻¹) at hrelLo
  change κ₁*(transferScale q.m level-(q.m : ℝ)⁻¹) ≤
    (precision+2)*q.gain+κ₁*(q.m : ℝ)⁻¹ at hrelHi
  rw [←hs0] at hrelLo hrelHi
  have herror : κ₁*(q.m : ℝ)⁻¹+2*q.δ₀ ≤ χ*q.gain := by
    linarith only [hfirst,mul_le_of_le_one_left hinv hκ1]
  refine ⟨level,hl0,hlm,hlo,hhi,hearly,hclock,hroom,?_⟩
  intro W N L σ p ω ν E B f Mp Dp hp hN hL K hK
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hKp : 0 < K := (Real.rpow_pos_of_pos hNp _).trans_le hK
  have hgap : 2*q.δ₀ ≤ κ₁*(transferScale q.m level-transferScale q.m 0) := by
    nlinarith only [hrelLo,hprecision,hg,hfirst,hχg,hinv]
  obtain ⟨hT,hdyadic⟩ := hp.relative_old_clock_dyadic hN hL 0 level q.valid.1.1 hlm hgap
  obtain ⟨hpathLo,hpathHi⟩ := hp.relative_old_clock_bounds hNp 0 level q.valid.1.1 hlm
  rw [hdyadic] at hpathLo hpathHi
  have hbase : (N^(q.gain*L))^(-(precision+2))=N^(-((precision+2)*q.gain*L)) := by
    rw [←Real.rpow_mul hNp.le]
    congr 1
    ring
  refine ⟨hT,?_,?_⟩
  · rw [hbase]
    apply le_trans _ hpathLo
    calc
      _ ≤ N^(-((precision+2)*q.gain*L))/N^(χ*q.gain*L) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hK
      _ = N^(-(((precision+2)*q.gain+χ*q.gain)*L)) := by
        rw [←Real.rpow_sub hNp]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by
        have hh : κ₁*(transferScale q.m level-transferScale q.m 0)+2*q.δ₀ ≤
            (precision+2)*q.gain+χ*q.gain := by
          rw [hs0] at hrelHi ⊢
          linarith only [hrelHi,herror]
        nlinarith only [mul_le_mul_of_nonneg_right hh hL])
  · rw [hbase]
    apply hpathHi.trans
    calc
      _ ≤ N^(χ*q.gain*L)*N^(-((precision+2)*q.gain*L)) := by
        rw [←Real.rpow_add hNp]
        apply Real.rpow_le_rpow_of_exponent_le hN
        have hh : (precision+2)*q.gain-χ*q.gain ≤
            κ₁*(transferScale q.m level-transferScale q.m 0)-2*q.δ₀ := by
          nlinarith only [hrelLo,hfirst,hinv]
        nlinarith only [mul_le_mul_of_nonneg_right hh hL]
      _ ≤ _ := mul_le_mul_of_nonneg_right hK (by positivity)

end
end ParentSource

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent
