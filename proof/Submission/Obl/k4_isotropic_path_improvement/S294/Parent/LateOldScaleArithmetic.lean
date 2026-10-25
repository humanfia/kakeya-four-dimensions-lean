-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.LateOldScaleArithmetic, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/LateOldScaleArithmetic.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Mathlib

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent

open Set

namespace LateOldScales

/-- A supplied uniform grid has a later level at any prescribed fixed
multiple of the gain. Its first level can remain arbitrarily shallow. -/
theorem exists_late_level {m : ℕ} {gain A : ℝ}
    (hm : 0 < m) (hgain : 0 < gain) (hA : 0 ≤ A)
    (hfirst : (m : ℝ)⁻¹ ≤ gain) (hsmall : (A+2)*gain < 1) :
    ∃ level : ℕ, level < m ∧
      A*gain ≤ ((level : ℝ)+1)/(m : ℝ) ∧
      ((level : ℝ)+1)/(m : ℝ) ≤ (A+2)*gain := by
  let level := ⌈A*gain*(m : ℝ)⌉₊
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hlo : A*gain*(m : ℝ) ≤ (level : ℝ) := Nat.le_ceil _
  have hhi : (level : ℝ) < A*gain*(m : ℝ)+1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hfirst' : 1 ≤ gain*(m : ℝ) := by
    rw [← one_div,div_le_iff₀ hmR] at hfirst
    exact hfirst
  have hlevelUpper : ((level : ℝ)+1)/(m : ℝ) ≤ (A+2)*gain := by
    apply (div_le_iff₀ hmR).mpr
    nlinarith only [hhi,hfirst']
  have hlevelReal : (level : ℝ) < m := by
    have hlt := hlevelUpper.trans_lt hsmall
    rw [div_lt_one hmR] at hlt
    linarith
  refine ⟨level,by exact_mod_cast hlevelReal,?_,hlevelUpper⟩
  exact (le_div_iff₀ hmR).mpr (by linarith)

/-- The required polynomial degree depends on the positive clock
exponent alone, before precision, loss, or gain are chosen. -/
theorem exists_qualification_degree {κ : ℝ} (hκ : 0 < κ) :
    ∃ M : ℕ, 2 ≤ M ∧ 2 ≤ (M : ℝ)*κ := by
  obtain ⟨M,hM⟩ := exists_nat_gt (2/κ)
  refine ⟨max 2 M,le_max_left _ _,?_⟩
  have hM' : 2 ≤ (M : ℝ)*κ := (div_le_iff₀ hκ).mp hM.le
  exact hM'.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_right 2 M) hκ.le)

/-- A late old depth proportional to the gain simultaneously leaves
the middle quarter available and puts its clock below the requested
accuracy scale. The multiplier is fixed before choosing the gain. -/
theorem exists_late_level_with_budgets {m : ℕ} {κ precision gain δ : ℝ}
    (hm : 0 < m) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hprecision : 1 ≤ precision)
    (hgain : 0 < gain) (hfirst : (m : ℝ)⁻¹ ≤ gain) (hδ : δ ≤ gain)
    (hsmall : (((precision+2)/κ)+8)*gain ≤ 1/8) :
    ∃ level : ℕ, 0 < level ∧ level < m ∧
      ((precision+2)/κ)*gain ≤ ((level : ℝ)+1)/(m : ℝ) ∧
      ((level : ℝ)+1)/(m : ℝ) ≤ (((precision+2)/κ)+2)*gain ∧
      ((level : ℝ)+1)/(m : ℝ) ≤ 1/8 ∧
      precision*gain+gain ≤ κ*(((level : ℝ)+1)/(m : ℝ))-δ ∧
      ((level : ℝ)+1)/(m : ℝ)+δ+2*gain ≤ 1 := by
  let A := (precision+2)/κ
  have hA : 0 < A := by dsimp [A]; positivity
  have hA3 : 3 ≤ A := (le_div_iff₀ hκ).mpr (by nlinarith only [hκ1,hprecision])
  have hsmall' : (A+2)*gain < 1 := by change (A+8)*gain ≤ 1/8 at hsmall; nlinarith only [hsmall,hgain]
  obtain ⟨level,hlm,hlo,hhi⟩ := exists_late_level hm hgain hA.le hfirst hsmall'
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hlevelPos : 0 < level := by
    by_contra h
    have hl0 : level=0 := by omega
    rw [hl0,Nat.cast_zero,zero_add] at hlo
    have hfirst' : 1/(m : ℝ) ≤ gain := by simpa only [one_div] using hfirst
    have hAgain := mul_le_mul_of_nonneg_right hA3 hgain.le
    nlinarith only [hlo,hfirst',hAgain,hgain]
  have hscaled : (precision+2)*gain ≤ κ*(((level : ℝ)+1)/(m : ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left hlo hκ.le
    have heq : κ*(A*gain)=(precision+2)*gain := by
      dsimp only [A]
      field_simp [hκ.ne']
    rwa [heq] at hh
  refine ⟨level,hlevelPos,hlm,hlo,hhi,?_,?_,?_⟩
  · change (A+8)*gain ≤ 1/8 at hsmall
    nlinarith only [hhi,hsmall,hgain]
  · nlinarith only [hscaled,hδ]
  · change (A+8)*gain ≤ 1/8 at hsmall
    nlinarith only [hhi,hsmall,hδ,hgain]

/-- The same arbitrarily shallow root bounds used by the actual row
factory pay the clock-change error for any fixed qualification degree. -/
theorem shallow_root_error_budget {M : ℕ} {κ χ gain sRoot δ : ℝ}
    (hκ : κ ≤ 1) (hgain : 0 ≤ gain) (hroot : 0 ≤ sRoot)
    (hχ : χ*((M : ℝ)+1) ≤ 1) (hfirst : sRoot+2*δ ≤ χ*gain) :
    (M : ℝ)*κ*sRoot+(2*(M : ℝ)+2)*δ ≤ gain := by
  have hM : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
  have hκM : (M : ℝ)*κ ≤ (M : ℝ)+1 := by nlinarith only [hκ,hM]
  have hcompare := mul_le_mul_of_nonneg_right hκM hroot
  have hscale := mul_le_mul_of_nonneg_left hfirst (by positivity : (0 : ℝ) ≤ (M : ℝ)+1)
  have hχscale := mul_le_mul_of_nonneg_right hχ hgain
  nlinarith only [hcompare,hscale,hχscale]

/-- One native polynomial fit in the shallow clock is accurate enough
on the later old block, with a whole gain power left to pay constants.
Only the actual path clock and width bounds enter the inequality. -/
theorem polynomial_clock_error_budget
    {N L κ gain precision sOld sRoot δ h hRoot a ζ : ℝ} {M : ℕ}
    (hN : 1 ≤ N) (hL : 0 ≤ L) (hκ : 0 < κ) (hgain : 0 < gain)
    (hprecision : 1 ≤ precision) (hOld : 0 ≤ sOld)
    (hM : 1 ≤ (M : ℝ)*κ)
    (hdepth : (precision+2)*gain ≤ κ*sOld)
    (hroot : (M : ℝ)*κ*sRoot+(2*(M : ℝ)+2)*δ ≤ gain)
    (hh : 0 ≤ h) (hhRoot : 0 < hRoot)
    (hclock : h ≤ N^(-((κ*sOld-δ)*L)))
    (hrootClock : N^(-((κ*sRoot+δ)*L)) ≤ hRoot)
    (hwidth : N^(-((sOld+δ)*L)) ≤ a)
    (hzeta : N^(-(precision*gain*L)) ≤ ζ) :
    N^(gain*L)*h*(h/hRoot)^M ≤ a*ζ := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hratio : h/hRoot ≤ N^((-κ*sOld+κ*sRoot+2*δ)*L) := by
    calc
      _ ≤ N^(-((κ*sOld-δ)*L))/hRoot := div_le_div_of_nonneg_right hclock hhRoot.le
      _ ≤ N^(-((κ*sOld-δ)*L))/N^(-((κ*sRoot+δ)*L)) :=
        div_le_div_of_nonneg_left (by positivity)
          (Real.rpow_pos_of_pos hNp _) hrootClock
      _ = _ := by rw [← Real.rpow_sub hNp]; congr 1; ring
  have hdegree : sOld ≤ (M : ℝ)*κ*sOld := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hM hOld
  have hbudget : precision*gain+2*gain+sOld ≤ ((M : ℝ)+1)*κ*sOld := by
    nlinarith only [hdegree,hdepth]
  have hexponent : gain-(κ*sOld-δ)+(-κ*sOld+κ*sRoot+2*δ)*(M : ℝ) ≤
      -(sOld+δ)-precision*gain := by
    nlinarith only [hbudget,hroot]
  have ha : 0 ≤ a := (Real.rpow_pos_of_pos hNp _).le.trans hwidth
  calc
    _ ≤ N^(gain*L)*N^(-((κ*sOld-δ)*L))*(N^((-κ*sOld+κ*sRoot+2*δ)*L))^M := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hclock (by positivity)
      · exact pow_le_pow_left₀ (div_nonneg hh hhRoot.le) hratio M
      · exact pow_nonneg (div_nonneg hh hhRoot.le) M
      · positivity
    _ = N^((gain-(κ*sOld-δ)+(-κ*sOld+κ*sRoot+2*δ)*(M : ℝ))*L) := by
      rw [← Real.rpow_mul_natCast hNp.le,← Real.rpow_add hNp,← Real.rpow_add hNp]
      congr 1
      ring
    _ ≤ N^(-((sOld+δ)*L))*N^(-(precision*gain*L)) := by
      rw [← Real.rpow_add hNp]
      apply Real.rpow_le_rpow_of_exponent_le hN
      nlinarith only [mul_le_mul_of_nonneg_right hexponent hL]
    _ ≤ a*ζ := mul_le_mul hwidth hzeta (by positivity) ha

/-- The row accuracy can also be fixed before the gain: a fixed
multiple for the old depth determines a sufficient accuracy exponent. -/
theorem row_error_budget
    {N L gain precision oldMultiplier accuracy sOld δ h a ζ : ℝ}
    (hN : 1 ≤ N) (hL : 0 ≤ L) (hgain : 0 < gain)
    (hdepth : sOld ≤ oldMultiplier*gain) (htolerance : δ ≤ gain)
    (haccuracy : oldMultiplier+precision+2 ≤ accuracy)
    (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hwidth : N^(-((sOld+δ)*L)) ≤ a)
    (hzeta : N^(-(precision*gain*L)) ≤ ζ) :
    N^(gain*L)*h*N^(-(accuracy*gain*L)) ≤ a*ζ := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have ha : 0 ≤ a := (Real.rpow_pos_of_pos hNp _).le.trans hwidth
  have hexponent : gain-accuracy*gain ≤ -(sOld+δ)-precision*gain := by
    nlinarith only [mul_le_mul_of_nonneg_right haccuracy hgain.le,hdepth,htolerance]
  calc
    _ ≤ N^(gain*L)*1*N^(-(accuracy*gain*L)) := by gcongr
    _ = N^((gain-accuracy*gain)*L) := by rw [mul_one,← Real.rpow_add hNp]; congr 1; ring
    _ ≤ N^(-((sOld+δ)*L))*N^(-(precision*gain*L)) := by
      rw [← Real.rpow_add hNp]
      apply Real.rpow_le_rpow_of_exponent_le hN
      nlinarith only [mul_le_mul_of_nonneg_right hexponent hL]
    _ ≤ a*ζ := mul_le_mul hwidth hzeta (by positivity) ha

end LateOldScales

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent
