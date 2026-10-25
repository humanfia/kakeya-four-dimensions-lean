-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.NativeClockCutoffs, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.NativeClockScales

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set

/-- Exact dyadic rounding preserves polynomial cutoff floors with
one fixed positive power of slack. -/
theorem dyadic_round_power_bounds {N query X Y margin : ℝ} (hN : 1<N)
    (hquery : 0<query) (hquery1 : query≤1)
    (hlo : N^(-X)≤query) (hhi : query≤N^(-Y))
    (hlarge : 2≤N^margin) :
    N^(-(X+margin))≤dyadicParameterWidth (parameterLevel query) ∧
      dyadicParameterWidth (parameterLevel query)≤N^(-Y) := by
  have hNp : 0<N := zero_lt_one.trans hN
  have hh := parameterLevel_width query hquery hquery1
  refine ⟨?_,hh.2.trans hhi⟩
  calc
    _=N^(-X)/N^margin := by
      rw [←Real.rpow_sub hNp]
      congr 1
      ring
    _≤N^(-X)/2 := div_le_div_of_nonneg_left
      (Real.rpow_nonneg hNp.le _) (by norm_num) hlarge
    _≤query/2 := div_le_div_of_nonneg_right hlo (by norm_num)
    _≤_ := hh.1

/-- The two native dyadic cutoffs at the literal child clock.
Their polynomial floors are uniform over the actual clock exponent. -/
theorem exists_native_clock_cutoffs {N lower upper D margin : ℝ}
    (hN : 1<N) (T : ℕ) (hlower : 0<lower) (hD : 1≤D)
    (hclockLo : lower≤nativeClockExponent N T)
    (hclockHi : nativeClockExponent N T≤upper)
    (P : ℕ) (hP : 1≤P) (hlarge : 2≤N^margin) :
    let Z := upper*D+margin
    let R := (P:ℝ)*Z+margin
    ∃ (zeta : ℝ) (world : ℕ),
      0<zeta ∧ zeta≤1 ∧
      zeta≤(((2:ℝ)^T)⁻¹)^D ∧
      N^(-Z)≤zeta ∧ zeta≤N^(-(lower*D)) ∧
      N^(-R)≤dyadicParameterWidth world ∧
      dyadicParameterWidth world≤N^(-((P:ℝ)*lower*D)) ∧
      dyadicParameterWidth world≤zeta := by
  intro Z R
  have hNp : 0<N := zero_lt_one.trans hN
  have hDp : 0<D := zero_lt_one.trans_le hD
  let lam := ((2:ℝ)^T)⁻¹
  have hlam : 0<lam := by dsimp only [lam]; positivity
  have hlam1 : lam≤1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
  let query := lam^D
  have hquery : 0<query := Real.rpow_pos_of_pos hlam _
  have hquery1 : query≤1 := Real.rpow_le_one hlam.le hlam1 hDp.le
  have hqueryEq : query=N^(-nativeClockExponent N T*D) := by
    dsimp only [query,lam]
    rw [←nativeClockExponent_width hN,←Real.rpow_mul hNp.le]
  have hqueryLo : N^(-(upper*D))≤query := by
    rw [hqueryEq]
    exact Real.rpow_le_rpow_of_exponent_le hN.le (by nlinarith)
  have hqueryHi : query≤N^(-(lower*D)) := by
    rw [hqueryEq]
    exact Real.rpow_le_rpow_of_exponent_le hN.le (by nlinarith)
  let zeta := dyadicParameterWidth (parameterLevel query)
  have hzeta : 0<zeta := dyadicParameterWidth_pos _
  have hzeta1 : zeta≤1 := (parameterLevel_width query hquery hquery1).2.trans hquery1
  have hzetaQuery : zeta≤query := (parameterLevel_width query hquery hquery1).2
  have hzetaPower := dyadic_round_power_bounds hN hquery hquery1 hqueryLo hqueryHi hlarge
  have hzetaLower : N^(-Z)≤zeta := hzetaPower.1
  have hzetaUpper : zeta≤N^(-(lower*D)) := hzetaPower.2
  let queryR := zeta^(P:ℝ)
  have hP0 : (0:ℝ)≤P := Nat.cast_nonneg _
  have hP1 : (1:ℝ)≤P := by exact_mod_cast hP
  have hqueryR : 0<queryR := Real.rpow_pos_of_pos hzeta _
  have hqueryR1 : queryR≤1 := Real.rpow_le_one hzeta.le hzeta1 hP0
  have hqueryRLo : N^(-((P:ℝ)*Z))≤queryR := by
    calc
      _=(N^(-Z))^(P:ℝ) := by rw [←Real.rpow_mul hNp.le]; congr 1; ring
      _≤queryR := Real.rpow_le_rpow (Real.rpow_nonneg hNp.le (-Z)) hzetaLower hP0
  have hqueryRHi : queryR≤N^(-((P:ℝ)*lower*D)) := by
    calc
      queryR≤(N^(-(lower*D)))^(P:ℝ) := Real.rpow_le_rpow hzeta.le hzetaUpper hP0
      _=_ := by rw [←Real.rpow_mul hNp.le]; congr 1; ring
  have hRpower := dyadic_round_power_bounds hN hqueryR hqueryR1 hqueryRLo hqueryRHi hlarge
  have hqueryRzeta : queryR≤zeta := by
    dsimp only [queryR]
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge hzeta hzeta1 hP1
  refine ⟨zeta,parameterLevel queryR,hzeta,hzeta1,hzetaQuery,hzetaLower,hzetaUpper,
    ?_,hRpower.2,?_⟩
  · simpa only [R] using hRpower.1
  · exact (parameterLevel_width queryR hqueryR hqueryR1).2.trans hqueryRzeta

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
