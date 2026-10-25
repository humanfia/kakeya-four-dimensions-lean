-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.NativeClockScales, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.SnapshotDyadicScales

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set

noncomputable section

/-- The native base exponent of the literal relative child clock. -/
def nativeClockExponent (N : ℝ) (T : ℕ) : ℝ := Real.logb N ((2:ℝ)^T)

/-- No time rounding is needed: the actual child clock is the native
qualification clock at this exponent. -/
theorem nativeClockExponent_width {N : ℝ} (hN : 1 < N) (T : ℕ) :
    N^(-nativeClockExponent N T)=((2:ℝ)^T)⁻¹ := by
  rw [nativeClockExponent,Real.rpow_neg (zero_lt_one.trans hN).le,
    Real.rpow_logb (zero_lt_one.trans hN) hN.ne' (by positivity)]

theorem nativeClockExponent_pos {N : ℝ} (hN : 1 < N) {T : ℕ} (hT : 0 < T) :
    0 < nativeClockExponent N T := by
  exact Real.logb_pos hN (one_lt_pow₀ (by norm_num : (1:ℝ)<2) (by omega : T≠0))

/-- Polynomial clock bounds give polynomial native exponent bounds,
uniformly over all packets and roots. -/
theorem nativeClockExponent_bounds {N lower upper : ℝ} (hN : 1 < N) (T : ℕ)
    (hlo : N^(-upper) ≤ ((2:ℝ)^T)⁻¹) (hhi : ((2:ℝ)^T)⁻¹ ≤ N^(-lower)) :
    lower ≤ nativeClockExponent N T ∧ nativeClockExponent N T ≤ upper := by
  rw [←nativeClockExponent_width hN] at hlo hhi
  have hlo' := (Real.rpow_le_rpow_left_iff hN).mp hlo
  have hhi' := (Real.rpow_le_rpow_left_iff hN).mp hhi
  constructor <;> linarith

/-- The exact native time-scale range follows automatically from
nonnegative analytic slack, at the actual child clock exponent. -/
theorem nativeClockExponent_time_range {N alpha : ℝ} (hN : 1 < N) (T : ℕ)
    (hT : 0 < T) (halpha : 0 ≤ alpha) :
    N^(-nativeClockExponent N T)/(N^(nativeClockExponent N T*alpha)) ≤ ((2:ℝ)^T)⁻¹ ∧
      ((2:ℝ)^T)⁻¹ ≤ (N^(nativeClockExponent N T*alpha))*N^(-nativeClockExponent N T) := by
  have hscale : 1 ≤ N^(nativeClockExponent N T*alpha) :=
    Real.one_le_rpow hN.le (mul_nonneg (nativeClockExponent_pos hN hT).le halpha)
  rw [nativeClockExponent_width hN]
  constructor
  · exact div_le_self (by positivity) hscale
  · exact (le_mul_iff_one_le_left (by positivity : 0 < ((2:ℝ)^T)⁻¹)).mpr hscale

/-- The dyadic scalar cutoff rounds the actual analytic clock power
by at most two, with its inequality in the needed direction. -/
theorem nativeClock_scalar_cutoff {N cZeta : ℝ} (hN : 1 < N) (T : ℕ)
    (hcZeta : 0 < cZeta) :
    let query := (((2:ℝ)^T)⁻¹)^cZeta
    let zeta := dyadicParameterWidth (parameterLevel query)
    0 < zeta ∧ zeta ≤ 1 ∧ zeta ≤ query ∧ query/2 ≤ zeta := by
  let query := (((2:ℝ)^T)⁻¹)^cZeta
  have hq : 0 < query := Real.rpow_pos_of_pos (by positivity) _
  have hq1 : query ≤ 1 := Real.rpow_le_one (by positivity)
    (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1:ℝ)≤2))) hcZeta.le
  have hh := parameterLevel_width query hq hq1
  exact ⟨dyadicParameterWidth_pos _,hh.2.trans hq1,hh.2,hh.1⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
