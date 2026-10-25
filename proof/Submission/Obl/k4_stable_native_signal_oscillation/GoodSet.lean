import Submission.Obl.k4_stable_native_signal_oscillation.RootCorrection
import Submission.Obl.k4_stable_native_signal_oscillation.BasePolynomials

namespace Submission.Obl.k4_stable_native_signal_oscillation
open MvPolynomial MeasureTheory Set
open Submission.Obl.k4_quadratic_atlas_normalization

noncomputable def baseValue (F : MvPolynomial (Fin 3) ℝ) (u : BasePoint) : ℝ :=
  eval (fun i => u i) F

lemma continuous_baseValue (F : MvPolynomial (Fin 3) ℝ) : Continuous (baseValue F) :=
  (MvPolynomial.continuous_eval F).comp (by fun_prop)

noncomputable def goodSet (K a : ℝ) (P S : MvPolynomial (Fin 4) ℝ) : Set NativePoint :=
  {p | ‖nativeBase p‖ ≤ K ∧ |value P p| ≤ K * a ∧
    K⁻¹ ≤ |value (pderiv 3 P) p| ∧ |value (pderiv 3 P) p| ≤ K ∧
    |curvature P 3| ≤ K / a ∧ |value S p| ≤ K ∧
    |value (pderiv 3 S) p| ≤ K ∧ |curvature S 3| ≤ K}

lemma measurableSet_goodSet (K a : ℝ) (P S : MvPolynomial (Fin 4) ℝ) :
    MeasurableSet (goodSet K a P S) := by
  apply MeasurableSet.inter
  · exact measurableSet_le measurable_nativeBase.norm measurable_const
  apply MeasurableSet.inter
  · exact measurableSet_le (continuous_value P).abs.measurable measurable_const
  apply MeasurableSet.inter
  · exact measurableSet_le measurable_const (continuous_value (pderiv 3 P)).abs.measurable
  apply MeasurableSet.inter
  · exact measurableSet_le (continuous_value (pderiv 3 P)).abs.measurable measurable_const
  apply MeasurableSet.inter
  · exact MeasurableSet.const _
  apply MeasurableSet.inter
  · exact measurableSet_le (continuous_value S).abs.measurable measurable_const
  apply MeasurableSet.inter
  · exact measurableSet_le (continuous_value (pderiv 3 S)).abs.measurable measurable_const
  exact MeasurableSet.const _

lemma snoc_nativeBase (p : NativePoint) (w : ℝ) :
    (Fin.snoc (fun j : Fin 3 => nativeBase p j) w : Fin 4 → ℝ) =
      Function.update (fun i => p i) 3 w := by
  funext i
  fin_cases i <;> rfl

lemma snoc_nativeBase_self (p : NativePoint) :
    (Fin.snoc (fun j : Fin 3 => nativeBase p j) (p 3) : Fin 4 → ℝ) = (fun i => p i) := by
  rw [snoc_nativeBase]
  exact Function.update_eq_self _ _

lemma center_signal_error (P S : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (hS : S.totalDegree ≤ 2) {K a : ℝ}
    (hK : 2 ≤ K) (ha : 0 < a) (ha1 : a ≤ 1)
    (hc : (K ^ 5 * a)⁻¹ ≤ |curvature P 3|) {p : NativePoint}
    (hp : p ∈ goodSet K a P S) :
    |baseValue (centerSignal P S) (nativeBase p) - value S p| ≤ K ^ 14 * a := by
  have hK0 : 0 < K := by linarith
  have hc0 : curvature P 3 ≠ 0 := abs_pos.mp ((by positivity : 0 < (K ^ 5 * a)⁻¹).trans_le hc)
  have he := eval_centerPoly P hP hc0 (fun j : Fin 3 => nativeBase p j) (p 3)
  rw [snoc_nativeBase_self] at he
  unfold baseValue
  rw [eval_centerSignal, he, snoc_nativeBase]
  exact hiddenCenter_signal_error P S hS (fun i => p i) 3 hK ha ha1 hc
    hp.2.2.2.1 hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2

lemma signal_bound_from_error {K a x y : ℝ} (hK : 2 ≤ K) (ha1 : a ≤ 1)
    (he : |x - y| ≤ K ^ 14 * a) (hy : |y| ≤ K) : |x| ≤ K ^ 15 := by
  have hK0 : 0 ≤ K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hb : K ≤ K ^ 14 := by
    simpa using pow_le_pow_right₀ hK1 (by decide : 1 ≤ 14)
  calc
    |x| = |(x - y) + y| := by congr 1; ring
    _ ≤ |x - y| + |y| := abs_add_le _ _
    _ ≤ K ^ 14 * a + K := add_le_add he hy
    _ ≤ K ^ 14 * 1 + K ^ 14 := add_le_add
      (mul_le_mul_of_nonneg_left ha1 (pow_nonneg hK0 _)) hb
    _ = K ^ 14 + K ^ 14 := by ring
    _ = 2 * K ^ 14 := by ring
    _ ≤ K * K ^ 14 := mul_le_mul_of_nonneg_right hK (pow_nonneg hK0 _)
    _ = K ^ 15 := by ring

lemma absorb_signal_error {K a r : ℝ} {c C : ℕ} (hK : 2 ≤ K)
    (ha : 0 ≤ a) (hr : 0 ≤ r) (hc : c ≤ C) (hC : 15 ≤ C) :
    2 * K ^ 14 * a + K ^ c * r ≤ K ^ C * (a + r) := by
  have hK0 : 0 ≤ K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hfirst : 2 * K ^ 14 ≤ K ^ C := by
    calc
      _ ≤ K * K ^ 14 := mul_le_mul_of_nonneg_right hK (pow_nonneg hK0 _)
      _ = K ^ 15 := by ring
      _ ≤ K ^ C := pow_le_pow_right₀ hK1 hC
  calc
    _ = (2 * K ^ 14) * a + K ^ c * r := by ring
    _ ≤ K ^ C * a + K ^ C * r := add_le_add
      (mul_le_mul_of_nonneg_right hfirst ha)
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hK1 hc) hr)
    _ = K ^ C * (a + r) := by ring

end Submission.Obl.k4_stable_native_signal_oscillation
