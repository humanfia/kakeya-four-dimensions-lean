import Submission.Obl.k4_stable_native_signal_oscillation.Hidden

namespace Submission.Obl.k4_stable_native_signal_oscillation
open MvPolynomial MeasureTheory
open Submission.Obl.k4_quadratic_atlas_normalization

/-- A rationalized quadratic-formula correction, with no division by the curvature. -/
noncomputable def rootStep (r d c : ℝ) : ℝ :=
  -2 * r / (d + if 0 ≤ d then Real.sqrt (d ^ 2 - 2 * c * r)
    else -Real.sqrt (d ^ 2 - 2 * c * r))

lemma rootStep_spec {r d c : ℝ} (hd : d ≠ 0) (hD : 0 < d ^ 2 - 2 * c * r) :
    r + d * rootStep r d c + c * (rootStep r d c) ^ 2 / 2 = 0 ∧
    d + c * rootStep r d c ≠ 0 ∧
    |rootStep r d c| ≤ 2 * |r| / |d| := by
  let s : ℝ := if 0 ≤ d then Real.sqrt (d ^ 2 - 2 * c * r)
    else -Real.sqrt (d ^ 2 - 2 * c * r)
  have hs : s ^ 2 = d ^ 2 - 2 * c * r := by
    dsimp [s]
    split_ifs <;> simp [Real.sq_sqrt hD.le]
  have heabs : |d| ≤ |d + s| := by
    dsimp [s]
    split_ifs with hd0
    · rw [abs_of_nonneg hd0, abs_of_nonneg (add_nonneg hd0 (Real.sqrt_nonneg _))]
      linarith [Real.sqrt_nonneg (d ^ 2 - 2 * c * r)]
    · have hd0' : d < 0 := lt_of_not_ge hd0
      rw [abs_of_neg hd0', abs_of_neg (by linarith [Real.sqrt_nonneg (d ^ 2 - 2 * c * r)] :
        d + -Real.sqrt (d ^ 2 - 2 * c * r) < 0)]
      linarith [Real.sqrt_nonneg (d ^ 2 - 2 * c * r)]
  have he : d + s ≠ 0 := abs_pos.mp ((abs_pos.mpr hd).trans_le heabs)
  have hr : r + d * rootStep r d c + c * (rootStep r d c) ^ 2 / 2 = 0 := by
    change r + d * (-2 * r / (d + s)) + c * (-2 * r / (d + s)) ^ 2 / 2 = 0
    field_simp
    linear_combination r * hs
  refine ⟨hr, ?_, ?_⟩
  · intro hz
    have hsq : (d + c * rootStep r d c) ^ 2 = d ^ 2 - 2 * c * r := by
      linear_combination 2 * c * hr
    rw [hz, zero_pow (by decide : 2 ≠ 0)] at hsq
    linarith
  · change |-2 * r / (d + s)| ≤ _
    rw [abs_div, abs_mul]
    norm_num
    exact div_le_div_of_nonneg_left (by positivity) (abs_pos.mpr hd) heabs

abbrev NativePoint := EuclideanSpace ℝ (Fin 4)
abbrev BasePoint := EuclideanSpace ℝ (Fin 3)

noncomputable def nativeBase (p : NativePoint) : BasePoint :=
  WithLp.toLp 2 ![p 0, p 1, p 2]

noncomputable def value (P : MvPolynomial (Fin 4) ℝ) (p : NativePoint) : ℝ :=
  eval (fun i => p i) P

lemma continuous_value (P : MvPolynomial (Fin 4) ℝ) : Continuous (value P) := by
  exact (MvPolynomial.continuous_eval P).comp (by fun_prop)

lemma measurable_nativeBase : Measurable nativeBase := by
  apply Continuous.measurable
  unfold nativeBase
  fun_prop

noncomputable def rootLift (P : MvPolynomial (Fin 4) ℝ) (p : NativePoint) : NativePoint :=
  WithLp.toLp 2 (Function.update (fun i => p i) 3
    (p 3 + rootStep (value P p) (value (pderiv 3 P) p) (curvature P 3)))

lemma measurable_rootLift (P : MvPolynomial (Fin 4) ℝ) : Measurable (rootLift P) := by
  apply (WithLp.measurable_toLp 2 _).comp
  apply Measurable.of_eval
  intro i
  by_cases hi : i = 3
  · subst i
    simp only [Function.update_self]
    unfold rootStep
    have hr := (continuous_value P).measurable
    have hd := (continuous_value (pderiv 3 P)).measurable
    exact (by fun_prop : Measurable (fun p : NativePoint => p 3)).add
      (((measurable_const.mul hr).div
        (hd.add (Measurable.ite (measurableSet_le measurable_const hd)
          ((hd.pow_const 2).sub (measurable_const.mul hr)).sqrt
          (((hd.pow_const 2).sub (measurable_const.mul hr)).sqrt.neg)))))
  · simp only [Function.update_of_ne hi]
    fun_prop

lemma nativeBase_rootLift (P : MvPolynomial (Fin 4) ℝ) (p : NativePoint) :
    nativeBase (rootLift P p) = nativeBase p := by
  simp [nativeBase, rootLift]

lemma rootLift_spec (P S : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (hS : S.totalDegree ≤ 2) {K a : ℝ}
    (hK : 2 ≤ K) (ha : 0 < a) (ha1 : a ≤ 1)
    (hc : |curvature P 3| ≤ (K ^ 5 * a)⁻¹) (p : NativePoint)
    (hr : |value P p| ≤ K * a) (hd : K⁻¹ ≤ |value (pderiv 3 P) p|)
    (hS1 : |value (pderiv 3 S) p| ≤ K) (hS2 : |curvature S 3| ≤ K) :
    value P (rootLift P p) = 0 ∧ value (pderiv 3 P) (rootLift P p) ≠ 0 ∧
    |value S (rootLift P p) - value S p| ≤ K ^ 14 * a := by
  have hK0 : 0 < K := by linarith
  have hd0 : value (pderiv 3 P) p ≠ 0 :=
    abs_pos.mp ((inv_pos.mpr hK0).trans_le hd)
  have hsmall := small_curvature_error hK ha hc hr
  have hd2 : (K⁻¹) ^ 2 ≤ (value (pderiv 3 P) p) ^ 2 := by
    calc
      _ ≤ |value (pderiv 3 P) p| ^ 2 := pow_le_pow_left₀ (by positivity) hd 2
      _ = (value (pderiv 3 P) p) ^ 2 := sq_abs _
  have hD : 0 < (value (pderiv 3 P) p) ^ 2 - 2 * curvature P 3 * value P p := by
    have hh := le_abs_self (curvature P 3 * value P p)
    rw [abs_mul] at hh
    have hk2 : 0 < (K⁻¹) ^ 2 := by positivity
    nlinarith
  obtain ⟨hroot, hsimple, hdist⟩ := rootStep_spec hd0 hD
  have ht := quadratic_coordinate_taylor P hP (fun i => p i) 3
    (rootStep (value P p) (value (pderiv 3 P) p) (curvature P 3))
  have hder := quadratic_coordinate_derivative P hP (fun i => p i) 3
    (rootStep (value P p) (value (pderiv 3 P) p) (curvature P 3))
  refine ⟨ht.trans hroot, ?_, ?_⟩
  · change eval (Function.update (fun i => p i) 3
      (p 3 + rootStep (value P p) (value (pderiv 3 P) p) (curvature P 3))) (pderiv 3 P) ≠ 0
    rw [hder]
    exact hsimple
  · have hp : 2 * K ^ 2 ≤ K ^ 6 := by
      calc
        _ ≤ K * K ^ 2 := mul_le_mul_of_nonneg_right hK (sq_nonneg K)
        _ = K ^ 3 := by ring
        _ ≤ K ^ 6 := pow_le_pow_right₀ (by linarith) (by decide : 3 ≤ 6)
    have hh := hdist.trans ((residual_ratio hK0 ha.le hr hd).trans
      (mul_le_mul_of_nonneg_right hp ha.le))
    exact signal_error_power S hS (fun i => p i) 3 hK ha.le ha1 hS1 hS2 hh

end Submission.Obl.k4_stable_native_signal_oscillation
