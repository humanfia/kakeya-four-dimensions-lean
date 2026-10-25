/-
Adapted from: here:o064
Written in this workspace by session x0217, from the supplied paper,
Lemma a03:actual-lists. No external formal code.
-/

import Submission.Lib.K4OriginalLists.ContinuousLists
import Submission.Lib.K4OriginalLists.SignVariation

/-!
Polynomial cell averaging with all discrete tags retained jointly.  The error
depends on total tagged density and the number of polynomial boundaries, and
is independent of the number of possible tags and of the analytical mask.
-/

namespace Submission.Lib.K4OriginalLists

open Finset MeasureTheory Set

variable {X β : Type*} [MeasurableSpace X] [Fintype β]

/-- Averaging a vector of densities contracts its total absolute mass. -/
theorem sum_abs_integral_le (ν : Measure X) [IsProbabilityMeasure ν]
    (p : X → β → ℝ) (hp : ∀ a, Integrable (fun x => p x a) ν)
    (H : ℝ) (hbound : ∀ x, ∑ a, |p x a| ≤ H) :
    (∑ a, |∫ x, p x a ∂ν|) ≤ H := by
  classical
  calc
    _ ≤ ∑ a, ∫ x, |p x a| ∂ν := sum_le_sum fun a _ => abs_integral_le_integral_abs
    _ = ∫ x, ∑ a, |p x a| ∂ν :=
      (integral_finsetSum _ (fun a _ => (hp a).abs)).symm
    _ ≤ ∫ _x : X, H ∂ν :=
      integral_mono (integrable_finsetSum _ (fun a _ => (hp a).abs)) (integrable_const _) hbound
    _ = H := by simp

/-- A vector and its cell mean have absolute difference at most twice the density bound. -/
theorem sum_abs_sub_integral_le (ν : Measure X) [IsProbabilityMeasure ν]
    (p : X → β → ℝ) (hp : ∀ a, Integrable (fun x => p x a) ν)
    (H : ℝ) (hbound : ∀ x, ∑ a, |p x a| ≤ H) (x : X) :
    (∑ a, |p x a - ∫ y, p y a ∂ν|) ≤ 2 * H := by
  calc
    _ ≤ ∑ a, (|p x a| + |∫ y, p y a ∂ν|) :=
      sum_le_sum fun a _ => abs_sub _ _
    _ = (∑ a, |p x a|) + ∑ a, |∫ y, p y a ∂ν| := sum_add_distrib
    _ ≤ 2 * H := by linarith [hbound x, sum_abs_integral_le ν p hp H hbound]

/-- A cell mean agrees with the original density away from polynomial boundaries.
Only a neighborhood of the real roots can contribute to the averaging error. -/
theorem sign_cell_averaging_error_le {m : ℕ}
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (C : Set ℝ)
    (p : Fin m → Polynomial ℝ) (rule : (Fin m → Bool) → β → ℝ) (H ρ : ℝ)
    (hbound : ∀ s, ∑ a, |rule s a| ≤ H)
    (hsupport : ∀ᵐ x ∂ν, x ∈ C)
    (hdiam : ∀ x ∈ C, ∀ y ∈ C, |x - y| ≤ |ρ|) :
    (∫⁻ x, ENNReal.ofReal (∑ a,
      |rule (fun i => decide (0 ≤ (p i).eval x)) a -
        ∫ y, rule (fun i => decide (0 ≤ (p i).eval y)) a ∂ν|) ∂ν) ≤
      ENNReal.ofReal (2 * H) * ν (signRootNeighborhood p ρ) := by
  classical
  let f : ℝ → β → ℝ := fun x => rule (fun i => decide (0 ≤ (p i).eval x))
  let S := signRootNeighborhood p ρ
  have hp : ∀ a, Integrable (fun x => f x a) ν :=
    integrable_polynomial_sign_rule_component ν p rule H hbound
  have hpoint : ∀ᵐ x ∂ν, ENNReal.ofReal (∑ a, |f x a - ∫ y, f y a ∂ν|) ≤
      ENNReal.ofReal (2 * H) * S.indicator 1 x := by
    filter_upwards [hsupport] with x hx
    by_cases hxS : x ∈ S
    · simpa [indicator_of_mem hxS] using ENNReal.ofReal_le_ofReal
        (sum_abs_sub_integral_le ν f hp H (fun x => hbound _) x)
    · have hmean (a : β) : (∫ y, f y a ∂ν) = f x a := by
        calc
          _ = ∫ _y : ℝ, f x a ∂ν := by
            apply integral_congr_ae
            filter_upwards [hsupport] with y hy
            exact (congrFun (sign_rule_eq_of_not_mem_rootNeighborhood p rule ρ x y hxS
              (hdiam x hx y hy)) a).symm
          _ = f x a := by simp
      simp [hmean, indicator_of_notMem hxS]
  change (∫⁻ x, ENNReal.ofReal (∑ a, |f x a - ∫ y, f y a ∂ν|) ∂ν) ≤ _
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (2 * H) * S.indicator 1 x ∂ν := lintegral_mono_ae hpoint
    _ = ENNReal.ofReal (2 * H) * ∫⁻ x, S.indicator 1 x ∂ν :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (2 * H) * ν S :=
      mul_le_mul_of_nonneg_left (lintegral_indicator_one_le S) zero_le

/-- The total error over disjoint observation cells is at most a fixed constant times
density, total polynomial degree, and cell width.  The cells may be any dominated family. -/
theorem sign_cell_averaging_total_error_le {m : ℕ} {ι : Type*} [Fintype ι]
    (ν : ι → Measure ℝ) [∀ c, IsProbabilityMeasure (ν c)]
    (C : ι → Set ℝ) (w : ι → ENNReal)
    (p : Fin m → Polynomial ℝ) (rule : (Fin m → Bool) → β → ℝ) (H ρ : ℝ)
    (hbound : ∀ s, ∑ a, |rule s a| ≤ H)
    (hsupport : ∀ c, ∀ᵐ x ∂ν c, x ∈ C c)
    (hdiam : ∀ c x, x ∈ C c → ∀ y ∈ C c, |x - y| ≤ |ρ|)
    (hdom : (∑ c, w c • ν c) ≤ volume) :
    (∑ c, w c * ∫⁻ x, ENNReal.ofReal (∑ a,
      |rule (fun i => decide (0 ≤ (p i).eval x)) a -
        ∫ y, rule (fun i => decide (0 ≤ (p i).eval y)) a ∂ν c|) ∂ν c) ≤
      ENNReal.ofReal (4 * H * (∑ i, ((p i).natDegree : ℝ)) * |ρ|) := by
  classical
  let S := signRootNeighborhood p ρ
  have hS : MeasurableSet S := measurableSet_signRootNeighborhood p ρ
  have hH : 0 ≤ H :=
    (sum_nonneg (fun a _ => abs_nonneg (rule (fun _ => false) a))).trans (hbound _)
  have hdomS : (∑ c, w c * ν c S) ≤ volume S := by
    simpa [Measure.sum_apply, hS] using (Measure.le_iff.mp hdom S hS)
  calc
    _ ≤ ∑ c, w c * (ENNReal.ofReal (2 * H) * ν c S) := by
      apply sum_le_sum
      intro c _
      exact mul_le_mul_of_nonneg_left
        (sign_cell_averaging_error_le (ν c) (C c) p rule H ρ hbound (hsupport c) (hdiam c)) zero_le
    _ = ENNReal.ofReal (2 * H) * ∑ c, w c * ν c S := by
      rw [mul_sum]
      apply sum_congr rfl
      intro c _
      ac_rfl
    _ ≤ ENNReal.ofReal (2 * H) * volume S := mul_le_mul_of_nonneg_left hdomS zero_le
    _ ≤ ENNReal.ofReal (2 * H) *
        ENNReal.ofReal (2 * (∑ i, ((p i).natDegree : ℝ)) * |ρ|) :=
      mul_le_mul_of_nonneg_left (volume_signRootNeighborhood_le p ρ) zero_le
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * H)]
      congr 1
      ring

/-- Real-valued form of the joint cell-averaging estimate. -/
theorem sign_cell_averaging_total_error_real_le {m : ℕ} {ι : Type*} [Fintype ι]
    (ν : ι → Measure ℝ) [∀ c, IsProbabilityMeasure (ν c)]
    (C : ι → Set ℝ) (w : ι → ℝ) (hw : ∀ c, 0 ≤ w c)
    (p : Fin m → Polynomial ℝ) (rule : (Fin m → Bool) → β → ℝ) (H ρ : ℝ)
    (hbound : ∀ s, ∑ a, |rule s a| ≤ H)
    (hsupport : ∀ c, ∀ᵐ x ∂ν c, x ∈ C c)
    (hdiam : ∀ c x, x ∈ C c → ∀ y ∈ C c, |x - y| ≤ |ρ|)
    (hdom : (∑ c, ENNReal.ofReal (w c) • ν c) ≤ volume) :
    (∑ c, w c * ∫ x, ∑ a,
      |rule (fun i => decide (0 ≤ (p i).eval x)) a -
        ∫ y, rule (fun i => decide (0 ≤ (p i).eval y)) a ∂ν c| ∂ν c) ≤
      4 * H * (∑ i, ((p i).natDegree : ℝ)) * |ρ| := by
  classical
  let f : ℝ → β → ℝ := fun x => rule (fun i => decide (0 ≤ (p i).eval x))
  have hp : ∀ c a, Integrable (fun x => f x a) (ν c) :=
    fun c => integrable_polynomial_sign_rule_component (ν c) p rule H hbound
  have herrint (c : ι) : Integrable (fun x => ∑ a, |f x a - ∫ y, f y a ∂ν c|) (ν c) :=
    integrable_finsetSum _ (fun a _ => ((hp c a).sub (integrable_const _)).abs)
  have herrnn (c : ι) : 0 ≤ᵐ[ν c] (fun x => ∑ a, |f x a - ∫ y, f y a ∂ν c|) :=
    Filter.Eventually.of_forall (fun _ => sum_nonneg (fun _ _ => abs_nonneg _))
  have heq : ENNReal.ofReal (∑ c, w c * ∫ x, ∑ a, |f x a - ∫ y, f y a ∂ν c| ∂ν c) =
      ∑ c, ENNReal.ofReal (w c) *
        ∫⁻ x, ENNReal.ofReal (∑ a, |f x a - ∫ y, f y a ∂ν c|) ∂ν c := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun c _ =>
      mul_nonneg (hw c) (integral_nonneg (fun _ => sum_nonneg (fun _ _ => abs_nonneg _))))]
    apply sum_congr rfl
    intro c _
    rw [ENNReal.ofReal_mul (hw c), ofReal_integral_eq_lintegral_ofReal (herrint c) (herrnn c)]
  have hH : 0 ≤ H :=
    (sum_nonneg (fun a _ => abs_nonneg (rule (fun _ => false) a))).trans (hbound _)
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity :
    0 ≤ 4 * H * (∑ i, ((p i).natDegree : ℝ)) * |ρ|)).mp
  rw [heq]
  exact sign_cell_averaging_total_error_le ν C (fun c => ENNReal.ofReal (w c))
    p rule H ρ hbound hsupport hdiam hdom

end Submission.Lib.K4OriginalLists
