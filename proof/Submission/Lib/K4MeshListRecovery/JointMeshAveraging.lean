import Submission.Lib.K4OriginalLists
import Submission.Lib.K4ModelReduction.CoordinateAveraging

/-!
Adapted from: here:o064

Joint tagged errors for the actual mesh-averaging operator.  All components
share the same polynomial boundaries, so their total density controls the
error without a factor for the number of tags.
-/

namespace Submission.Lib.K4MeshListRecovery

open Finset MeasureTheory Set
open Submission.Lib.K4OriginalLists Submission.Lib.K4ModelReduction

theorem ofReal_integral_joint_error
    {X β : Type*} [MeasurableSpace X] [Fintype β]
    (μ : Measure X) (f g : β → X → ℝ)
    (hf : ∀ a, Integrable (f a) μ) (hg : ∀ a, Integrable (g a) μ) :
    ENNReal.ofReal (∫ x, ∑ a, |f a x - g a x| ∂μ) =
      ∑ a, densityL1Distance μ (f a) (g a) := by
  have hsum : (∫ x, ∑ a, |f a x - g a x| ∂μ) = ∑ a, ∫ x, |f a x - g a x| ∂μ :=
    integral_finsetSum _ (fun a _ => ((hf a).sub (hg a)).abs)
  rw [hsum,
    ENNReal.ofReal_sum_of_nonneg (fun a _ => integral_nonneg (fun _ => abs_nonneg _))]
  apply sum_congr rfl
  intro a _
  exact ofReal_integral_eq_lintegral_ofReal ((hf a).sub (hg a)).abs
    (Filter.Eventually.of_forall (fun _ => abs_nonneg _))

/-- The actual scalar mesh operator has the same joint sign-vector bound as
averaging over a prescribed finite family of cells. -/
theorem meshAverage_sign_vector_error
    {m : ℕ} {β : Type*} [Fintype β]
    (p : Fin m → Polynomial ℝ) (rule : (Fin m → Bool) → β → ℝ)
    (H : ℝ) (hbound : ∀ s, ∑ a, |rule s a| ≤ H)
    {ρ : ℝ} (hρ : 0 < ρ) :
    (∫⁻ x : ℝ, ENNReal.ofReal (∑ a,
      |meshAverage (fun y => rule (fun i => decide (0 ≤ (p i).eval y)) a) ρ x -
        rule (fun i => decide (0 ≤ (p i).eval x)) a|)) ≤
      ENNReal.ofReal (4 * H * (∑ i, ((p i).natDegree : ℝ)) * ρ) := by
  classical
  let f : ℝ → β → ℝ := fun x => rule (fun i => decide (0 ≤ (p i).eval x))
  let S := signRootNeighborhood p ρ
  have hH : 0 ≤ H := (sum_nonneg (fun a _ => abs_nonneg (rule (fun _ => false) a))).trans
    (hbound _)
  have hpoint (x : ℝ) : ENNReal.ofReal (∑ a,
      |meshAverage (fun y => f y a) ρ x - f x a|) ≤
      ENNReal.ofReal (2 * H) * S.indicator 1 x := by
    by_cases hx : x ∈ S
    · let ν := ProbabilityTheory.cond volume (meshCell ρ x)
      have : IsProbabilityMeasure ν := meshCell_law_isProbabilityMeasure hρ x
      have hint : ∀ a, Integrable (fun y => f y a) ν :=
        integrable_polynomial_sign_rule_component ν p rule H hbound
      simpa only [indicator_of_mem hx, Pi.one_apply, mul_one, meshAverage, abs_sub_comm]
        using ENNReal.ofReal_le_ofReal
          (sum_abs_sub_integral_le ν f hint H (fun _ => hbound _) x)
    · have heq (a : β) : meshAverage (fun y => f y a) ρ x = f x a := by
        apply meshAverage_eq_of_constant _ hρ
        intro y hy
        apply Eq.symm
        apply congrFun (sign_rule_eq_of_not_mem_rootNeighborhood p rule ρ x y hx ?_) a
        rw [abs_of_pos hρ, abs_le]
        have hx' := mem_meshCell hρ x
        constructor <;> linarith [hx'.1, hx'.2, hy.1, hy.2]
      simp only [heq, sub_self, abs_zero, sum_const_zero, ENNReal.ofReal_zero,
        indicator_of_notMem hx, mul_zero, le_refl]
  change (∫⁻ x : ℝ, ENNReal.ofReal (∑ a,
    |meshAverage (fun y => f y a) ρ x - f x a|)) ≤ _
  calc
    _ ≤ ∫⁻ x : ℝ, ENNReal.ofReal (2 * H) * S.indicator 1 x := lintegral_mono hpoint
    _ = ENNReal.ofReal (2 * H) * ∫⁻ x : ℝ, S.indicator 1 x :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (2 * H) * volume S :=
      mul_le_mul_of_nonneg_left (lintegral_indicator_one_le S) zero_le
    _ ≤ ENNReal.ofReal (2 * H) *
        ENNReal.ofReal (2 * (∑ i, ((p i).natDegree : ℝ)) * |ρ|) :=
      mul_le_mul_of_nonneg_left (volume_signRootNeighborhood_le p ρ) zero_le
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * H), abs_of_pos hρ]
      congr 1
      ring

/-- Transverse integration of the actual mesh bound.  Polynomial coefficients
may depend on the hidden variables; the support and degree bounds are uniform. -/
theorem meshAverage_sign_vector_transverse_error
    {Y β : Type*} [MeasurableSpace Y] [Fintype β] {m : ℕ}
    (μ : Measure Y) (E : Set Y) (p : Y → Fin m → Polynomial ℝ)
    (rule : (Fin m → Bool) → β → ℝ) (H D : ℝ)
    (hbound : ∀ s, ∑ a, |rule s a| ≤ H)
    (hdegree : ∀ y ∈ E, ∑ i, ((p y i).natDegree : ℝ) ≤ D)
    (hsupport : ∀ y ∉ E, ∀ t a, rule (fun i => decide (0 ≤ (p y i).eval t)) a = 0)
    {ρ : ℝ} (hρ : 0 < ρ) :
    (∫⁻ y, (∫⁻ t : ℝ, ENNReal.ofReal (∑ a,
      |meshAverage (fun u => rule (fun i => decide (0 ≤ (p y i).eval u)) a) ρ t -
        rule (fun i => decide (0 ≤ (p y i).eval t)) a|)) ∂μ) ≤
      ENNReal.ofReal (4 * H * D * ρ) * μ E := by
  classical
  have hH : 0 ≤ H :=
    (sum_nonneg (fun a _ => abs_nonneg (rule (fun _ => false) a))).trans (hbound _)
  calc
    _ ≤ ∫⁻ y, ENNReal.ofReal (4 * H * D * ρ) * E.indicator 1 y ∂μ := by
      apply lintegral_mono
      intro y
      by_cases hy : y ∈ E
      · simp only [indicator_of_mem hy, Pi.one_apply, mul_one]
        apply (meshAverage_sign_vector_error (p y) rule H hbound hρ).trans
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hdegree y hy) (by positivity)) hρ.le
      · simp only [hsupport y hy, meshAverage, integral_zero, sub_self, abs_zero,
          sum_const_zero, ENNReal.ofReal_zero, lintegral_zero, indicator_of_notMem hy,
          mul_zero, le_refl]
    _ = ENNReal.ofReal (4 * H * D * ρ) * ∫⁻ y, E.indicator 1 y ∂μ :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (4 * H * D * ρ) * μ E :=
      mul_le_mul_of_nonneg_left (lintegral_indicator_one_le E) zero_le

/-- Sum the accepted scalar composition estimate before applying any bounds
on the original coordinate errors. -/
theorem coordinate_averaging_joint_error
    {n : ℕ} {β : Type*} [Fintype β] (M : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (f : β → boundedMeasurableFunctions (Fin (n + 1) → ℝ) M) :
    (∑ a, densityL1Distance volume
      ((List.finRange (n + 1)).foldr (fun i g => coordinateAverage i M hρ g) (f a)).val
      (f a).val) ≤
      ∑ i : Fin (n + 1), ∑ a,
        densityL1Distance volume (coordinateAverage i M hρ (f a)).val (f a).val := by
  have heach (a : β) := coordinate_averaging_error M hρ (List.finRange (n + 1)) (f a)
  have hsum (a : β) :
      ((List.finRange (n + 1)).map (fun i =>
        densityL1Distance volume (coordinateAverage i M hρ (f a)).val (f a).val)).sum =
        ∑ i : Fin (n + 1), densityL1Distance volume
          (coordinateAverage i M hρ (f a)).val (f a).val := by
    rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
  simp only [hsum] at heach
  exact (sum_le_sum (fun a _ => heach a)).trans_eq (sum_comm)

end Submission.Lib.K4MeshListRecovery
