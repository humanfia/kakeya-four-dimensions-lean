-- Adapted from this LOT tree o064, session x0447, commit e825efe6,
-- Submission/Obl/k4_terminal_charts_from_scalar_mesh_row_fit/OriginalPolynomialBounds.lean.

import Submission.Lib.K4PolynomialRemezThree.SmallBall
import Submission.Obl.k4_stable_native_signal_oscillation.BasePolynomials

/-! Coefficient bounds directly from an original observable law. The canonical
polynomial sublevel set replaces the possibly nonmeasurable projection image. -/

namespace Submission.Obl.k4_clean_cover_graph_atlas

open MeasureTheory Set MvPolynomial
open scoped ENNReal

/-- A fixed-degree polynomial bounded on positive original mass has bounded
coefficients. Only the original base ceiling and its original mass are used. -/
theorem exists_original_law_polynomial_coefficient_bound (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : MvPolynomial (Fin 3) ℝ), P.totalDegree ≤ D →
      ∀ (X : Type*) [MeasurableSpace X] (μ : Measure X)
        (base : X → EuclideanSpace ℝ (Fin 3)) (H q V : ℝ),
        Measurable base → 0 < H → 0 < q → q ≤ 1 → 0 ≤ V →
        μ.map base ≤ ENNReal.ofReal H • volume →
        ENNReal.ofReal (H * q) ≤ μ univ →
        (∀ᵐ x ∂μ, ‖base x‖ ≤ 1 / 8 ∧ |eval (fun i => base x i) P| ≤ V) →
        ∀ d, |P.coeff d| ≤ C * (32 * ((D : ℝ) + 1) / q) ^ (3 * D) * V := by
  obtain ⟨C, hC, hsublevel⟩ :=
    Submission.Lib.K4PolynomialRemezThree.exists_coefficient_sublevel_bound_on_small_ball D
  refine ⟨C, hC, ?_⟩
  intro P hP X inst μ base H q V hb hH hq hqone hV hcap hmass hpoint d
  by_contra hbound
  have hlarge : C * (32 * ((D : ℝ) + 1) / q) ^ (3 * D) * V < |P.coeff d| :=
    lt_of_not_ge hbound
  have hcoeffpos : 0 < |P.coeff d| := lt_of_le_of_lt (by positivity) hlarge
  let S : Set (EuclideanSpace ℝ (Fin 3)) :=
    {x | ‖x‖ ≤ 1 / 8 ∧ |eval (fun i => x i) P| ≤
      (|P.coeff d| / C) * (q / (32 * (D + 1))) ^ (3 * D)}
  have hS : MeasurableSet S := by
    have heval : Continuous (fun x : EuclideanSpace ℝ (Fin 3) =>
        eval (fun i => x i) P) := P.continuous_eval.comp (by fun_prop)
    exact (measurableSet_le continuous_norm.measurable measurable_const).inter
      (measurableSet_le heval.measurable.abs measurable_const)
  have hcancel :
      (32 * ((D : ℝ) + 1) / q) ^ (3 * D) *
        (q / (32 * ((D : ℝ) + 1))) ^ (3 * D) = 1 := by
    rw [← mul_pow]
    have : (32 * ((D : ℝ) + 1) / q) * (q / (32 * ((D : ℝ) + 1))) = 1 := by
      field_simp
    rw [this, one_pow]
  have hthreshold : V ≤
      (|P.coeff d| / C) * (q / (32 * ((D : ℝ) + 1))) ^ (3 * D) := by
    have hh := mul_le_mul_of_nonneg_right hlarge.le
      (show 0 ≤ (q / (32 * ((D : ℝ) + 1))) ^ (3 * D) by positivity)
    have heq : C * (32 * ((D : ℝ) + 1) / q) ^ (3 * D) * V *
        (q / (32 * ((D : ℝ) + 1))) ^ (3 * D) = C * V := by
      calc
        _ = C * V * ((32 * ((D : ℝ) + 1) / q) ^ (3 * D) *
          (q / (32 * ((D : ℝ) + 1))) ^ (3 * D)) := by ring
        _ = _ := by rw [hcancel, mul_one]
    rw [heq] at hh
    calc
      V = (C * V) / C := by field_simp
      _ ≤ (|P.coeff d| * (q / (32 * ((D : ℝ) + 1))) ^ (3 * D)) / C :=
        div_le_div_of_nonneg_right hh hC.le
      _ = _ := by ring
  have hsupport : ∀ᵐ x ∂μ, base x ∈ S := by
    filter_upwards [hpoint] with x hx
    exact ⟨hx.1, hx.2.trans hthreshold⟩
  have htotal : μ univ = μ (base ⁻¹' S) := by
    have hz : μ (base ⁻¹' S)ᶜ = 0 := ae_iff.mp hsupport
    rw [← measure_add_measure_compl (hb hS), hz, add_zero]
  have hmassS : ENNReal.ofReal (H * q) ≤ ENNReal.ofReal H * volume S := by
    calc
      _ ≤ μ univ := hmass
      _ = (μ.map base) S := by rw [Measure.map_apply hb hS, htotal]
      _ ≤ _ := by
        simpa only [Measure.smul_apply, smul_eq_mul] using (Measure.le_iff'.mp hcap S)
  have hsmall : volume S < ENNReal.ofReal q :=
    hsublevel P hP |P.coeff d| q hcoeffpos hq hqone ⟨d, le_rfl⟩
  have hstrict : ENNReal.ofReal H * volume S < ENNReal.ofReal (H * q) := by
    rw [ENNReal.ofReal_mul hH.le]
    exact ENNReal.mul_lt_mul_right (ne_of_gt (ENNReal.ofReal_pos.mpr hH))
      ENNReal.ofReal_ne_top hsmall
  exact (not_lt_of_ge hmassS) hstrict

/-- The discriminant coefficient bound used before short-block subdivision.
The input mass is that of the original matched candidate, so there is no new
mass floor on each comparison subbox. -/
theorem exists_original_law_discriminant_coefficient_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : MvPolynomial (Fin 4) ℝ), P.totalDegree ≤ 2 →
      ∀ (X : Type*) [MeasurableSpace X] (μ : Measure X)
        (base : X → EuclideanSpace ℝ (Fin 3)) (hidden : X → ℝ)
        (H q K a : ℝ),
        Measurable base → 0 < H → 0 < q → q ≤ 1 → 2 ≤ K → 0 < a →
        μ.map base ≤ ENNReal.ofReal H • volume →
        ENNReal.ofReal (H * q) ≤ μ univ →
        |Submission.Obl.k4_quadratic_atlas_normalization.curvature P (Fin.last 3)| ≤ K / a →
        (∀ᵐ x ∂μ, ‖base x‖ ≤ 1 / 8 ∧
          |eval (Fin.snoc (fun i => base x i) (hidden x)) P| ≤ K * a ∧
          |eval (Fin.snoc (fun i => base x i) (hidden x)) (pderiv (Fin.last 3) P)| ≤ K) →
        ∀ d, |(Submission.Obl.k4_stable_native_signal_oscillation.baseDiscriminant P).coeff d| ≤
          C * (96 / q) ^ 6 * K ^ 4 := by
  obtain ⟨C, hC, hbound⟩ := exists_original_law_polynomial_coefficient_bound 2
  refine ⟨C, hC, ?_⟩
  intro P hP X inst μ base hidden H q K a hb hH hq hqone hK ha hcap hmass hcurv hpoint d
  have hpoly := Submission.Obl.k4_stable_native_signal_oscillation.baseDiscriminant_degree P hP
  have hpointD : ∀ᵐ x ∂μ, ‖base x‖ ≤ 1 / 8 ∧
      |eval (fun i => base x i)
        (Submission.Obl.k4_stable_native_signal_oscillation.baseDiscriminant P)| ≤ K ^ 4 := by
    filter_upwards [hpoint] with x hx
    refine ⟨hx.1, ?_⟩
    rw [Submission.Obl.k4_stable_native_signal_oscillation.eval_baseDiscriminant
      P hP (fun i => base x i) (hidden x)]
    exact Submission.Obl.k4_stable_native_signal_oscillation.discriminant_bound
      P _ _ hK ha hcurv hx.2.1 hx.2.2
  have hh := hbound _ hpoly X μ base H q (K ^ 4) hb hH hq hqone (by positivity)
    hcap hmass hpointD d
  norm_num at hh ⊢
  exact hh

end Submission.Obl.k4_clean_cover_graph_atlas
