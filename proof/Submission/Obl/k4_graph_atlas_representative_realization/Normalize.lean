import Submission.Obl.k4_stable_native_signal_oscillation.Hidden
import Submission.Obl.k4_quadratic_atlas_normalization.Thickness

namespace Submission.Obl.k4_graph_atlas_representative_realization

open MvPolynomial
open Submission.Obl.k4_quadratic_atlas_normalization
open Submission.Obl.k4_stable_native_signal_oscillation

noncomputable def normalizedTest (P : MvPolynomial (Fin 4) ℝ) (s B d : ℝ) :
    MvPolynomial (Fin 4) ℝ :=
  if |curvature P 3| * d ≤ B * s then C (B / s) * P
  else criticalCenterTest P 3 B

lemma low_step {s B d k h : ℝ} (_hs : 0 < s) (hB : 0 < B)
    (hh : |h| ≤ d / (8 * B)) (hk : |k| * d ≤ B * s) :
    |k| * |h| ≤ s / 8 := by
  have hh' := (le_div_iff₀ (by positivity : 0 < 8 * B)).mp hh
  have hmul := mul_le_mul_of_nonneg_left hh' (abs_nonneg k)
  apply (mul_le_mul_iff_right₀ (by positivity : 0 < 8 * B)).mp
  nlinarith

lemma low_numerics {s B d k q h κ : ℝ} (hs : 0 < s) (hB : 0 < B)
    (hd : 0 < d) (hκ : 8 ≤ κ) (hh : |h| ≤ d / (8 * B))
    (hk : |k| * d ≤ B * s) (hql : s / 2 ≤ |q|) (hqu : |q| ≤ 2 * s) :
    |B / s * (q * h + k * h ^ 2 / 2)| ≤ κ * d ∧
    |B / s * (q + k * h)| ≤ κ * B ∧
    |B / s * k| ≤ κ * B ^ 2 / d ∧
    B / κ ≤ |B / s * (q + k * h)| := by
  have hstep := low_step hs hB hh hk
  have hqlo : s / 4 ≤ |q + k * h| := by
    have ht := abs_sub_abs_le_abs_sub q (q + k * h)
    have he : q - (q + k * h) = -(k * h) := by ring
    rw [he, abs_neg, abs_mul] at ht
    linarith
  have hqhi : |q + k * h| ≤ 3 * s := by
    have ht := abs_add_le q (k * h)
    rw [abs_mul] at ht
    linarith
  have hval : |q * h + k * h ^ 2 / 2| ≤ 3 * s * |h| := by
    calc
      _ ≤ |q * h| + |k * h ^ 2 / 2| := abs_add_le _ _
      _ = |q| * |h| + (|k| * |h|) * |h| / 2 := by
        rw [abs_mul, abs_div, abs_mul, abs_pow,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        ring
      _ ≤ (2 * s) * |h| + (s / 8) * |h| / 2 := by gcongr
      _ ≤ 3 * s * |h| := by nlinarith [abs_nonneg h]
  have hscale : 0 < B / s := div_pos hB hs
  have hsmall := (le_div_iff₀ (by positivity : 0 < 8 * B)).mp hh
  rw [abs_mul, abs_of_pos hscale, abs_mul, abs_of_pos hscale,
    abs_mul, abs_of_pos hscale]
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      _ ≤ B / s * (3 * s * |h|) := mul_le_mul_of_nonneg_left hval hscale.le
      _ = 3 * B * |h| := by field_simp
      _ ≤ κ * d := by nlinarith
  · calc
      _ ≤ B / s * (3 * s) := mul_le_mul_of_nonneg_left hqhi hscale.le
      _ = 3 * B := by field_simp
      _ ≤ κ * B := by nlinarith
  · apply (le_div_iff₀ hd).mpr
    have ht := mul_le_mul_of_nonneg_left hk hscale.le
    have he : B / s * (B * s) = B ^ 2 := by field_simp
    rw [he] at ht
    nlinarith [sq_nonneg B]
  · calc
      _ ≤ B / 4 := div_le_div_of_nonneg_left hB.le (by norm_num) (by linarith)
      _ = B / s * (s / 4) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hqlo hscale.le

lemma high_numerics {s B d k q h κ : ℝ} (hs : 0 < s) (hB : 0 < B)
    (hd : 0 < d) (hκ : 8 ≤ κ) (hh : |h| ≤ d / (8 * B))
    (hk : B * s ≤ |k| * d) (hqu : |q| ≤ 2 * s) :
    |B / k * (q + k * h)| ≤ κ * d := by
  have hkpos : 0 < |k| := by nlinarith [mul_pos hB hs]
  have hkne : k ≠ 0 := abs_pos.mp hkpos
  have hsmall := (le_div_iff₀ (by positivity : 0 < 8 * B)).mp hh
  have hratio : B / |k| * |q| ≤ 2 * d := by
    apply (mul_le_mul_iff_left₀ hkpos).mp
    have he : B / |k| * |q| * |k| = B * |q| := by field_simp
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_left hqu hB.le]
  calc
    _ = |B / k * q + B * h| := by congr 1; field_simp
    _ ≤ |B / k * q| + |B * h| := abs_add_le _ _
    _ = B / |k| * |q| + B * |h| := by
      rw [abs_mul, abs_div, abs_of_pos hB, abs_mul, abs_of_pos hB]
    _ ≤ κ * d := by nlinarith

/-- Normalizing a quadratic or its affine center converts a nearby stable root
into every value and derivative test, without restricting the trajectory set. -/
theorem normalizedTest_bounds (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    {s B d κ : ℝ} (hs : 0 < s) (hB : 0 < B) (hd : 0 < d) (hκ : 8 ≤ κ)
    (z : Fin 4 → ℝ) (w : ℝ) (hw : |z 3 - w| ≤ d / (8 * B))
    (hroot : eval (Function.update z 3 w) P = 0)
    (hlo : s / 2 ≤ |eval (Function.update z 3 w) (pderiv 3 P)|)
    (hhi : |eval (Function.update z 3 w) (pderiv 3 P)| ≤ 2 * s) :
    |eval z (normalizedTest P s B d)| ≤ κ * d ∧
    |eval z (pderiv 3 (normalizedTest P s B d))| ≤ κ * B ∧
    |eval z (pderiv 3 (pderiv 3 (normalizedTest P s B d)))| ≤ κ * B ^ 2 / d ∧
    B / κ ≤ |eval z (pderiv 3 (normalizedTest P s B d))| := by
  have hu : Function.update (Function.update z 3 w) 3
      ((Function.update z 3 w) 3 + (z 3 - w)) = z := by
    simp only [Function.update_self]
    rw [show w + (z 3 - w) = z 3 by ring, Function.update_idem, Function.update_eq_self]
  have ht := quadratic_coordinate_taylor P hP (Function.update z 3 w) 3 (z 3 - w)
  have hv := quadratic_coordinate_derivative P hP (Function.update z 3 w) 3 (z 3 - w)
  rw [hu, hroot, zero_add] at ht
  rw [hu] at hv
  unfold normalizedTest
  split_ifs with hk
  · have hb := low_numerics hs hB hd hκ hw hk hlo hhi
    simpa only [eval_mul, eval_C, pderiv_C_mul, second_pderiv_eq_curvature P hP 3,
      ht, hv] using hb
  · have hkn : curvature P 3 ≠ 0 := by
      have : 0 < |curvature P 3| := by
        have hlt := lt_of_not_ge hk
        nlinarith [mul_pos hB hs]
      exact abs_pos.mp this
    have hval := high_numerics hs hB hd hκ hw (le_of_lt (lt_of_not_ge hk)) hhi
    rw [← hv] at hval
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [criticalCenterTest, eval_mul, eval_C] using hval
    · rw [criticalCenterTest_pderiv P hP 3 B hkn, eval_C, abs_of_pos hB]
      nlinarith
    · rw [criticalCenterTest_second_pderiv P hP 3 B hkn, map_zero, abs_zero]
      positivity
    · rw [criticalCenterTest_pderiv P hP 3 B hkn, eval_C, abs_of_pos hB]
      exact div_le_self hB.le (by linarith)

theorem normalizedTest_degree (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (s B d : ℝ) : (normalizedTest P s B d).totalDegree ≤ 2 := by
  classical
  unfold normalizedTest
  split_ifs
  · exact (totalDegree_mul _ _).trans (by simpa using hP)
  · exact (criticalCenterTest_totalDegree P hP 3 B).trans (by norm_num)

theorem normalizedTest_coeff (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    {s B d V : ℝ} (hs : 0 < s) (hB : 0 < B) (hd : d ≤ 1) (hV : 1 ≤ V)
    (hBV : B ≤ V) (hsV : s⁻¹ ≤ V) (hcoeff : ∀ e, |P.coeff e| ≤ V)
    (e : Fin 4 →₀ ℕ) : |(normalizedTest P s B d).coeff e| ≤ 2 * V ^ 3 := by
  have hV0 : 0 ≤ V := by linarith
  unfold normalizedTest
  split_ifs with hk
  · rw [coeff_C_mul, abs_mul, abs_of_pos (div_pos hB hs), div_eq_mul_inv]
    calc
      _ ≤ V * V * V := by gcongr; exact hcoeff e
      _ ≤ 2 * V ^ 3 := by nlinarith [pow_nonneg hV0 3]
  · have hkpos : 0 < |curvature P 3| := by
      have hlt := lt_of_not_ge hk
      have hm := mul_le_mul_of_nonneg_left hd (abs_nonneg (curvature P 3))
      nlinarith [mul_pos hB hs]
    have hratio : B / |curvature P 3| ≤ s⁻¹ := by
      rw [← one_div, div_le_div_iff₀ hkpos hs]
      have hm := mul_le_mul_of_nonneg_left hd (abs_nonneg (curvature P 3))
      nlinarith [lt_of_not_ge hk]
    rw [criticalCenterTest, coeff_C_mul, abs_mul, abs_div, abs_of_pos hB]
    calc
      _ ≤ s⁻¹ * (2 * V) := mul_le_mul hratio
        (quadratic_pderiv_coeff_bound P hP 3 hV0 hcoeff e) (abs_nonneg _) (by positivity)
      _ ≤ V * (2 * V) := mul_le_mul_of_nonneg_right hsV (by positivity)
      _ ≤ 2 * V ^ 3 := by nlinarith [mul_le_mul_of_nonneg_left hV (sq_nonneg V)]

end Submission.Obl.k4_graph_atlas_representative_realization
