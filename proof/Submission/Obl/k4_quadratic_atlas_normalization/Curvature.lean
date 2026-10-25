import Submission.Obl.k4_quadratic_slope_volume.PolynomialSlices

-- Adapted from this LOT tree, o104, session x0350, commit 0e2b59568680,
-- Submission/Obl/k4_terminal_time_extension/Curvature.lean.

/-!
The late curvature dichotomy in the supplied paper's Lemma 3.5.
A high-curvature quadratic is replaced directly by its normalized derivative;
this is the affine critical-center equation, with no root choice required.
-/

namespace Submission.Obl.k4_quadratic_atlas_normalization

open MvPolynomial

variable {σ : Type*}

/-- The constant second derivative in the hidden coordinate. -/
noncomputable def curvature (P : MvPolynomial σ ℝ) (i : σ) : ℝ :=
  (pderiv i (pderiv i P)).coeff 0

theorem second_pderiv_eq_curvature (P : MvPolynomial σ ℝ)
    (hP : P.totalDegree ≤ 2) (i : σ) :
    pderiv i (pderiv i P) = C (curvature P i) := by
  classical
  have h₁ := Submission.Obl.k4_quadratic_slope_volume.totalDegree_pderiv_le P i
  have h₂ := Submission.Obl.k4_quadratic_slope_volume.totalDegree_pderiv_le (pderiv i P) i
  have hd : (pderiv i (pderiv i P)).totalDegree = 0 := by omega
  exact totalDegree_eq_zero_iff_eq_C.mp hd

/-- The quadratic discriminant, written in the original variables. -/
noncomputable def discriminant (P : MvPolynomial σ ℝ) (i : σ) : MvPolynomial σ ℝ :=
  (pderiv i P) ^ 2 - C (2 * curvature P i) * P

theorem discriminant_eval (P : MvPolynomial σ ℝ) (i : σ) (z : σ → ℝ) :
    eval z (discriminant P i) =
      (eval z (pderiv i P)) ^ 2 - 2 * curvature P i * eval z P := by
  simp [discriminant]

/-- The discriminant does not vary in the hidden coordinate. -/
theorem discriminant_pderiv (P : MvPolynomial σ ℝ)
    (hP : P.totalDegree ≤ 2) (i : σ) : pderiv i (discriminant P i) = 0 := by
  simp only [discriminant, map_sub, pow_two, pderiv_mul, pderiv_C, zero_mul, zero_add,
    second_pderiv_eq_curvature P hP i]
  rw [map_mul, map_ofNat]
  ring

theorem discriminant_totalDegree (P : MvPolynomial σ ℝ)
    (hP : P.totalDegree ≤ 2) (i : σ) : (discriminant P i).totalDegree ≤ 2 := by
  classical
  have hder := Submission.Obl.k4_quadratic_slope_volume.totalDegree_pderiv_le P i
  unfold discriminant
  apply (totalDegree_sub _ _).trans
  apply max_le
  · exact (totalDegree_pow _ _).trans (by omega)
  · apply (totalDegree_mul _ _).trans
    simpa only [totalDegree_C, zero_add] using hP

/-- The hidden coordinate may be changed freely when evaluating the discriminant. -/
theorem discriminant_update [DecidableEq σ] (P : MvPolynomial σ ℝ)
    (hP : P.totalDegree ≤ 2) (i : σ) (z : σ → ℝ) (w : ℝ) :
    eval (Function.update z i w) (discriminant P i) = eval z (discriminant P i) := by
  classical
  let q := Submission.Obl.k4_quadratic_slope_volume.coordinatePolynomialHom z i (discriminant P i)
  have hd : q.derivative = 0 := by
    change (Submission.Obl.k4_quadratic_slope_volume.coordinatePolynomialHom z i
      (discriminant P i)).derivative = 0
    rw [Submission.Obl.k4_quadratic_slope_volume.derivative_coordinatePolynomialHom,
      discriminant_pderiv P hP i, map_zero]
  have hq := Polynomial.eq_C_of_derivative_eq_zero hd
  rw [← Submission.Obl.k4_quadratic_slope_volume.eval_coordinatePolynomialHom]
  change q.eval w = _
  have heval := Submission.Obl.k4_quadratic_slope_volume.eval_coordinatePolynomialHom
    (discriminant P i) z i (z i)
  rw [Function.update_eq_self] at heval
  rw [← heval]
  change q.eval w = q.eval (z i)
  rw [hq]
  simp

/-- Derivative coefficients of a quadratic cost only a factor of two. -/
theorem quadratic_pderiv_coeff_bound (P : MvPolynomial σ ℝ)
    (hP : P.totalDegree ≤ 2) (i : σ) {V : ℝ}
    (hV : 0 ≤ V) (hcoeff : ∀ e, |P.coeff e| ≤ V) (e : σ →₀ ℕ) :
    |(pderiv i P).coeff e| ≤ 2 * V := by
  classical
  rw [coeff_pderiv]
  by_cases he : P.coeff (e + Finsupp.single i 1) = 0
  · simp [he, mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hV]
  have hs := mem_support_iff.mpr he
  have hdeg := ((monomial_le_degreeOf i hs).trans (degreeOf_le_totalDegree P i)).trans hP
  have hei : (e i : ℝ) + 1 ≤ 2 := by
    have hh : e i + 1 ≤ 2 := by simpa using hdeg
    exact_mod_cast hh
  rw [abs_mul, abs_of_nonneg (show 0 ≤ (e i : ℝ) + 1 by positivity)]
  calc
    _ ≤ V * 2 := mul_le_mul (hcoeff _) hei (by positivity) hV
    _ = 2 * V := mul_comm _ _

/-- The affine equation `w - F_ctr`, in the requested hidden derivative unit `B`. -/
noncomputable def criticalCenterTest (P : MvPolynomial σ ℝ) (i : σ) (B : ℝ) :
    MvPolynomial σ ℝ :=
  C (B / curvature P i) * pderiv i P

theorem criticalCenterTest_totalDegree (P : MvPolynomial σ ℝ)
    (hP : P.totalDegree ≤ 2) (i : σ) (B : ℝ) :
    (criticalCenterTest P i B).totalDegree ≤ 1 := by
  classical
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  exact (Submission.Obl.k4_quadratic_slope_volume.totalDegree_pderiv_le P i).trans (by omega)

theorem criticalCenterTest_pderiv (P : MvPolynomial σ ℝ)
    (hP : P.totalDegree ≤ 2) (i : σ) (B : ℝ) (hc : curvature P i ≠ 0) :
    pderiv i (criticalCenterTest P i B) = C B := by
  rw [criticalCenterTest, pderiv_C_mul, second_pderiv_eq_curvature P hP i,
    ← map_mul, div_mul_cancel₀ B hc]

theorem criticalCenterTest_second_pderiv (P : MvPolynomial σ ℝ)
    (hP : P.totalDegree ≤ 2) (i : σ) (B : ℝ) (hc : curvature P i ≠ 0) :
    pderiv i (pderiv i (criticalCenterTest P i B)) = 0 := by
  rw [criticalCenterTest_pderiv P hP i B hc, pderiv_C]

/-- The high-curvature center estimate uses only the old derivative upper bound. -/
theorem criticalCenterTest_eval_bound (P : MvPolynomial σ ℝ) (i : σ)
    {B a U : ℝ} (hB : 0 ≤ B) (ha : 0 < a) (hc : a ≤ |curvature P i|)
    (z : σ → ℝ) (hU : |eval z (pderiv i P)| ≤ U) :
    |eval z (criticalCenterTest P i B)| ≤ B * U / a := by
  rw [criticalCenterTest, eval_mul, eval_C, abs_mul, abs_div, abs_of_nonneg hB]
  calc
    B / |curvature P i| * |eval z (pderiv i P)| =
        B * |eval z (pderiv i P)| / |curvature P i| := by ring
    _ ≤ B * U / a := by
      exact div_le_div₀ (mul_nonneg hB ((abs_nonneg _).trans hU))
        (mul_le_mul_of_nonneg_left hU hB) ha hc

/-- Polynomial coefficient control survives the high-curvature replacement. -/
theorem criticalCenterTest_coeff_bound (P : MvPolynomial σ ℝ)
    (hP : P.totalDegree ≤ 2) (i : σ) {B a V : ℝ}
    (hB : 0 ≤ B) (ha : 0 < a) (hc : a ≤ |curvature P i|)
    (hV : 0 ≤ V) (hcoeff : ∀ e, |P.coeff e| ≤ V) (e : σ →₀ ℕ) :
    |(criticalCenterTest P i B).coeff e| ≤ 2 * B * V / a := by
  classical
  rw [criticalCenterTest, coeff_C_mul, abs_mul, abs_div, abs_of_nonneg hB]
  calc
    _ ≤ (B / |curvature P i|) * (2 * V) :=
      mul_le_mul_of_nonneg_left (quadratic_pderiv_coeff_bound P hP i hV hcoeff e)
        (by positivity)
    _ = (2 * B * V) / |curvature P i| := by ring
    _ ≤ 2 * B * V / a := div_le_div_of_nonneg_left (by positivity) ha hc

/-- A discriminant bounded away from zero and a small curvature-value error force
a real, positive discriminant and a derivative lower bound at the source. -/
theorem low_curvature_derivative_floor {p q c σ₀ : ℝ}
    (hσ : 0 < σ₀) (hdisc : σ₀ ≤ |q ^ 2 - 2 * c * p|)
    (hsmall : 2 * |c * p| ≤ σ₀ / 2) :
    0 < q ^ 2 - 2 * c * p ∧ σ₀ / 2 ≤ q ^ 2 := by
  have habs := abs_le.mp (le_refl |c * p|)
  have hd : 0 < q ^ 2 - 2 * c * p := by
    by_contra! hn
    rw [abs_of_nonpos hn] at hdisc
    nlinarith [sq_nonneg q]
  rw [abs_of_pos hd] at hdisc
  exact ⟨hd, by nlinarith⟩

end Submission.Obl.k4_quadratic_atlas_normalization
