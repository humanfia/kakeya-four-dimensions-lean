-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Restoration/Analytic/WitnessComparison.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o267, branch x0945, commit 7135e2fbe574;
-- source Submission/Obl/k4_original_potential_reference_completion/Analytic/WitnessComparison.lean (session x0945).
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (with x0491's contributions), branch x0487,
-- commit 36234c36, file Submission/Obl/k4_isotropic_discovery_of_local_restoration/WitnessComparison.lean
-- (namespace renamed; the attributions that file carries are kept below).
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.Analytic.QuadraticFitNorming
import Submission.Obl.k4_seven_direction_local_degree_restoration.Hidden

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open MvPolynomial

/-- The accepted affine-substitution degree bound and quadratic coefficient
lemma give the actual time fit, in arbitrary coordinate dimension. -/
theorem quadratic_eval_affine_fit {σ : Type*} (P : MvPolynomial σ ℝ)
    (hP : P.totalDegree ≤ 2) (u v : σ → ℝ) :
    ∃ α β γ : ℝ, ∀ t : ℝ,
      eval (fun i => u i + t * v i) P = α + β * t + γ * t ^ 2 := by
  let Q : σ → Polynomial ℝ := fun i => Polynomial.C (u i) + Polynomial.C (v i) * Polynomial.X
  let R : Polynomial ℝ := MvPolynomial.eval₂ Polynomial.C Q P
  have hQ : ∀ i, (Q i).natDegree ≤ 1 := by
    intro i
    exact (Polynomial.natDegree_add_le _ _).trans (max_le (by simp)
      ((Polynomial.natDegree_C_mul_le _ _).trans (by simp)))
  have hR : R.natDegree ≤ 2 :=
    (Submission.Obl.k4_quadratic_slope_volume.natDegree_eval₂_affine_le P Q hQ).trans hP
  obtain ⟨γ, β, α, hcoeff⟩ := Submission.Lib.K4QuadraticSublevel.quadratic_eq_coefficients R hR
  refine ⟨α, β, γ, ?_⟩
  intro t
  calc
    _ = R.eval t := by
      simpa only [R, Q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, mul_comm] using
        (Submission.Obl.k4_quadratic_slope_volume.eval_polynomial_substitution P Q t).symm
    _ = _ := by rw [hcoeff]; simp; ring

/-- A narrow branch tube gives a small normalized old-test error. The
Taylor estimate itself is the accepted local-restoration hidden lemma. -/
theorem quadratic_residual_hidden_shift_bound
    (S : Poly) (hS : S.totalDegree ≤ 2) (u : Base) (f w : ℝ)
    {A a b : ℝ} (hA : 2 ≤ A) (ha : 0 < a) (hb : 0 ≤ b) (hba : b ≤ a)
    (hdist : |w - f| ≤ A * b)
    (hfirst : |eval ![u 0, u 1, u 2, w] (pderiv 3 S)| ≤ A)
    (hsecond : |eval ![u 0, u 1, u 2, w] (pderiv 3 (pderiv 3 S))| ≤ A / a) :
    |eval ![u 0, u 1, u 2, f] S / a - eval ![u 0, u 1, u 2, w] S / a| ≤
      A ^ 4 * b / a := by
  have hdiff : |eval ![u 0, u 1, u 2, f] S - eval ![u 0, u 1, u 2, w] S| ≤
      A * (A * b) + (A / a) * (A * b) ^ 2 / 2 := by
    simpa only [Submission.Obl.k4_seven_direction_local_degree_restoration.evalAt,
      abs_sub_comm] using
      Submission.Obl.k4_seven_direction_local_degree_restoration.abs_hidden_quadratic_sub_le
        S hS u hdist hfirst hsecond
  have hratio0 : 0 ≤ b / a := div_nonneg hb ha.le
  have hratio1 : b / a ≤ 1 := (div_le_one ha).mpr hba
  have hsquare : (b / a) ^ 2 ≤ b / a := by
    nlinarith [mul_nonneg hratio0 (sub_nonneg.mpr hratio1)]
  have hA0 : 0 ≤ A := by linarith
  have hdouble : 2 * A ^ 2 ≤ A ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_right hA (sq_nonneg A)]
  have hpower : A ^ 2 + A ^ 3 / 2 ≤ A ^ 4 := by
    calc
      _ ≤ A ^ 3 := by linarith
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by norm_num)
  calc
    _ = |eval ![u 0, u 1, u 2, f] S - eval ![u 0, u 1, u 2, w] S| / a := by
      rw [← sub_div, abs_div, abs_of_pos ha]
    _ ≤ (A * (A * b) + (A / a) * (A * b) ^ 2 / 2) / a :=
      div_le_div_of_nonneg_right hdiff ha.le
    _ = A ^ 2 * (b / a) + (A ^ 3 / 2) * (b / a) ^ 2 := by field_simp
    _ ≤ A ^ 2 * (b / a) + (A ^ 3 / 2) * (b / a) := by gcongr
    _ = (A ^ 2 + A ^ 3 / 2) * (b / a) := by ring
    _ ≤ A ^ 4 * (b / a) := mul_le_mul_of_nonneg_right hpower hratio0
    _ = _ := by ring

/-- The old quadratic restricted to an actual affine hidden trajectory
supplies the quadratic fit needed by third-jet norming. -/
theorem exists_quadratic_residual_line_fit
    (S : Poly) (hS : S.totalDegree ≤ 2) (f : Base → ℝ)
    (u v : Base) (w₀ w₁ : ℝ) (E : Set ℝ)
    {A a b : ℝ} (hA : 2 ≤ A) (ha : 0 < a) (hb : 0 ≤ b) (hba : b ≤ a)
    (hdist : ∀ t ∈ E, |w₀ + w₁ * t - f (u + t • v)| ≤ A * b)
    (hfirst : ∀ t ∈ E,
      |eval ![(u + t • v) 0, (u + t • v) 1, (u + t • v) 2, w₀ + w₁ * t]
        (pderiv 3 S)| ≤ A)
    (hsecond : ∀ t ∈ E,
      |eval ![(u + t • v) 0, (u + t • v) 1, (u + t • v) 2, w₀ + w₁ * t]
        (pderiv 3 (pderiv 3 S))| ≤ A / a) :
    ∃ α β γ : ℝ, ∀ t ∈ E,
      |eval ![(u + t • v) 0, (u + t • v) 1, (u + t • v) 2, f (u + t • v)] S / a -
        (α + β * t + γ * t ^ 2)| ≤ A ^ 4 * b / a := by
  obtain ⟨α, β, γ, hfit⟩ := quadratic_eval_affine_fit S hS
    ![u 0, u 1, u 2, w₀] ![v 0, v 1, v 2, w₁]
  have hfit' : ∀ t : ℝ,
      eval ![(u + t • v) 0, (u + t • v) 1, (u + t • v) 2, w₀ + w₁ * t] S =
        α + β * t + γ * t ^ 2 := by
    intro t
    have heq : (fun i : Fin 4 => ![u 0, u 1, u 2, w₀] i + t * ![v 0, v 1, v 2, w₁] i) =
        ![(u + t • v) 0, (u + t • v) 1, (u + t • v) 2, w₀ + w₁ * t] := by
      funext i
      fin_cases i <;> simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mul_comm]
    simpa only [heq] using hfit t
  refine ⟨α / a, β / a, γ / a, ?_⟩
  intro t ht
  have hh := quadratic_residual_hidden_shift_bound S hS (u + t • v) (f (u + t • v))
    (w₀ + w₁ * t) hA ha hb hba (hdist t ht) (hfirst t ht) (hsecond t ht)
  rw [hfit' t] at hh
  have heq : (α + β * t + γ * t ^ 2) / a = α / a + β / a * t + γ / a * t ^ 2 := by ring
  rw [heq] at hh
  exact hh

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
