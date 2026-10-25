-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Analytic/BoxDilation.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Analytic/BoxDilation.lean.
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (including x0491 contributions),
-- branch merged/o143/x0487, commit 36234c3602987ce26ddd4bced782149873fbaa4e.
-- Original file: Submission/Obl/k4_isotropic_discovery_of_local_restoration/BoxDilation.lean
-- Earlier source attributions below are retained.
import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.DilatedBranch

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open MvPolynomial

/-- A central polynomial lower bound yields positivity throughout the
complex coordinate box after one uniformly chosen power dilation. -/
theorem positive_polynomial_on_box_after_uniform_dilation (D : ℕ) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ A : ℝ, 2 ≤ A →
      ∀ P : MvPolynomial (Fin 3) ℝ, P.totalDegree ≤ D →
      (∀ m, |P.coeff m| ≤ A) → (A⁻¹) ^ 2 ≤ eval (fun _ => (0 : ℝ)) P →
      ∀ y : Fin 3 → ℂ, (∀ i, ‖y i‖ < 4) →
        0 < (eval₂ (algebraMap ℝ ℂ) y (baseDilation (A ^ M)⁻¹ P)).re := by
  obtain ⟨M, hM, hvar⟩ := polynomial_variation_after_small_dilation 3 D
  refine ⟨M + 1, by omega, ?_⟩
  intro A hA P hP hcoeff hcenter y hy
  have hApos : 0 < A := by linarith
  let z : EuclideanSpace ℂ (Fin 3) := WithLp.toLp 2 y
  have hnorm8 : ‖z‖ ≤ 8 := by
    apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)).mp
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin 3, (16 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have hh := pow_le_pow_left₀ (norm_nonneg (y i)) (hy i).le 2
        norm_num at hh
        exact hh
      _ ≤ (8 : ℝ) ^ 2 := by norm_num
  let z' : EuclideanSpace ℂ (Fin 3) := (A : ℂ)⁻¹ • z
  have hnorm4 : ‖z'‖ ≤ 4 := by
    dsimp [z']
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hApos]
    have hi : A⁻¹ ≤ (1 / 2 : ℝ) := by
      simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 2) hA
    nlinarith [mul_le_mul hi hnorm8 (norm_nonneg z) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hv := hvar A hA P hP hcoeff z' hnorm4
  have hpoint : ((A : ℂ) ^ M)⁻¹ • z' = ((A : ℂ) ^ (M + 1))⁻¹ • z := by
    dsimp [z']
    rw [smul_smul, pow_succ, mul_inv_rev]
    congr 1
    ring
  have hval : eval₂ (algebraMap ℝ ℂ) y (baseDilation (A ^ (M + 1))⁻¹ P) =
      eval (fun i => (((A : ℂ) ^ (M + 1))⁻¹ • z) i) (P.map (algebraMap ℝ ℂ)) := by
    change eval₂ (algebraMap ℝ ℂ) (fun i => z i) _ = _
    rw [eval₂_eq_eval_map, eval_complex_baseDilation]
    simp only [Complex.ofReal_inv, Complex.ofReal_pow, PiLp.smul_apply, smul_eq_mul]
  have hzero : eval (fun _ => (0 : ℂ)) (P.map (algebraMap ℝ ℂ)) =
      (eval (fun _ => (0 : ℝ)) P : ℂ) :=
    Submission.Lib.K4QuadraticSheetsReal.eval_map_real P (fun _ => 0)
  rw [hpoint, ← hval, hzero] at hv
  have hre : |(eval₂ (algebraMap ℝ ℂ) y (baseDilation (A ^ (M + 1))⁻¹ P)).re -
      eval (fun _ => (0 : ℝ)) P| ≤ (A⁻¹) ^ 2 / 8 := by
    simpa only [Complex.sub_re, Complex.ofReal_re] using
      (Complex.abs_re_le_norm (eval₂ (algebraMap ℝ ℂ) y
        (baseDilation (A ^ (M + 1))⁻¹ P) - (eval (fun _ => (0 : ℝ)) P : ℂ))).trans hv
  have hapos : 0 < (A⁻¹) ^ 2 := pow_pos (inv_pos.mpr hApos) 2
  linarith [(abs_le.mp hre).1]

/-- Uniform discriminant positivity in the exact coordinate-box form used
by the accepted sign-selected native sheet constructor. -/
theorem native_discriminant_on_box_after_uniform_dilation (d : ℕ) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ A : ℝ, 2 ≤ A →
      ∀ (B C₀ : MvPolynomial (Fin 3) ℝ) (a : ℝ),
      B.totalDegree ≤ d → C₀.totalDegree ≤ d →
      (∀ m, |(nativeBaseDiscriminant a B C₀).coeff m| ≤ A) →
      (A⁻¹) ^ 2 ≤ eval (fun _ => (0 : ℝ)) (nativeBaseDiscriminant a B C₀) →
      ∀ y : Fin 3 → ℂ, (∀ i, ‖y i‖ < 4) →
        0 < (eval₂ (algebraMap ℝ ℂ) y
          (baseDilation (A ^ M)⁻¹ B * baseDilation (A ^ M)⁻¹ B -
            C (4 * a) * baseDilation (A ^ M)⁻¹ C₀)).re := by
  obtain ⟨M, hM, hpositive⟩ := positive_polynomial_on_box_after_uniform_dilation (2 * d)
  refine ⟨M, hM, ?_⟩
  intro A hA B C₀ a hB hC hcoeff hcenter y hy
  have hh := hpositive A hA (nativeBaseDiscriminant a B C₀)
    (nativeBaseDiscriminant_totalDegree d a B C₀ hB hC) hcoeff hcenter y hy
  rw [baseDilation_nativeBaseDiscriminant] at hh
  simpa only [nativeBaseDiscriminant, pow_two] using hh

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
