-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Analytic.SmallDilation, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Analytic/SmallDilation.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Analytic/SmallDilation.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Analytic/SmallDilation.lean.
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (including x0491 contributions),
-- branch merged/o143/x0487, commit 36234c3602987ce26ddd4bced782149873fbaa4e.
-- Original file: Submission/Obl/k4_isotropic_discovery_of_local_restoration/SmallDilation.lean
-- Earlier source attributions below are retained.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.ComplexPolynomialBounds

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic

noncomputable section

open MvPolynomial

/-- One exponent, fixed by dimension and degree alone, makes every
coefficient-bounded polynomial vary by at most `A⁻²/8` on the dilated
radius-four complex ball. -/
theorem polynomial_variation_after_small_dilation (n D : ℕ) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ A : ℝ, 2 ≤ A →
      ∀ P : MvPolynomial (Fin n) ℝ, P.totalDegree ≤ D →
      (∀ m, |P.coeff m| ≤ A) →
      ∀ z : EuclideanSpace ℂ (Fin n), ‖z‖ ≤ 4 →
        ‖eval (fun i => (((A ^ M)⁻¹ : ℂ) • z) i) (P.map (algebraMap ℝ ℂ)) -
          eval (fun _ => (0 : ℂ)) (P.map (algebraMap ℝ ℂ))‖ ≤ (A⁻¹) ^ 2 / 8 := by
  let K : ℝ := 4 * (((D + 1 : ℕ) : ℝ) ^ n * (2 : ℝ) ^ D)
  have hKpos : 0 < K := by dsimp [K]; positivity
  obtain ⟨e, he⟩ := pow_unbounded_of_one_lt K (by norm_num : (1 : ℝ) < 2)
  refine ⟨e + 8, by omega, ?_⟩
  intro A hA P hP hcoeff z hz
  have hApos : 0 < A := by linarith
  have hAone : 1 ≤ A := by linarith
  have hKA : K ≤ A ^ e := he.le.trans (pow_le_pow_left₀ (by norm_num) hA _)
  have h32 : (32 : ℝ) ≤ A ^ 5 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hA 5
    norm_num at hh
    exact hh
  have hpower : 32 * K * A ^ 3 ≤ A ^ (e + 8) := by
    calc
      32 * K * A ^ 3 ≤ A ^ 5 * A ^ e * A ^ 3 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul h32 hKA hKpos.le (by positivity)) (by positivity)
      _ = A ^ (e + 8) := by rw [pow_add]; ring
  have hvar : K * A * (4 * (A ^ (e + 8))⁻¹) ≤ (A⁻¹) ^ 2 / 8 := by
    have hh := div_le_div_of_nonneg_right hpower
      (by positivity : (0 : ℝ) ≤ 8 * A ^ 2 * A ^ (e + 8))
    convert hh using 1 <;> field_simp [ne_of_gt hApos] <;> ring
  have hpower4 : (4 : ℝ) ≤ A ^ (e + 8) := by
    calc
      4 ≤ A ^ 2 := by
        have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hA 2
        norm_num at hh
        exact hh
      _ ≤ A ^ (e + 8) := pow_le_pow_right₀ hAone (by omega)
  have hr : (A ^ (e + 8))⁻¹ ≤ (1 / 4 : ℝ) := by
    simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 4) hpower4
  have hnorm : ‖(((A ^ (e + 8))⁻¹ : ℂ) • z)‖ ≤ 4 * (A ^ (e + 8))⁻¹ := by
    rw [norm_smul, norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hApos]
    nlinarith [mul_le_mul_of_nonneg_left hz (by positivity : 0 ≤ (A ^ (e + 8))⁻¹)]
  have hnorm1 : ‖(((A ^ (e + 8))⁻¹ : ℂ) • z)‖ ≤ 1 := hnorm.trans (by linarith)
  calc
    _ ≤ K * A * ‖(((A ^ (e + 8))⁻¹ : ℂ) • z)‖ := by
      simpa [K] using complex_polynomial_lipschitz_on_unit D P hP hApos.le hcoeff
        hnorm1 (show ‖(0 : EuclideanSpace ℂ (Fin n))‖ ≤ 1 by simp)
    _ ≤ K * A * (4 * (A ^ (e + 8))⁻¹) :=
      mul_le_mul_of_nonneg_left hnorm (mul_nonneg hKpos.le hApos.le)
    _ ≤ _ := hvar

/-- Small coefficient-controlled dilations turn central half-margins into
the full complex comparison margins used by stable branch construction. -/
theorem comparison_margins_after_small_dilation (n D : ℕ) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ A : ℝ, 2 ≤ A →
      ∀ B R : MvPolynomial (Fin n) ℝ,
      B.totalDegree ≤ D → R.totalDegree ≤ D →
      (∀ m, |B.coeff m| ≤ A) → (∀ m, |R.coeff m| ≤ A) →
      ∀ β : ℝ, 0 < β → A⁻¹ ≤ β →
      ‖eval (fun _ => (0 : ℂ)) (B.map (algebraMap ℝ ℂ)) - (β : ℂ)‖ ≤ β / 8 →
      ‖eval (fun _ => (0 : ℂ)) (R.map (algebraMap ℝ ℂ)) - (β : ℂ) ^ 2‖ ≤ β ^ 2 / 8 →
      ∀ z : EuclideanSpace ℂ (Fin n), ‖z‖ ≤ 4 →
        ‖eval (fun i => (((A ^ M)⁻¹ : ℂ) • z) i) (B.map (algebraMap ℝ ℂ)) -
          (β : ℂ)‖ ≤ β / 4 ∧
        ‖eval (fun i => (((A ^ M)⁻¹ : ℂ) • z) i) (R.map (algebraMap ℝ ℂ)) -
          (β : ℂ) ^ 2‖ ≤ β ^ 2 / 4 := by
  obtain ⟨M, hM, hvar⟩ := polynomial_variation_after_small_dilation n D
  refine ⟨M, hM, ?_⟩
  intro A hA B R hB hR hBc hRc β hβ hfloor hb0 hr0 z hz
  have hApos : 0 < A := by linarith
  have hAinv0 : 0 ≤ A⁻¹ := inv_nonneg.mpr hApos.le
  have hAinv1 : A⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith : 1 ≤ A)
  have hsmallB : (A⁻¹) ^ 2 ≤ β := by nlinarith
  have hsmallR : (A⁻¹) ^ 2 ≤ β ^ 2 := pow_le_pow_left₀ hAinv0 hfloor 2
  have hvarB := hvar A hA B hB hBc z hz
  have hvarR := hvar A hA R hR hRc z hz
  constructor
  · exact (norm_sub_le_norm_sub_add_norm_sub _
      (eval (fun _ => (0 : ℂ)) (B.map (algebraMap ℝ ℂ))) _).trans (by linarith [hvarB])
  · exact (norm_sub_le_norm_sub_add_norm_sub _
      (eval (fun _ => (0 : ℂ)) (R.map (algebraMap ℝ ℂ))) _).trans (by linarith [hvarR])

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic
