-- Adapted from this LOT tree, obligation o254, branch x0898, commit f25a0cc9, file Submission/Obl/k4_general_parent_wide_layer_candidates/Native/ProjectedPolynomialNorm.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
/- Adapted from this LOT tree, obligation o200, session x0934, commit 3ef9d3b45123d3245f500a2dc2bd85270a8fff3d,
   Submission/Obl/k4_finite_projected_horizontal_candidates/ProjectedPolynomialNorm.lean. Original source attributions are retained below. -/
import Mathlib
import Submission.Lib.K4PolynomialRemezThree.PolynomialNorm
import Submission.Lib.K4ScalarSwitching.PolynomialDegree

/-! Projected quadratic norms come from the full-time strip normalization. -/

namespace Submission.Obl.k4_general_wide_layer_offset_comparison.Native.CommonDomain

open MvPolynomial Set
open Submission.Lib.K4ScalarSwitching.PolynomialDegree

noncomputable section

def stripSub (u v β : ℝ) : Fin 2 → MvPolynomial (Fin 2) ℝ :=
  ![X 0, C u + C v * X 0 + C β * (C 2 * X 1 - 1)]

def stripNormalized (G : MvPolynomial (Fin 2) ℝ) (u v β : ℝ) : MvPolynomial (Fin 2) ℝ :=
  aeval (stripSub u v β) G

theorem stripSub_degree (u v β : ℝ) (i : Fin 2) : (stripSub u v β i).totalDegree ≤ 1 := by
  fin_cases i
  · simp [stripSub]
  · change (C u + C v * X (0 : Fin 2) + C β * (C 2 * X 1 - 1)).totalDegree ≤ 1
    apply degree_add_le
    · exact degree_add_le (by simp) ((degree_C_mul_le _ _).trans (by simp))
    · apply (degree_C_mul_le _ _).trans
      exact degree_sub_le ((degree_C_mul_le _ _).trans (by simp)) (by simp)

theorem stripNormalized_degree (G : MvPolynomial (Fin 2) ℝ) (u v β : ℝ) :
    (stripNormalized G u v β).totalDegree ≤ G.totalDegree :=
  degree_aeval_le G _ (stripSub_degree u v β)

theorem stripNormalized_eval (G : MvPolynomial (Fin 2) ℝ) (u v β : ℝ) (x : Fin 2 → ℝ) :
    eval x (stripNormalized G u v β) = eval ![x 0, u + v * x 0 + β * (2 * x 1 - 1)] G := by
  unfold stripNormalized
  rw [aeval_def]
  change eval₂ (RingHom.id ℝ) x (eval₂ C (stripSub u v β) G) = _
  rw [← eval₂_assoc]
  congr 1
  ext i
  fin_cases i <;> simp [stripSub]

theorem stripNormalized_eval_complex (G : MvPolynomial (Fin 2) ℝ) (u v β : ℝ) (x : Fin 2 → ℂ) :
    eval₂ (algebraMap ℝ ℂ) x (stripNormalized G u v β) =
      eval₂ (algebraMap ℝ ℂ) ![x 0, (u : ℂ) + (v : ℂ) * x 0 + (β : ℂ) * (2 * x 1 - 1)] G := by
  unfold stripNormalized
  rw [aeval_def]
  change eval₂ (algebraMap ℝ ℂ) x (eval₂ C (stripSub u v β) G) = _
  rw [← eval₂_assoc]
  congr 1
  ext i
  fin_cases i <;> simp [stripSub]

/-- A single fixed constant controls all normalized projected quadratics on
complex boxes. It depends only on dimension two and degree two. -/
theorem exists_projected_strip_complex_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (G : MvPolynomial (Fin 2) ℝ), G.totalDegree ≤ 2 →
      ∀ (u v β H : ℝ), 0 ≤ H →
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1,
        |eval ![t, u + t * v + β * w] G| ≤ H) →
      ∀ (R : ℝ), 1 ≤ R → ∀ x : Fin 2 → ℂ, (∀ i, ‖x i‖ ≤ R) →
        ‖eval₂ (algebraMap ℝ ℂ) ![x 0, (u : ℂ) + (v : ℂ) * x 0 + (β : ℂ) * (2 * x 1 - 1)] G‖ ≤
          9 * C * H * R ^ 2 := by
  obtain ⟨C, hC, hcoeff⟩ := Submission.Lib.K4PolynomialRemezThree.exists_coefficient_bound_on_unit_cube 2 2
  refine ⟨C, hC, ?_⟩
  intro G hG u v β H hH hstrip R hR x hx
  have hdeg : (stripNormalized G u v β).totalDegree ≤ 2 := (stripNormalized_degree G u v β).trans hG
  have hbox (y : Fin 2 → ℝ) (hy : y ∈ Icc 0 1) : |eval y (stripNormalized G u v β)| ≤ H := by
    rw [stripNormalized_eval]
    have ht : y 0 ∈ Icc (0 : ℝ) 1 := ⟨hy.1 0, hy.2 0⟩
    have hw : 2 * y 1 - 1 ∈ Icc (-1 : ℝ) 1 := by
      have h₀ : 0 ≤ y 1 := hy.1 1
      have h₁ : y 1 ≤ 1 := hy.2 1
      constructor <;> linarith
    simpa only [mul_comm v] using hstrip (y 0) ht (2 * y 1 - 1) hw
  have hc := hcoeff (stripNormalized G u v β) hdeg H hH hbox
  have h := Submission.Lib.K4PolynomialRemezThree.norm_complex_eval_le_of_coeff_bound
    2 2 (stripNormalized G u v β) hdeg (mul_nonneg hC.le hH) hR hc x hx
  rw [stripNormalized_eval_complex] at h
  convert h using 1 <;> norm_num <;> ring

end

end Submission.Obl.k4_general_wide_layer_offset_comparison.Native.CommonDomain
