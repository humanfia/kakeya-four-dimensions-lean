-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Restoration/BranchConstruction.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o267, branch x0945, commit 7135e2fbe574;
-- source Submission/Obl/k4_original_potential_reference_completion/BranchConstruction.lean (session x0945).
-- Existing source attributions are preserved below.

import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.UniformSignedBranch
import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.QuadraticBranchExtensions
import Submission.Lib.K4QuadraticSheetsReal

/-!
# The dilated native branch with its rational presentation

`uniform_signed_branch_with_extensions` (o143, x0487) builds the signed simple root of the
native base equation `a w² + B w + C₀ = 0` after the uniform base dilation `A^(-M)`, with all
four sampled extension fields. The trajectory tests also need the rational presentation
`W F = U + V s`, `s² = Δ`, with `W` nonzero at every point; `presentation_of_simple_quadratic_branch`
supplies it on the same complex ball.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open MvPolynomial Metric
open scoped ContDiff

/-- The dilated signed branch, its extensions, and the rational presentation. -/
theorem uniform_branch_with_presentation (d : ℕ) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ A : ℝ, 2 ≤ A →
      ∀ (B C₀ : MvPolynomial (Fin 3) ℝ) (a σ : ℝ),
      B.totalDegree ≤ d → C₀.totalDegree ≤ d → σ ≠ 0 →
      (a = 0 → 0 < eval (fun _ => (0 : ℝ)) B * σ) →
      (∀ m, |(nativeBaseDiscriminant a B C₀).coeff m| ≤ A) →
      (A⁻¹) ^ 2 ≤ eval (fun _ => (0 : ℝ)) (nativeBaseDiscriminant a B C₀) →
      ∃ (F : EuclideanSpace ℂ (Fin 3) → ℂ) (f : Base → ℝ) (Δ U V W : MvPolynomial (Fin 3) ℂ)
        (sq : EuclideanSpace ℂ (Fin 3) → ℂ),
        ContDiffOn ℂ ⊤ F (ball 0 4) ∧ ContDiffOn ℝ 6 f (ball 0 3) ∧
        (∀ x ∈ ball (0 : Base) 4, F (DenseJet.realSlice x) = (f x : ℂ)) ∧
        (∀ x ∈ ball (0 : Base) 4,
          a * (f x) ^ 2 + eval (fun i => x i) (baseDilation (A ^ M)⁻¹ B) * f x +
            eval (fun i => x i) (baseDilation (A ^ M)⁻¹ C₀) = 0 ∧
          0 < (2 * a * f x + eval (fun i => x i) (baseDilation (A ^ M)⁻¹ B)) * σ) ∧
        W ≠ 0 ∧ Δ.totalDegree ≤ 2 * (d + 1) ∧ U.totalDegree ≤ 2 * (d + 1) ∧
        V.totalDegree ≤ 2 * (d + 1) ∧ W.totalDegree ≤ 2 * (d + 1) ∧
        (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4, (sq z) ^ 2 = eval (fun i => z i) Δ) ∧
        (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
          eval (fun i => z i) W * F z = eval (fun i => z i) U + eval (fun i => z i) V * sq z) ∧
        (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4, eval (fun i => z i) W ≠ 0) ∧
        ∀ (S : Poly) (lam : ℝ), S.totalDegree ≤ 2 → lam ≠ 0 →
          HasRealExtension (864 * (2 * (d + 1)) + 2) f ∧
          (∀ v : Base, HasRealExtension (864 * (2 * (d + 1)) + 2)
            (fun x => iteratedFDeriv ℝ 2 f x (fun _ => v))) ∧
          HasRealExtension (864 * (2 * (d + 1)) + 2)
            (fun x => eval ![x 0, x 1, x 2, f x] S / lam) ∧
          (∀ v : Base, HasRealExtension (864 * (2 * (d + 1)) + 2)
            (fun x => iteratedFDeriv ℝ 3
              (fun y => eval ![y 0, y 1, y 2, f y] S / lam) x (fun _ => v))) := by
  obtain ⟨M, hM, hbranch⟩ := uniform_signed_branch_with_extensions d
  refine ⟨M, hM, ?_⟩
  intro A hA B C₀ a σ hB hC hσ hσ0 hcoeff hcenter
  obtain ⟨F, f, hF, hf, hmatch, hcomplex, hreal, hext⟩ :=
    hbranch A hA B C₀ a σ hB hC hσ hσ0 hcoeff hcenter
  set Bδ := baseDilation (A ^ M)⁻¹ B
  set Cδ := baseDilation (A ^ M)⁻¹ C₀
  have hBδ : (Bδ.map (algebraMap ℝ ℂ)).totalDegree ≤ d :=
    (Submission.Lib.K4QuadraticSheetsReal.totalDegree_map_le' _ _).trans ((baseDilation_totalDegree _ B).trans hB)
  have hCδ : (Cδ.map (algebraMap ℝ ℂ)).totalDegree ≤ d :=
    (Submission.Lib.K4QuadraticSheetsReal.totalDegree_map_le' _ _).trans ((baseDilation_totalDegree _ C₀).trans hC)
  obtain ⟨Δ, U, V, W, _hΔ0, hW0, hΔd, hUd, hVd, hWd, hpres⟩ :=
    presentation_of_simple_quadratic_branch d (Bδ.map (algebraMap ℝ ℂ))
      (Cδ.map (algebraMap ℝ ℂ)) hBδ hCδ (a : ℂ) (ball 0 4) (by simp) F
      (fun z hz => (hcomplex z hz).1) (fun z hz => (hcomplex z hz).2)
  refine ⟨F, f, Δ, U, V, W,
    fun z => eval (fun i => z i) (Bδ.map (algebraMap ℝ ℂ)) + 2 * (a : ℂ) * F z,
    hF, hf, hmatch, hreal, hW0, hΔd, hUd, hVd, hWd, ?_, ?_, ?_, hext⟩
  · exact fun z hz => (hpres z hz).1
  · exact fun z hz => (hpres z hz).2.1
  · exact fun z hz => (hpres z hz).2.2

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
