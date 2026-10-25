-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Analytic/UniformSignedBranch.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Analytic/UniformSignedBranch.lean.
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (including x0491 contributions),
-- branch merged/o143/x0487, commit 36234c3602987ce26ddd4bced782149873fbaa4e.
-- Original file: Submission/Obl/k4_isotropic_discovery_of_local_restoration/UniformSignedBranch.lean
-- Earlier source attributions below are retained.
import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.BoxDilation
import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.SignedBranch

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open MvPolynomial Metric
open scoped ContDiff

/-- One exponent, fixed before the coefficient height and all native data,
constructs either sign-selected smooth branch after dilation, together
with every algebraic extension required by the sampled certificate. -/
theorem uniform_signed_branch_with_extensions (d : ℕ) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ A : ℝ, 2 ≤ A →
      ∀ (B C₀ : MvPolynomial (Fin 3) ℝ) (a σ : ℝ),
      B.totalDegree ≤ d → C₀.totalDegree ≤ d → σ ≠ 0 →
      (a = 0 → 0 < eval (fun _ => (0 : ℝ)) B * σ) →
      (∀ m, |(nativeBaseDiscriminant a B C₀).coeff m| ≤ A) →
      (A⁻¹) ^ 2 ≤ eval (fun _ => (0 : ℝ)) (nativeBaseDiscriminant a B C₀) →
      let Bδ := baseDilation (A ^ M)⁻¹ B
      let Cδ := baseDilation (A ^ M)⁻¹ C₀
      ∃ (F : EuclideanSpace ℂ (Fin 3) → ℂ) (f : Base → ℝ),
        ContDiffOn ℂ ⊤ F (ball 0 4) ∧ ContDiffOn ℝ 6 f (ball 0 3) ∧
        (∀ x ∈ ball (0 : Base) 4, F (DenseJet.realSlice x) = (f x : ℂ)) ∧
        (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
          eval (fun i => z i) (Cδ.map (algebraMap ℝ ℂ)) +
            eval (fun i => z i) (Bδ.map (algebraMap ℝ ℂ)) * F z + (a : ℂ) * (F z) ^ 2 = 0 ∧
          eval (fun i => z i) (Bδ.map (algebraMap ℝ ℂ)) + 2 * (a : ℂ) * F z ≠ 0) ∧
        (∀ x ∈ ball (0 : Base) 4,
          a * (f x) ^ 2 + eval (fun i => x i) Bδ * f x + eval (fun i => x i) Cδ = 0 ∧
          0 < (2 * a * f x + eval (fun i => x i) Bδ) * σ) ∧
        ∀ (S : Poly) (lam : ℝ), S.totalDegree ≤ 2 → lam ≠ 0 →
          HasRealExtension (864 * (2 * (d + 1)) + 2) f ∧
          (∀ v : Base, HasRealExtension (864 * (2 * (d + 1)) + 2)
            (fun x => iteratedFDeriv ℝ 2 f x (fun _ => v))) ∧
          HasRealExtension (864 * (2 * (d + 1)) + 2)
            (fun x => eval ![x 0, x 1, x 2, f x] S / lam) ∧
          (∀ v : Base, HasRealExtension (864 * (2 * (d + 1)) + 2)
            (fun x => iteratedFDeriv ℝ 3
              (fun y => eval ![y 0, y 1, y 2, f y] S / lam) x (fun _ => v))) := by
  obtain ⟨M, hM, hpositive⟩ := native_discriminant_on_box_after_uniform_dilation d
  refine ⟨M, hM, ?_⟩
  intro A hA B C₀ a σ hB hC hσ hσ0 hcoeff hcenter
  apply exists_smooth_signed_branch_with_extensions d
    (baseDilation (A ^ M)⁻¹ B) (baseDilation (A ^ M)⁻¹ C₀)
    ((baseDilation_totalDegree _ B).trans hB) ((baseDilation_totalDegree _ C₀).trans hC) a σ hσ
  · intro ha
    simpa only [eval_baseDilation, mul_zero] using hσ0 ha
  · exact hpositive A hA B C₀ a hB hC hcoeff hcenter

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
