-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Analytic/SignedBranch.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Analytic/SignedBranch.lean.
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (including x0491 contributions),
-- branch merged/o143/x0487, commit 36234c3602987ce26ddd4bced782149873fbaa4e.
-- Original file: Submission/Obl/k4_isotropic_discovery_of_local_restoration/SignedBranch.lean
-- Earlier source attributions below are retained.
import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.NativeSmooth
import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.QuadraticBranchExtensions
import Submission.Obl.k4_stable_quadratic_hidden_sheets.Sheet

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open MvPolynomial Metric
open scoped ContDiff

/-- The accepted sign-selected sheet construction, upgraded to the exact
complex/real regularity and all four algebraic extension fields required
by sampled restoration. Both hidden-derivative signs are allowed. -/
theorem exists_smooth_signed_branch_with_extensions (d : ℕ)
    (B C₀ : MvPolynomial (Fin 3) ℝ) (hB : B.totalDegree ≤ d) (hC : C₀.totalDegree ≤ d)
    (a σ : ℝ) (hσ : σ ≠ 0)
    (hσ0 : a = 0 → 0 < eval (fun _ => (0 : ℝ)) B * σ)
    (hDpos : ∀ y : Fin 3 → ℂ, (∀ i, ‖y i‖ < 4) →
      0 < (eval₂ (algebraMap ℝ ℂ) y (B * B - C (4 * a) * C₀)).re) :
    ∃ (F : EuclideanSpace ℂ (Fin 3) → ℂ) (f : Base → ℝ),
      ContDiffOn ℂ ⊤ F (ball 0 4) ∧ ContDiffOn ℝ 6 f (ball 0 3) ∧
      (∀ x ∈ ball (0 : Base) 4, F (DenseJet.realSlice x) = (f x : ℂ)) ∧
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
        eval (fun i => z i) (C₀.map (algebraMap ℝ ℂ)) +
          eval (fun i => z i) (B.map (algebraMap ℝ ℂ)) * F z + (a : ℂ) * (F z) ^ 2 = 0 ∧
        eval (fun i => z i) (B.map (algebraMap ℝ ℂ)) + 2 * (a : ℂ) * F z ≠ 0) ∧
      (∀ x ∈ ball (0 : Base) 4,
        a * (f x) ^ 2 + eval (fun i => x i) B * f x + eval (fun i => x i) C₀ = 0 ∧
        0 < (2 * a * f x + eval (fun i => x i) B) * σ) ∧
      ∀ (S : Poly) (lam : ℝ), S.totalDegree ≤ 2 → lam ≠ 0 →
        HasRealExtension (864 * (2 * (d + 1)) + 2) f ∧
        (∀ v : Base, HasRealExtension (864 * (2 * (d + 1)) + 2)
          (fun x => iteratedFDeriv ℝ 2 f x (fun _ => v))) ∧
        HasRealExtension (864 * (2 * (d + 1)) + 2)
          (fun x => eval ![x 0, x 1, x 2, f x] S / lam) ∧
        (∀ v : Base, HasRealExtension (864 * (2 * (d + 1)) + 2)
          (fun x => iteratedFDeriv ℝ 3
            (fun y => eval ![y 0, y 1, y 2, f y] S / lam) x (fun _ => v))) := by
  obtain ⟨F, hFd, hFr, hFre⟩ := k4_stable_quadratic_hidden_sheets.exists_sheet a B C₀
    (0 : Base) σ 4 (by norm_num) hσ (by simpa using hσ0) (by
      intro y hy
      exact hDpos y (by simpa using hy))
  have hcenter : WithLp.toLp 2 (fun j : Fin 3 => ((0 : Base) j : ℂ)) =
      (0 : EuclideanSpace ℂ (Fin 3)) := by ext i; rfl
  rw [hcenter] at hFd hFr
  have hroot (z : EuclideanSpace ℂ (Fin 3)) (hz : z ∈ ball 0 4) :
      eval (fun i => z i) (C₀.map (algebraMap ℝ ℂ)) +
        eval (fun i => z i) (B.map (algebraMap ℝ ℂ)) * F z + (a : ℂ) * (F z) ^ 2 = 0 := by
    simpa only [eval₂_eq_eval_map, add_comm, add_left_comm, add_assoc] using hFr z hz
  have hsimple (z : EuclideanSpace ℂ (Fin 3)) (hz : z ∈ ball 0 4) :
      eval (fun i => z i) (B.map (algebraMap ℝ ℂ)) + 2 * (a : ℂ) * F z ≠ 0 := by
    have hnorm : ‖z‖ < 4 := by simpa only [mem_ball, dist_zero_right] using hz
    have hpositive := hDpos (fun i => z i) (fun i => (PiLp.norm_apply_le z i).trans_lt hnorm)
    have hdisc : (eval (fun i => z i) (B.map (algebraMap ℝ ℂ)) + 2 * (a : ℂ) * F z) ^ 2 =
        eval₂ (algebraMap ℝ ℂ) (fun i => z i) (B * B - C (4 * a) * C₀) := by
      rw [k4_stable_quadratic_hidden_sheets.eval₂_disc]
      simp only [eval₂_eq_eval_map]
      linear_combination (4 * (a : ℂ)) * hroot z hz
    intro hzero
    rw [hzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hdisc
    rw [← hdisc] at hpositive
    simpa using hpositive
  have hF : ContDiffOn ℂ ⊤ F (ball 0 4) := contDiffOn_simple_native_quadratic_branch
    (a : ℂ) (B.map (algebraMap ℝ ℂ)) (C₀.map (algebraMap ℝ ℂ))
    isOpen_ball hFd.continuousOn hroot hsimple ⊤
  let f : Base → ℝ := fun x => (F (DenseJet.realSlice x)).re
  have hrealdata (x : Base) (hx : ‖x‖ < 4) :
      F (DenseJet.realSlice x) = (f x : ℂ) ∧
      a * (f x) ^ 2 + eval (fun i => x i) B * f x + eval (fun i => x i) C₀ = 0 ∧
      0 < (2 * a * f x + eval (fun i => x i) B) * σ := by
    obtain ⟨φ, hφ, hrφ, hsφ⟩ := hFre x (by simpa using hx)
    change F (DenseJet.realSlice x) = (φ : ℂ) at hφ
    have hfφ : f x = φ := by dsimp [f]; rw [hφ]; rfl
    rw [hfφ]
    exact ⟨hφ, hrφ, hsφ⟩
  have hreal : ∀ x ∈ ball (0 : Base) 4, F (DenseJet.realSlice x) = (f x : ℂ) :=
    fun x hx => (hrealdata x (by simpa only [mem_ball, dist_zero_right] using hx)).1
  have hfsmooth : ContDiffOn ℝ 6 f (ball 0 3) := by
    intro x hx
    have hx4 : ‖x‖ < 4 := by
      have hx3 : ‖x‖ < 3 := by simpa only [mem_ball, dist_zero_right] using hx
      linarith
    exact ((DenseJet.contDiffAt_real_slice (hF.of_le le_top)
      (fun y hy => (hrealdata y hy).1) hx4).of_le (by simp)).contDiffWithinAt
  refine ⟨F, f, hF, hfsmooth, hreal, (fun z hz => ⟨hroot z hz, hsimple z hz⟩), ?_, ?_⟩
  · intro x hx
    exact (hrealdata x (by simpa only [mem_ball, dist_zero_right] using hx)).2
  · intro S lam hS hlam
    exact simple_quadratic_branch_all_sampled_extensions d
      (B.map (algebraMap ℝ ℂ)) (C₀.map (algebraMap ℝ ℂ))
      ((Submission.Lib.K4QuadraticSheetsReal.totalDegree_map_le' _ B).trans hB)
      ((Submission.Lib.K4QuadraticSheetsReal.totalDegree_map_le' _ C₀).trans hC)
      (a : ℂ) F hF hroot hsimple f hreal S hS lam hlam

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
