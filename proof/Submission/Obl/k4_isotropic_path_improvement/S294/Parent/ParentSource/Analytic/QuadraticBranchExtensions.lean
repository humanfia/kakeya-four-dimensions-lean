-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Analytic.QuadraticBranchExtensions, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Analytic/QuadraticBranchExtensions.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Analytic/QuadraticBranchExtensions.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Analytic/QuadraticBranchExtensions.lean.
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (including x0491 contributions),
-- branch merged/o143/x0487, commit 36234c3602987ce26ddd4bced782149873fbaa4e.
-- Original file: Submission/Obl/k4_isotropic_discovery_of_local_restoration/QuadraticBranchExtensions.lean
-- Earlier source attributions below are retained.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.QuadraticRealJets

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic

noncomputable section

open MvPolynomial Metric
open scoped ContDiff

/-- A simple branch of a quadratic in the hidden variable has a rational
presentation in its discriminant square root. The linear case uses the
nonzero linear coefficient as denominator. No lower bound on the quadratic
coefficient is needed, and the base coefficients can have arbitrary degree. -/
theorem presentation_of_simple_quadratic_branch {n : ℕ} (d : ℕ)
    (B C₀ : MvPolynomial (Fin n) ℂ) (hB : B.totalDegree ≤ d)
    (hC : C₀.totalDegree ≤ d) (a : ℂ)
    (Ω : Set (EuclideanSpace ℂ (Fin n))) (hzero : (0 : EuclideanSpace ℂ (Fin n)) ∈ Ω)
    (F : EuclideanSpace ℂ (Fin n) → ℂ)
    (hroot : ∀ z ∈ Ω, eval (fun i => z i) C₀ +
      eval (fun i => z i) B * F z + a * (F z) ^ 2 = 0)
    (hsimple : ∀ z ∈ Ω, eval (fun i => z i) B + 2 * a * F z ≠ 0) :
    ∃ Δ U V W : MvPolynomial (Fin n) ℂ,
      Δ ≠ 0 ∧ W ≠ 0 ∧ Δ.totalDegree ≤ 2 * (d + 1) ∧
      U.totalDegree ≤ 2 * (d + 1) ∧ V.totalDegree ≤ 2 * (d + 1) ∧
      W.totalDegree ≤ 2 * (d + 1) ∧
      ∀ z ∈ Ω,
        (eval (fun i => z i) B + 2 * a * F z) ^ 2 = eval (fun i => z i) Δ ∧
        eval (fun i => z i) W * F z = eval (fun i => z i) U +
          eval (fun i => z i) V * (eval (fun i => z i) B + 2 * a * F z) ∧
        eval (fun i => z i) W ≠ 0 := by
  let Δ := B ^ 2 - C (4 * a) * C₀
  have hΔdeg : Δ.totalDegree ≤ 2 * (d + 1) := by
    apply (totalDegree_sub _ _).trans
    refine max_le ((totalDegree_pow B 2).trans ?_) ((totalDegree_mul _ _).trans ?_)
    · exact (Nat.mul_le_mul_left 2 hB).trans (by omega)
    · simpa only [totalDegree_C, zero_add] using hC.trans (by omega : d ≤ 2 * (d + 1))
  have hdisc (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ Ω) :
      (eval (fun i => z i) B + 2 * a * F z) ^ 2 = eval (fun i => z i) Δ := by
    simp only [Δ, map_sub, map_pow, map_mul, eval_C]
    linear_combination (4 * a) * hroot z hz
  have hΔne : Δ ≠ 0 := by
    intro hzeroPoly
    have heq := hdisc 0 hzero
    rw [hzeroPoly, map_zero] at heq
    exact pow_ne_zero 2 (hsimple 0 hzero) heq
  by_cases ha : a = 0
  · have hBne : B ≠ 0 := by
      intro hzeroPoly
      have h := hsimple 0 hzero
      simp [ha, hzeroPoly] at h
    refine ⟨Δ, -C₀, 0, B, hΔne, hBne, hΔdeg, ?_, by simp,
      hB.trans (by omega), ?_⟩
    · simpa only [totalDegree_neg] using hC.trans (by omega : d ≤ 2 * (d + 1))
    · intro z hz
      refine ⟨hdisc z hz, ?_, ?_⟩
      · simp only [map_neg, map_zero, zero_mul, add_zero]
        have heq := hroot z hz
        simp only [ha, zero_mul, add_zero] at heq
        linear_combination heq
      · simpa only [ha, mul_zero, zero_mul, add_zero] using hsimple z hz
  · have h2a : 2 * a ≠ 0 := mul_ne_zero (by norm_num) ha
    refine ⟨Δ, -B, 1, C (2 * a), hΔne, by simpa using h2a, hΔdeg,
      ?_, by simp, by rw [totalDegree_C]; omega, ?_⟩
    · simpa only [totalDegree_neg] using hB.trans (by omega : d ≤ 2 * (d + 1))
    · intro z hz
      refine ⟨hdisc z hz, ?_, ?_⟩
      · simp only [eval_C, map_neg, map_one, one_mul]
        ring
      · simpa only [eval_C] using h2a

/-- Simple native quadratic branches supply all sampled extension fields
at a degree chosen solely from their base-polynomial degree. This includes
vanishing hidden curvature and arbitrarily small nonzero hidden curvature. -/
theorem simple_quadratic_branch_all_sampled_extensions (d : ℕ)
    (B C₀ : MvPolynomial (Fin 3) ℂ) (hB : B.totalDegree ≤ d)
    (hC : C₀.totalDegree ≤ d) (a : ℂ)
    (F : EuclideanSpace ℂ (Fin 3) → ℂ)
    (hF : ContDiffOn ℂ ⊤ F (ball 0 4))
    (hroot : ∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
      eval (fun i => z i) C₀ + eval (fun i => z i) B * F z + a * (F z) ^ 2 = 0)
    (hsimple : ∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
      eval (fun i => z i) B + 2 * a * F z ≠ 0)
    (f : Base → ℝ)
    (hfF : ∀ x ∈ ball (0 : Base) 4, F (DenseJet.realSlice x) = (f x : ℂ))
    (S : Poly) (hS : S.totalDegree ≤ 2) (lam : ℝ) (hlam : lam ≠ 0) :
    HasRealExtension (864 * (2 * (d + 1)) + 2) f ∧
    (∀ v : Base, HasRealExtension (864 * (2 * (d + 1)) + 2)
      (fun x => iteratedFDeriv ℝ 2 f x (fun _ => v))) ∧
    HasRealExtension (864 * (2 * (d + 1)) + 2)
      (fun x => eval ![x 0, x 1, x 2, f x] S / lam) ∧
    (∀ v : Base, HasRealExtension (864 * (2 * (d + 1)) + 2)
      (fun x => iteratedFDeriv ℝ 3
        (fun y => eval ![y 0, y 1, y 2, f y] S / lam) x (fun _ => v))) := by
  obtain ⟨Δ, U, V, W, hΔne, hWne, hΔ, hU, hV, hW, hdata⟩ :=
    presentation_of_simple_quadratic_branch d B C₀ hB hC a (ball 0 4)
      (by simp) F hroot hsimple
  let s : EuclideanSpace ℂ (Fin 3) → ℂ :=
    fun z => eval (fun i => z i) B + 2 * a * F z
  have hBsm : ContDiffOn ℂ ⊤ (fun z : EuclideanSpace ℂ (Fin 3) => eval (fun i => z i) B)
      (ball 0 4) := by
    apply k4_quadratic_sheet_continuation.contDiffOn_polynomial_eval
    intro i
    fun_prop
  have hs : DifferentiableOn ℂ s (ball 0 4) :=
    (hBsm.add ((contDiffOn_const : ContDiffOn ℂ ⊤
      (fun _ : EuclideanSpace ℂ (Fin 3) => 2 * a) (ball 0 4)).mul hF)).differentiableOn (by simp)
  exact rational_branch_all_sampled_extensions (2 * (d + 1)) (by omega)
    Δ U V W hΔ hU hV hW hΔne hWne s F hs hF
    (fun z hz => (hdata z hz).1) (fun z hz => (hdata z hz).2.1)
    f hfF S hS lam hlam

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic
