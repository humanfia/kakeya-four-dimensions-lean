-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Analytic.RationalCurve, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Analytic/RationalCurve.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Analytic/RationalCurve.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Analytic/RationalCurve.lean.
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (including x0491 contributions),
-- branch merged/o143/x0487, commit 36234c3602987ce26ddd4bced782149873fbaa4e.
-- Original file: Submission/Obl/k4_isotropic_discovery_of_local_restoration/RationalCurve.lean
-- Earlier source attributions below are retained.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.PolynomialDirectional
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.RationalDerivative

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic

noncomputable section

open Filter MvPolynomial
open scoped Topology

/-- Actual differentiation of a local rational square-root representation
gives the formal numerator/denominator update. Only local identities on a
neighbourhood of the differentiation point are needed. -/
theorem eval_sqrtRationalNext_of_derivative {n : ℕ}
    (Δ U V W : MvPolynomial (Fin n) ℂ) (a v : Fin n → ℂ)
    (s g : ℂ → ℂ) (t ds dg : ℂ)
    (hs : HasDerivAt s ds t) (hg : HasDerivAt g dg t)
    (hroot : (fun z => (s z) ^ 2) =ᶠ[𝓝 t]
      (fun z => eval (fun i => a i + z * v i) Δ))
    (hrep : (fun z => eval (fun i => a i + z * v i) W * g z) =ᶠ[𝓝 t]
      (fun z => eval (fun i => a i + z * v i) U +
        eval (fun i => a i + z * v i) V * s z)) :
    eval (fun i => a i + t * v i) (sqrtRationalNextW Δ W) * dg =
      eval (fun i => a i + t * v i)
        (sqrtRationalNextU (complexPolynomialDirectional v) Δ U W) +
      eval (fun i => a i + t * v i)
        (sqrtRationalNextV (complexPolynomialDirectional v) Δ V W) * s t := by
  have hp (P : MvPolynomial (Fin n) ℂ) := hasDerivAt_eval_complex_line P a v t
  have hroot' : (fun z => s z * s z) =ᶠ[𝓝 t]
      (fun z => eval (fun i => a i + z * v i) Δ) := by
    simpa only [pow_two] using hroot
  have hds := hroot'.deriv_eq
  rw [(hs.fun_mul hs).deriv, (hp Δ).deriv] at hds
  have hdg := hrep.deriv_eq
  rw [((hp W).fun_mul hg).deriv, ((hp U).fun_add ((hp V).fun_mul hs)).deriv] at hdg
  apply eval_sqrtRationalNext (complexPolynomialDirectional v) Δ U V W
    (fun i => a i + t * v i) (s t) ds (g t) dg hroot.eq_of_nhds
  · linear_combination hds
  · exact hrep.eq_of_nhds
  · simpa only [add_assoc] using hdg

/-- The actual derivative along every affine complex line obeys one fixed
nonzero polynomial relation. Its degree depends only on the four input
degrees, not on the point, anchor, branch values or denominator size. -/
theorem exists_rational_curve_derivative_relation {n : ℕ} (D : ℕ)
    (Δ U V W : MvPolynomial (Fin n) ℂ) (v : Fin n → ℂ)
    (hΔ : Δ.totalDegree ≤ D) (hU : U.totalDegree ≤ D)
    (hV : V.totalDegree ≤ D) (hW : W.totalDegree ≤ D)
    (hΔne : Δ ≠ 0) (hWne : W ≠ 0) :
    ∃ P : MvPolynomial (Fin (n + 1)) ℂ, P ≠ 0 ∧ P.totalDegree ≤ 24 * D + 2 ∧
      ∀ (a : Fin n → ℂ) (s g : ℂ → ℂ) (t ds dg : ℂ),
        HasDerivAt s ds t → HasDerivAt g dg t →
        (fun z => (s z) ^ 2) =ᶠ[𝓝 t]
          (fun z => eval (fun i => a i + z * v i) Δ) →
        (fun z => eval (fun i => a i + z * v i) W * g z) =ᶠ[𝓝 t]
          (fun z => eval (fun i => a i + z * v i) U +
            eval (fun i => a i + z * v i) V * s z) →
        eval (Fin.snoc (fun i => a i + t * v i) dg) P = 0 := by
  let δ := complexPolynomialDirectional v
  have hδ : ∀ P : MvPolynomial (Fin n) ℂ, P.totalDegree ≤ D → (δ P).totalDegree ≤ D :=
    fun P hP => (complexPolynomialDirectional_totalDegree v P).trans hP
  obtain ⟨hnextU, hnextV, hnextW⟩ := sqrtRationalNext_degrees D δ hδ Δ U V W hΔ hU hV hW
  let U' := sqrtRationalNextU δ Δ U W
  let V' := sqrtRationalNextV δ Δ V W
  let W' := sqrtRationalNextW Δ W
  refine ⟨sqrtRationalRelation Δ U' V' W',
    sqrtRationalRelation_ne_zero Δ U' V' W' (sqrtRationalNextW_ne_zero Δ W hΔne hWne),
    (sqrtRationalRelation_totalDegree Δ U' V' W').trans ?_, ?_⟩
  · dsimp [U', V', W']
    omega
  · intro a s g t ds dg hs hg hroot hrep
    exact eval_sqrtRationalRelation Δ U' V' W' (fun i => a i + t * v i)
      (s t) dg hroot.eq_of_nhds
      (eval_sqrtRationalNext_of_derivative Δ U V W a v s g t ds dg hs hg hroot hrep)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic
