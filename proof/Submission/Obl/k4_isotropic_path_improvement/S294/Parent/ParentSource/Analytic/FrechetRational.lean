-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Analytic.FrechetRational, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Analytic/FrechetRational.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Analytic/FrechetRational.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Analytic/FrechetRational.lean.
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (including x0491 contributions),
-- branch merged/o143/x0487, commit 36234c3602987ce26ddd4bced782149873fbaa4e.
-- Original file: Submission/Obl/k4_isotropic_discovery_of_local_restoration/FrechetRational.lean
-- Earlier source attributions below are retained.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.RationalCurve

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic

noncomputable section

open Filter MvPolynomial
open scoped Topology

/-- The rational square-root update represents the actual Fréchet derivative
in a fixed direction on the entire open branch domain. Only local line
segments are used, so no smaller common domain is required. -/
theorem frechet_sqrtRationalNext {n : ℕ}
    (Δ U V W : MvPolynomial (Fin n) ℂ) (v : EuclideanSpace ℂ (Fin n))
    (Ω : Set (EuclideanSpace ℂ (Fin n))) (hΩ : IsOpen Ω)
    (s F : EuclideanSpace ℂ (Fin n) → ℂ)
    (hs : DifferentiableOn ℂ s Ω) (hF : DifferentiableOn ℂ F Ω)
    (hroot : ∀ z ∈ Ω, (s z) ^ 2 = eval (fun i => z i) Δ)
    (hrep : ∀ z ∈ Ω, eval (fun i => z i) W * F z =
      eval (fun i => z i) U + eval (fun i => z i) V * s z) :
    ∀ z ∈ Ω, eval (fun i => z i) (sqrtRationalNextW Δ W) * fderiv ℂ F z v =
      eval (fun i => z i) (sqrtRationalNextU (complexPolynomialDirectional (fun i => v i)) Δ U W) +
      eval (fun i => z i) (sqrtRationalNextV (complexPolynomialDirectional (fun i => v i)) Δ V W) * s z := by
  intro z hz
  let l : ℂ → EuclideanSpace ℂ (Fin n) := fun t => z + t • v
  have hl : HasDerivAt l v 0 := by
    simpa [l] using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add z
  have hnear : ∀ᶠ t in 𝓝 (0 : ℂ), l t ∈ Ω := by
    apply hl.continuousAt.eventually
    simpa [l] using hΩ.mem_nhds hz
  have hsAt : HasFDerivAt s (fderiv ℂ s z) (l 0) := by
    simpa [l] using ((hs z hz).differentiableAt (hΩ.mem_nhds hz)).hasFDerivAt
  have hFAt : HasFDerivAt F (fderiv ℂ F z) (l 0) := by
    simpa [l] using ((hF z hz).differentiableAt (hΩ.mem_nhds hz)).hasFDerivAt
  have hsline := hsAt.comp_hasDerivAt 0 hl
  have hFline := hFAt.comp_hasDerivAt 0 hl
  have hrootLine : (fun t => (s (l t)) ^ 2) =ᶠ[𝓝 (0 : ℂ)]
      (fun t => eval (fun i => z i + t * v i) Δ) := by
    filter_upwards [hnear] with t ht
    simpa [l] using hroot (l t) ht
  have hrepLine : (fun t => eval (fun i => z i + t * v i) W * F (l t)) =ᶠ[𝓝 (0 : ℂ)]
      (fun t => eval (fun i => z i + t * v i) U +
        eval (fun i => z i + t * v i) V * s (l t)) := by
    filter_upwards [hnear] with t ht
    simpa [l] using hrep (l t) ht
  have heq := eval_sqrtRationalNext_of_derivative Δ U V W (fun i => z i) (fun i => v i)
    (fun t => s (l t)) (fun t => F (l t)) 0 (fderiv ℂ s z v) (fderiv ℂ F z v)
    hsline hFline hrootLine hrepLine
  simpa [l] using heq

/-- A fixed polynomial relation, with degree controlled before the domain
and branch functions, annihilates the actual directional Fréchet derivative. -/
theorem exists_frechet_directional_relation {n : ℕ} (D : ℕ)
    (Δ U V W : MvPolynomial (Fin n) ℂ) (v : EuclideanSpace ℂ (Fin n))
    (hΔ : Δ.totalDegree ≤ D) (hU : U.totalDegree ≤ D)
    (hV : V.totalDegree ≤ D) (hW : W.totalDegree ≤ D)
    (hΔne : Δ ≠ 0) (hWne : W ≠ 0) :
    ∃ P : MvPolynomial (Fin (n + 1)) ℂ, P ≠ 0 ∧ P.totalDegree ≤ 24 * D + 2 ∧
      ∀ (Ω : Set (EuclideanSpace ℂ (Fin n))), IsOpen Ω →
      ∀ (s F : EuclideanSpace ℂ (Fin n) → ℂ),
        DifferentiableOn ℂ s Ω → DifferentiableOn ℂ F Ω →
        (∀ z ∈ Ω, (s z) ^ 2 = eval (fun i => z i) Δ) →
        (∀ z ∈ Ω, eval (fun i => z i) W * F z =
          eval (fun i => z i) U + eval (fun i => z i) V * s z) →
        ∀ z ∈ Ω, eval (Fin.snoc (fun i => z i) (fderiv ℂ F z v)) P = 0 := by
  let δ := complexPolynomialDirectional (fun i => v i)
  have hδ : ∀ P : MvPolynomial (Fin n) ℂ, P.totalDegree ≤ D → (δ P).totalDegree ≤ D :=
    fun P hP => (complexPolynomialDirectional_totalDegree (fun i => v i) P).trans hP
  obtain ⟨hnextU, hnextV, hnextW⟩ := sqrtRationalNext_degrees D δ hδ Δ U V W hΔ hU hV hW
  let U' := sqrtRationalNextU δ Δ U W
  let V' := sqrtRationalNextV δ Δ V W
  let W' := sqrtRationalNextW Δ W
  refine ⟨sqrtRationalRelation Δ U' V' W',
    sqrtRationalRelation_ne_zero Δ U' V' W' (sqrtRationalNextW_ne_zero Δ W hΔne hWne),
    (sqrtRationalRelation_totalDegree Δ U' V' W').trans ?_, ?_⟩
  · dsimp [U', V', W']
    omega
  · intro Ω hΩ s F hs hF hroot hrep z hz
    exact eval_sqrtRationalRelation Δ U' V' W' (fun i => z i) (s z)
      (fderiv ℂ F z v) (hroot z hz)
      (frechet_sqrtRationalNext Δ U V W v Ω hΩ s F hs hF hroot hrep z hz)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic
