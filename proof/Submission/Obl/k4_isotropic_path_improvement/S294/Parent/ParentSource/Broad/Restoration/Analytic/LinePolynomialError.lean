-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Restoration.Analytic.LinePolynomialError, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Restoration/Analytic/LinePolynomialError.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Restoration/Analytic/LinePolynomialError.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o267, branch x0945, commit 7135e2fbe574;
-- source Submission/Obl/k4_original_potential_reference_completion/Analytic/LinePolynomialError.lean (session x0945).
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (with x0491's contributions), branch x0487,
-- commit 36234c36, file Submission/Obl/k4_isotropic_discovery_of_local_restoration/LinePolynomialError.lean
-- (namespace renamed; the attributions that file carries are kept below).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Restoration.Analytic.LineRestriction

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic

noncomputable section

open MvPolynomial

/-- A polynomial hidden fit of any fixed degree can be subtracted on the
trajectory line without leaving the same quadratic extension. In particular,
a quadratic fit can be removed before estimating third residual derivatives. -/
theorem exists_polynomial_line_error_relation {n : ℕ} (D e : ℕ)
    (Δ U V W : MvPolynomial (Fin n) ℂ)
    (hΔ : Δ.totalDegree ≤ D) (hU : U.totalDegree ≤ D)
    (hV : V.totalDegree ≤ D) (hW : W.totalDegree ≤ D)
    (a v : Fin n → ℂ) (A : MvPolynomial (Fin 1) ℂ)
    (hA : A.totalDegree ≤ e) (hWa : eval a W ≠ 0) :
    ∃ P : MvPolynomial (Fin 2) ℂ,
      P ≠ 0 ∧ P.totalDegree ≤ 8 * (D + e) + 2 ∧
      ∀ t s g : ℂ, s ^ 2 = eval (fun i => a i + t * v i) Δ →
        eval (fun i => a i + t * v i) W * g =
          eval (fun i => a i + t * v i) U +
            eval (fun i => a i + t * v i) V * s →
        eval (Fin.snoc (fun _ : Fin 1 => t) (g - eval (fun _ : Fin 1 => t) A)) P = 0 := by
  let Δ' := complexLineRestriction a v Δ
  let V' := complexLineRestriction a v V
  let W' := complexLineRestriction a v W
  let U' := complexLineRestriction a v U - W' * A
  have hΔ' : Δ'.totalDegree ≤ D := (complexLineRestriction_totalDegree a v Δ).trans hΔ
  have hV' : V'.totalDegree ≤ D := (complexLineRestriction_totalDegree a v V).trans hV
  have hW' : W'.totalDegree ≤ D := (complexLineRestriction_totalDegree a v W).trans hW
  have hU' : U'.totalDegree ≤ D + e :=
    (totalDegree_sub _ _).trans (max_le
      (((complexLineRestriction_totalDegree a v U).trans hU).trans (by omega))
      ((totalDegree_mul _ _).trans (add_le_add hW' hA)))
  refine ⟨sqrtRationalRelation Δ' U' V' W',
    sqrtRationalRelation_ne_zero Δ' U' V' W' (complexLineRestriction_ne_zero a v W hWa),
    (sqrtRationalRelation_totalDegree Δ' U' V' W').trans (by omega), ?_⟩
  intro t s g hs hg
  apply eval_sqrtRationalRelation Δ' U' V' W' (fun _ : Fin 1 => t) s
    (g - eval (fun _ : Fin 1 => t) A)
  · simpa only [Δ', eval_complexLineRestriction] using hs
  · dsimp [U', V', W']
    simp only [map_sub, map_mul, eval_complexLineRestriction]
    linear_combination hg

/-- The polynomial-fit error as a one-dimensional algebraic sheet on the
standard complex ball. This is the interface for dense witness norming. -/
theorem hasSheetRelation_polynomial_line_error {n : ℕ} (D e : ℕ)
    (Δ U V W : MvPolynomial (Fin n) ℂ)
    (hΔ : Δ.totalDegree ≤ D) (hU : U.totalDegree ≤ D)
    (hV : V.totalDegree ≤ D) (hW : W.totalDegree ≤ D)
    (Ω : Set (EuclideanSpace ℂ (Fin n)))
    (s F : EuclideanSpace ℂ (Fin n) → ℂ)
    (hroot : ∀ z ∈ Ω, (s z) ^ 2 = eval (fun i => z i) Δ)
    (hrep : ∀ z ∈ Ω, eval (fun i => z i) W * F z =
      eval (fun i => z i) U + eval (fun i => z i) V * s z)
    (a v : EuclideanSpace ℂ (Fin n)) (A : MvPolynomial (Fin 1) ℂ)
    (hA : A.totalDegree ≤ e) (hWa : eval (fun i => a i) W ≠ 0)
    (hmap : Set.MapsTo (fun z : EuclideanSpace ℂ (Fin 1) => a + z 0 • v)
      (Metric.ball 0 4) Ω) :
    k4_algebraic_real_jet_comparison.HasSheetRelation 1 (8 * (D + e) + 2)
      (fun z => F (a + z 0 • v) - eval (fun i => z i) A) := by
  obtain ⟨P, hPne, hPdeg, hPrel⟩ := exists_polynomial_line_error_relation D e Δ U V W
    hΔ hU hV hW (fun i => a i) (fun i => v i) A hA hWa
  refine ⟨P, hPne, hPdeg, ?_⟩
  intro z hz
  have hrootLine : (s (a + z 0 • v)) ^ 2 =
      eval (fun i => a i + z 0 * v i) Δ := by
    simpa using hroot (a + z 0 • v) (hmap hz)
  have hrepLine : eval (fun i => a i + z 0 * v i) W * F (a + z 0 • v) =
      eval (fun i => a i + z 0 * v i) U +
        eval (fun i => a i + z 0 * v i) V * s (a + z 0 • v) := by
    simpa using hrep (a + z 0 • v) (hmap hz)
  have heq := hPrel (z 0) (s (a + z 0 • v)) (F (a + z 0 • v)) hrootLine hrepLine
  have hcoord : (fun _ : Fin 1 => z 0) = (fun i => z i) := by
    funext i
    fin_cases i
    rfl
  simpa only [hcoord] using heq

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic
