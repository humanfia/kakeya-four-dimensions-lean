-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Analytic.RationalDerivative, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Analytic/RationalDerivative.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Analytic/RationalDerivative.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Analytic/RationalDerivative.lean.
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (including x0491 contributions),
-- branch merged/o143/x0487, commit 36234c3602987ce26ddd4bced782149873fbaa4e.
-- Original file: Submission/Obl/k4_isotropic_discovery_of_local_restoration/RationalDerivative.lean
-- Earlier source attributions below are retained.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.RationalSquareRoot

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic

noncomputable section

open MvPolynomial

/-- The product and square-root differentiation identities preserve a rational
representation in the same square root. No division is needed in this step. -/
theorem rational_sqrt_derivative_identity {R : Type*} [CommRing R]
    (Δ U V W dΔ dU dV dW s ds g dg : R)
    (hs : s ^ 2 = Δ) (hds : 2 * s * ds = dΔ)
    (hg : W * g = U + V * s)
    (hdg : dW * g + W * dg = dU + dV * s + V * ds) :
    (2 * Δ * W ^ 2) * dg =
      2 * Δ * (dU * W - U * dW) +
        (2 * Δ * (dV * W - V * dW) + V * W * dΔ) * s := by
  linear_combination (2 * Δ * W) * hdg - (2 * Δ * dW) * hg +
    (V * W * s) * hds - (2 * V * W * ds) * hs

def sqrtRationalNextU {n : ℕ}
    (δ : MvPolynomial (Fin n) ℂ → MvPolynomial (Fin n) ℂ)
    (Δ U W : MvPolynomial (Fin n) ℂ) : MvPolynomial (Fin n) ℂ :=
  C 2 * Δ * (δ U * W - U * δ W)

def sqrtRationalNextV {n : ℕ}
    (δ : MvPolynomial (Fin n) ℂ → MvPolynomial (Fin n) ℂ)
    (Δ V W : MvPolynomial (Fin n) ℂ) : MvPolynomial (Fin n) ℂ :=
  C 2 * Δ * (δ V * W - V * δ W) + V * W * δ Δ

def sqrtRationalNextW {n : ℕ}
    (Δ W : MvPolynomial (Fin n) ℂ) : MvPolynomial (Fin n) ℂ := C 2 * Δ * W ^ 2

theorem sqrtRationalNextW_ne_zero {n : ℕ}
    (Δ W : MvPolynomial (Fin n) ℂ) (hΔ : Δ ≠ 0) (hW : W ≠ 0) :
    sqrtRationalNextW Δ W ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (by simp) hΔ) (pow_ne_zero 2 hW)

/-- One differentiation multiplies the numerator/denominator degree bound
by at most three, for every degree-preserving polynomial operator. -/
theorem sqrtRationalNext_degrees {n : ℕ} (D : ℕ)
    (δ : MvPolynomial (Fin n) ℂ → MvPolynomial (Fin n) ℂ)
    (hδ : ∀ P, P.totalDegree ≤ D → (δ P).totalDegree ≤ D)
    (Δ U V W : MvPolynomial (Fin n) ℂ)
    (hΔ : Δ.totalDegree ≤ D) (hU : U.totalDegree ≤ D)
    (hV : V.totalDegree ≤ D) (hW : W.totalDegree ≤ D) :
    (sqrtRationalNextU δ Δ U W).totalDegree ≤ 3 * D ∧
      (sqrtRationalNextV δ Δ V W).totalDegree ≤ 3 * D ∧
      (sqrtRationalNextW Δ W).totalDegree ≤ 3 * D := by
  have hCΔ : (C 2 * Δ).totalDegree ≤ D := by
    apply (totalDegree_mul _ _).trans
    simpa only [totalDegree_C, zero_add] using hΔ
  have hdiff (P : MvPolynomial (Fin n) ℂ) (hP : P.totalDegree ≤ D) :
      (δ P * W - P * δ W).totalDegree ≤ 2 * D := by
    apply (totalDegree_sub _ _).trans
    apply max_le
    · exact (totalDegree_mul _ _).trans ((add_le_add (hδ P hP) hW).trans (by omega))
    · exact (totalDegree_mul _ _).trans ((add_le_add hP (hδ W hW)).trans (by omega))
  have hfirst (P : MvPolynomial (Fin n) ℂ) (hP : P.totalDegree ≤ D) :
      (C 2 * Δ * (δ P * W - P * δ W)).totalDegree ≤ 3 * D :=
    (totalDegree_mul _ _).trans ((add_le_add hCΔ (hdiff P hP)).trans (by omega))
  refine ⟨hfirst U hU, ?_, ?_⟩
  · apply (totalDegree_add _ _).trans
    refine max_le (hfirst V hV) ?_
    exact (totalDegree_mul _ _).trans ((add_le_add
      ((totalDegree_mul _ _).trans (add_le_add hV hW)) (hδ Δ hΔ)).trans (by omega))
  · exact (totalDegree_mul _ _).trans ((add_le_add hCΔ
      ((totalDegree_pow _ 2).trans (Nat.mul_le_mul_left 2 hW))).trans (by omega))

theorem eval_sqrtRationalNext {n : ℕ}
    (δ : MvPolynomial (Fin n) ℂ → MvPolynomial (Fin n) ℂ)
    (Δ U V W : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) (s ds g dg : ℂ)
    (hs : s ^ 2 = eval x Δ) (hds : 2 * s * ds = eval x (δ Δ))
    (hg : eval x W * g = eval x U + eval x V * s)
    (hdg : eval x (δ W) * g + eval x W * dg =
      eval x (δ U) + eval x (δ V) * s + eval x V * ds) :
    eval x (sqrtRationalNextW Δ W) * dg =
      eval x (sqrtRationalNextU δ Δ U W) +
        eval x (sqrtRationalNextV δ Δ V W) * s := by
  simp only [sqrtRationalNextW, sqrtRationalNextU, sqrtRationalNextV,
    map_add, map_sub, map_mul, map_pow, eval_C]
  exact rational_sqrt_derivative_identity _ _ _ _ _ _ _ _ _ _ _ _ hs hds hg hdg

/-- A derivative obeying the two differentiation identities has relation
degree at most `24*D+2`. The actual calculus identities are explicit inputs. -/
theorem sqrt_rational_derivative_relation {n : ℕ} (D : ℕ)
    (δ : MvPolynomial (Fin n) ℂ → MvPolynomial (Fin n) ℂ)
    (hδ : ∀ P, P.totalDegree ≤ D → (δ P).totalDegree ≤ D)
    (Δ U V W : MvPolynomial (Fin n) ℂ)
    (hΔ : Δ.totalDegree ≤ D) (hU : U.totalDegree ≤ D)
    (hV : V.totalDegree ≤ D) (hWd : W.totalDegree ≤ D)
    (hΔne : Δ ≠ 0) (hWne : W ≠ 0) :
    ∃ P : MvPolynomial (Fin (n + 1)) ℂ, P ≠ 0 ∧ P.totalDegree ≤ 24 * D + 2 ∧
      ∀ (x : Fin n → ℂ) (s ds g dg : ℂ),
        s ^ 2 = eval x Δ → 2 * s * ds = eval x (δ Δ) →
        eval x W * g = eval x U + eval x V * s →
        eval x (δ W) * g + eval x W * dg =
          eval x (δ U) + eval x (δ V) * s + eval x V * ds →
        eval (Fin.snoc x dg) P = 0 := by
  obtain ⟨hnextU, hnextV, hnextW⟩ := sqrtRationalNext_degrees D δ hδ Δ U V W hΔ hU hV hWd
  let U' := sqrtRationalNextU δ Δ U W
  let V' := sqrtRationalNextV δ Δ V W
  let W' := sqrtRationalNextW Δ W
  refine ⟨sqrtRationalRelation Δ U' V' W',
    sqrtRationalRelation_ne_zero Δ U' V' W' (sqrtRationalNextW_ne_zero Δ W hΔne hWne),
    (sqrtRationalRelation_totalDegree Δ U' V' W').trans ?_, ?_⟩
  · change 2 * (Δ.totalDegree + U'.totalDegree + V'.totalDegree + W'.totalDegree + 1) ≤ _
    change (sqrtRationalNextU δ Δ U W).totalDegree ≤ 3 * D at hnextU
    dsimp [U', V', W']
    omega
  · intro x s ds g dg hs hds hg hdg
    exact eval_sqrtRationalRelation Δ U' V' W' x s dg hs
      (eval_sqrtRationalNext δ Δ U V W x s ds g dg hs hds hg hdg)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic
