-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Analytic/RationalQuadratic.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Analytic/RationalQuadratic.lean.
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (including x0491 contributions),
-- branch merged/o143/x0487, commit 36234c3602987ce26ddd4bced782149873fbaa4e.
-- Original file: Submission/Obl/k4_isotropic_discovery_of_local_restoration/RationalQuadratic.lean
-- Earlier source attributions below are retained.
import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.RationalSquareRoot

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open MvPolynomial

/-- A quadratic test evaluated on a rational square-root expression stays in
the same quadratic extension, including an arbitrary scalar normalization. -/
theorem rational_sqrt_quadratic_identity {R : Type*} [CommRing R]
    (Δ U V W A B C₀ lam s g q : R)
    (hs : s ^ 2 = Δ) (hg : W * g = U + V * s)
    (hq : lam * q = A * g ^ 2 + B * g + C₀) :
    (lam * W ^ 2) * q =
      A * (U ^ 2 + V ^ 2 * Δ) + B * U * W + C₀ * W ^ 2 +
        (2 * A * U * V + B * V * W) * s := by
  linear_combination (W ^ 2) * hq +
    (A * (W * g + U + V * s) + B * W) * hg + (A * V ^ 2) * hs

def sqrtRationalQuadraticU {n : ℕ} (Δ U V W A B C₀ : MvPolynomial (Fin n) ℂ) :
    MvPolynomial (Fin n) ℂ :=
  A * (U ^ 2 + V ^ 2 * Δ) + B * U * W + C₀ * W ^ 2

def sqrtRationalQuadraticV {n : ℕ} (U V W A B : MvPolynomial (Fin n) ℂ) :
    MvPolynomial (Fin n) ℂ := C 2 * A * U * V + B * V * W

def sqrtRationalQuadraticW {n : ℕ} (lam : ℂ) (W : MvPolynomial (Fin n) ℂ) :
    MvPolynomial (Fin n) ℂ := C lam * W ^ 2

theorem sqrtRationalQuadraticW_ne_zero {n : ℕ} (lam : ℂ)
    (W : MvPolynomial (Fin n) ℂ) (hlam : lam ≠ 0) (hW : W ≠ 0) :
    sqrtRationalQuadraticW lam W ≠ 0 := by
  exact mul_ne_zero (by simpa using hlam) (pow_ne_zero 2 hW)

theorem sqrtRationalQuadratic_degrees {n : ℕ} (D : ℕ)
    (Δ U V W A B C₀ : MvPolynomial (Fin n) ℂ) (lam : ℂ)
    (hΔ : Δ.totalDegree ≤ D) (hU : U.totalDegree ≤ D)
    (hV : V.totalDegree ≤ D) (hW : W.totalDegree ≤ D)
    (hA : A.totalDegree ≤ D) (hB : B.totalDegree ≤ D) (hC : C₀.totalDegree ≤ D) :
    (sqrtRationalQuadraticU Δ U V W A B C₀).totalDegree ≤ 4 * D ∧
      (sqrtRationalQuadraticV U V W A B).totalDegree ≤ 4 * D ∧
      (sqrtRationalQuadraticW lam W).totalDegree ≤ 4 * D := by
  have hU2 := (totalDegree_pow U 2).trans (Nat.mul_le_mul_left 2 hU)
  have hV2 := (totalDegree_pow V 2).trans (Nat.mul_le_mul_left 2 hV)
  have hW2 := (totalDegree_pow W 2).trans (Nat.mul_le_mul_left 2 hW)
  have hrad : (V ^ 2 * Δ).totalDegree ≤ 3 * D :=
    (totalDegree_mul _ _).trans ((add_le_add hV2 hΔ).trans (by omega))
  have hsum : (U ^ 2 + V ^ 2 * Δ).totalDegree ≤ 3 * D :=
    (totalDegree_add _ _).trans (max_le (hU2.trans (by omega)) hrad)
  have hprod3 (P Q S : MvPolynomial (Fin n) ℂ)
      (hP : P.totalDegree ≤ D) (hQ : Q.totalDegree ≤ D) (hS : S.totalDegree ≤ D) :
      (P * Q * S).totalDegree ≤ 3 * D :=
    (totalDegree_mul _ _).trans ((add_le_add
      ((totalDegree_mul _ _).trans (add_le_add hP hQ)) hS).trans (by omega))
  have hlead : (A * (U ^ 2 + V ^ 2 * Δ)).totalDegree ≤ 4 * D :=
    (totalDegree_mul _ _).trans ((add_le_add hA hsum).trans (by omega))
  have hBterm := hprod3 B U W hB hU hW
  have hCterm : (C₀ * W ^ 2).totalDegree ≤ 3 * D :=
    (totalDegree_mul _ _).trans ((add_le_add hC hW2).trans (by omega))
  have h2A : (C 2 * A).totalDegree ≤ D := by
    apply (totalDegree_mul _ _).trans
    simpa only [totalDegree_C, zero_add] using hA
  refine ⟨?_, ?_, ?_⟩
  · exact (totalDegree_add _ _).trans (max_le
      ((totalDegree_add _ _).trans (max_le hlead (hBterm.trans (by omega))))
      (hCterm.trans (by omega)))
  · exact (totalDegree_add _ _).trans (max_le
      ((hprod3 (C 2 * A) U V h2A hU hV).trans (by omega))
      ((hprod3 B V W hB hV hW).trans (by omega)))
  · apply (totalDegree_mul _ _).trans
    simpa only [totalDegree_C, zero_add] using hW2.trans (by omega : 2 * D ≤ 4 * D)

theorem eval_sqrtRationalQuadratic {n : ℕ}
    (Δ U V W A B C₀ : MvPolynomial (Fin n) ℂ) (lam : ℂ)
    (x : Fin n → ℂ) (s g q : ℂ)
    (hs : s ^ 2 = eval x Δ) (hg : eval x W * g = eval x U + eval x V * s)
    (hq : lam * q = eval x A * g ^ 2 + eval x B * g + eval x C₀) :
    eval x (sqrtRationalQuadraticW lam W) * q =
      eval x (sqrtRationalQuadraticU Δ U V W A B C₀) +
        eval x (sqrtRationalQuadraticV U V W A B) * s := by
  simp only [sqrtRationalQuadraticW, sqrtRationalQuadraticU, sqrtRationalQuadraticV,
    map_add, map_mul, map_pow, eval_C]
  exact rational_sqrt_quadratic_identity _ _ _ _ _ _ _ _ _ _ _ hs hg hq

/-- A normalized quadratic residual on the branch has a nonzero relation
whose degree is uniform over all coefficients and all evaluation points. -/
theorem exists_rational_quadratic_relation {n : ℕ} (D : ℕ)
    (Δ U V W A B C₀ : MvPolynomial (Fin n) ℂ) (lam : ℂ)
    (hΔ : Δ.totalDegree ≤ D) (hU : U.totalDegree ≤ D)
    (hV : V.totalDegree ≤ D) (hW : W.totalDegree ≤ D)
    (hA : A.totalDegree ≤ D) (hB : B.totalDegree ≤ D) (hC : C₀.totalDegree ≤ D)
    (hlam : lam ≠ 0) (hWne : W ≠ 0) :
    ∃ P : MvPolynomial (Fin (n + 1)) ℂ, P ≠ 0 ∧ P.totalDegree ≤ 32 * D + 2 ∧
      ∀ (x : Fin n → ℂ) (s g q : ℂ), s ^ 2 = eval x Δ →
        eval x W * g = eval x U + eval x V * s →
        lam * q = eval x A * g ^ 2 + eval x B * g + eval x C₀ →
        eval (Fin.snoc x q) P = 0 := by
  obtain ⟨hnextU, hnextV, hnextW⟩ :=
    sqrtRationalQuadratic_degrees D Δ U V W A B C₀ lam hΔ hU hV hW hA hB hC
  let U' := sqrtRationalQuadraticU Δ U V W A B C₀
  let V' := sqrtRationalQuadraticV U V W A B
  let W' := sqrtRationalQuadraticW lam W
  refine ⟨sqrtRationalRelation Δ U' V' W',
    sqrtRationalRelation_ne_zero Δ U' V' W' (sqrtRationalQuadraticW_ne_zero lam W hlam hWne),
    (sqrtRationalRelation_totalDegree Δ U' V' W').trans ?_, ?_⟩
  · dsimp [U', V', W']
    omega
  · intro x s g q hs hg hq
    exact eval_sqrtRationalRelation Δ U' V' W' x s q hs
      (eval_sqrtRationalQuadratic Δ U V W A B C₀ lam x s g q hs hg hq)

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
