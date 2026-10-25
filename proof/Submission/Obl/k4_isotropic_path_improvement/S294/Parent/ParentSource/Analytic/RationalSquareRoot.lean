-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Analytic.RationalSquareRoot, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Analytic/RationalSquareRoot.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Analytic/RationalSquareRoot.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Analytic/RationalSquareRoot.lean.
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (including x0491 contributions),
-- branch merged/o143/x0487, commit 36234c3602987ce26ddd4bced782149873fbaa4e.
-- Original file: Submission/Obl/k4_isotropic_discovery_of_local_restoration/RationalSquareRoot.lean
-- Earlier source attributions below are retained.
import Mathlib

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic

noncomputable section

open MvPolynomial

def liftBasePolynomial {n : ℕ} (P : MvPolynomial (Fin n) ℂ) :
    MvPolynomial (Fin (n + 1)) ℂ := rename Fin.castSucc P

def hiddenPolynomialMap (n : ℕ) :
    MvPolynomial (Fin (n + 1)) ℂ →+* Polynomial (MvPolynomial (Fin n) ℂ) :=
  eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    (Fin.snoc (fun i : Fin n => Polynomial.C (X i)) Polynomial.X)

lemma hiddenPolynomialMap_lift {n : ℕ} (P : MvPolynomial (Fin n) ℂ) :
    hiddenPolynomialMap n (liftBasePolynomial P) = Polynomial.C P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [liftBasePolynomial, hiddenPolynomialMap]
  | add p q hp hq => simpa only [liftBasePolynomial, map_add] using congrArg₂ (· + ·) hp hq
  | mul_X p i hp =>
    simp only [liftBasePolynomial, map_mul, rename_X] at hp ⊢
    rw [hp]
    simp [hiddenPolynomialMap]

/-- A polynomial equation for `g=(U+V*sqrt(Δ))/W`. Its leading coefficient in
the hidden variable is `W²`, so the equation stays nonzero in degenerate
cases such as `V=0`. -/
def sqrtRationalRelation {n : ℕ} (Δ U V W : MvPolynomial (Fin n) ℂ) :
    MvPolynomial (Fin (n + 1)) ℂ :=
  (liftBasePolynomial W * X (Fin.last n) - liftBasePolynomial U) ^ 2 -
    (liftBasePolynomial V) ^ 2 * liftBasePolynomial Δ

lemma hiddenPolynomialMap_sqrtRationalRelation {n : ℕ}
    (Δ U V W : MvPolynomial (Fin n) ℂ) :
    hiddenPolynomialMap n (sqrtRationalRelation Δ U V W) =
      Polynomial.C (W ^ 2) * Polynomial.X ^ 2 +
      Polynomial.C (-2 * W * U) * Polynomial.X +
      Polynomial.C (U ^ 2 - V ^ 2 * Δ) := by
  simp only [sqrtRationalRelation, map_sub, map_pow, map_mul, hiddenPolynomialMap_lift]
  have hX : hiddenPolynomialMap n (X (Fin.last n)) = Polynomial.X := by
    simp [hiddenPolynomialMap]
  rw [hX]
  simp only [map_neg, map_ofNat]
  ring

theorem sqrtRationalRelation_ne_zero {n : ℕ}
    (Δ U V W : MvPolynomial (Fin n) ℂ) (hW : W ≠ 0) :
    sqrtRationalRelation Δ U V W ≠ 0 := by
  have hcoeff : (hiddenPolynomialMap n (sqrtRationalRelation Δ U V W)).coeff 2 = W ^ 2 := by
    rw [hiddenPolynomialMap_sqrtRationalRelation]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
    norm_num
  intro hzero
  apply pow_ne_zero 2 hW
  have hh := congrArg (fun P => (hiddenPolynomialMap n P).coeff 2) hzero
  simpa only [hcoeff, map_zero, Polynomial.coeff_zero] using hh

theorem sqrtRationalRelation_totalDegree {n : ℕ}
    (Δ U V W : MvPolynomial (Fin n) ℂ) :
    (sqrtRationalRelation Δ U V W).totalDegree ≤
      2 * (Δ.totalDegree + U.totalDegree + V.totalDegree + W.totalDegree + 1) := by
  have hW : (liftBasePolynomial W * X (Fin.last n)).totalDegree ≤ W.totalDegree + 1 :=
    (totalDegree_mul _ _).trans
      (add_le_add (totalDegree_rename_le Fin.castSucc W) (by simp))
  have hWU : (liftBasePolynomial W * X (Fin.last n) - liftBasePolynomial U).totalDegree ≤
      W.totalDegree + U.totalDegree + 1 :=
    (totalDegree_sub _ _).trans (max_le (hW.trans (by omega))
      ((totalDegree_rename_le Fin.castSucc U).trans (by omega)))
  have hleft := (totalDegree_pow
    (liftBasePolynomial W * X (Fin.last n) - liftBasePolynomial U) 2).trans
      (Nat.mul_le_mul_left 2 hWU)
  have hright : ((liftBasePolynomial V) ^ 2 * liftBasePolynomial Δ).totalDegree ≤
      2 * V.totalDegree + Δ.totalDegree :=
    (totalDegree_mul _ _).trans (add_le_add
      ((totalDegree_pow _ 2).trans (Nat.mul_le_mul_left 2
        (totalDegree_rename_le Fin.castSucc V))) (totalDegree_rename_le Fin.castSucc Δ))
  exact (totalDegree_sub _ _).trans (max_le (hleft.trans (by omega))
    (hright.trans (by omega)))

lemma eval_liftBasePolynomial {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (x : Fin n → ℂ) (w : ℂ) :
    eval (Fin.snoc x w) (liftBasePolynomial P) = eval x P := by
  simp [liftBasePolynomial, eval_rename, Function.comp_def]

theorem eval_sqrtRationalRelation {n : ℕ}
    (Δ U V W : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) (s g : ℂ)
    (hs : s ^ 2 = eval x Δ)
    (hg : eval x W * g = eval x U + eval x V * s) :
    eval (Fin.snoc x g) (sqrtRationalRelation Δ U V W) = 0 := by
  simp only [sqrtRationalRelation, map_sub, map_pow, map_mul,
    eval_liftBasePolynomial, eval_X, Fin.snoc_last]
  have he : eval x W * g - eval x U = eval x V * s := by linear_combination hg
  rw [he, mul_pow, hs, sub_self]

/-- Rational expressions in one polynomial square root have a uniform
relation degree. This applies to explicit branch derivatives once their
rational formulas have been established. -/
theorem exists_sqrt_rational_relation {n : ℕ} {Y : Type*}
    (D : ℕ) (Δ U V W : MvPolynomial (Fin n) ℂ) (hW : W ≠ 0)
    (hΔ : Δ.totalDegree ≤ D) (hU : U.totalDegree ≤ D)
    (hV : V.totalDegree ≤ D) (hWd : W.totalDegree ≤ D)
    (Ω : Set Y) (x : Y → Fin n → ℂ) (s g : Y → ℂ)
    (hs : ∀ y ∈ Ω, (s y) ^ 2 = eval (x y) Δ)
    (hg : ∀ y ∈ Ω, eval (x y) W * g y = eval (x y) U + eval (x y) V * s y) :
    ∃ P : MvPolynomial (Fin (n + 1)) ℂ,
      P ≠ 0 ∧ P.totalDegree ≤ 8 * D + 2 ∧
      ∀ y ∈ Ω, eval (Fin.snoc (x y) (g y)) P = 0 := by
  refine ⟨sqrtRationalRelation Δ U V W, sqrtRationalRelation_ne_zero Δ U V W hW,
    (sqrtRationalRelation_totalDegree Δ U V W).trans (by omega), ?_⟩
  exact fun y hy => eval_sqrtRationalRelation Δ U V W (x y) (s y) (g y) (hs y hy) (hg y hy)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic
