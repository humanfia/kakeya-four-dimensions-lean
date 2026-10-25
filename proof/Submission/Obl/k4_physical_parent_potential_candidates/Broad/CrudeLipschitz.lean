-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/CrudeLipschitz.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
import Submission.Lib.K4QuadraticSheetCore.PolyBounds

/-!
# Crude Lipschitz bounds for polynomials on boxes

On the box `|xᵢ| ≤ Bx` with `Bx ≥ 1`, a real polynomial `Q` of total degree `D` satisfies
`|Q x - Q y| ≤ D · ‖Q‖₁ · Bx^D · Σ |xᵢ - yᵢ|`, where `‖Q‖₁` is the coefficient `ℓ¹` norm.  This
is the scaled form of lib's `K4QuadraticSheetCore.abs_eval_sub_eval_le` (the case `Bx = 1`).
In the broad completion it controls the variation of `R_b - P` across a base cell of tiny
side, so that every incidence in a fine observation cell has nearly the same own intercept.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Broad

open MvPolynomial
open Submission.Lib.K4ChartLifting
open Submission.Lib.K4QuadraticSheetCore

noncomputable section

variable {n : ℕ}

/-- Monomials on a box: the scaled product bound. -/
lemma abs_monomial_sub_le_scaled (d : Fin n →₀ ℕ) {Bx : ℝ} (hB : 1 ≤ Bx) (x y : Fin n → ℝ)
    (hx : ∀ i, |x i| ≤ Bx) (hy : ∀ i, |y i| ≤ Bx) :
    |∏ i, x i ^ d i - ∏ i, y i ^ d i| ≤
      Bx ^ (∑ i, d i) * ∑ i, (d i : ℝ) * |x i / Bx - y i / Bx| := by
  have hB0 : 0 < Bx := lt_of_lt_of_le one_pos hB
  have hu : ∀ i, |x i / Bx| ≤ 1 := fun i => by
    rw [abs_div, abs_of_pos hB0, div_le_one hB0]; exact hx i
  have hv : ∀ i, |y i / Bx| ≤ 1 := fun i => by
    rw [abs_div, abs_of_pos hB0, div_le_one hB0]; exact hy i
  have hxs : ∀ i, x i = Bx * (x i / Bx) := fun i => by field_simp
  have hys : ∀ i, y i = Bx * (y i / Bx) := fun i => by field_simp
  have hpx : ∏ i, x i ^ d i = Bx ^ (∑ i, d i) * ∏ i, (x i / Bx) ^ d i := by
    conv_lhs => arg 2; ext i; rw [hxs i, mul_pow]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hpy : ∏ i, y i ^ d i = Bx ^ (∑ i, d i) * ∏ i, (y i / Bx) ^ d i := by
    conv_lhs => arg 2; ext i; rw [hys i, mul_pow]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [hpx, hpy, ← mul_sub, abs_mul, abs_of_pos (by positivity)]
  gcongr
  calc |∏ i, (x i / Bx) ^ d i - ∏ i, (y i / Bx) ^ d i|
      ≤ ∑ i, |(x i / Bx) ^ d i - (y i / Bx) ^ d i| :=
        abs_prod_sub_prod_le _ _ _
          (fun i _ => by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (hu i))
          (fun i _ => by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (hv i))
    _ ≤ ∑ i, (d i : ℝ) * |x i / Bx - y i / Bx| :=
        Finset.sum_le_sum fun i _ => abs_pow_sub_pow_le _ _ (hu i) (hv i) _

/-- **Crude Lipschitz bound on a box.** -/
theorem abs_eval_sub_eval_le_box (Q : MvPolynomial (Fin n) ℝ) {Bx : ℝ} (hB : 1 ≤ Bx)
    (x y : Fin n → ℝ) (hx : ∀ i, |x i| ≤ Bx) (hy : ∀ i, |y i| ≤ Bx) :
    |MvPolynomial.eval x Q - MvPolynomial.eval y Q| ≤
      Q.totalDegree * coeffL1 Q * Bx ^ Q.totalDegree * ∑ i, |x i - y i| := by
  have hB0 : 0 < Bx := lt_of_lt_of_le one_pos hB
  rw [eval_eq', eval_eq', ← Finset.sum_sub_distrib]
  have hS : 0 ≤ ∑ i, |x i - y i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  calc |∑ d ∈ Q.support, (Q.coeff d * ∏ i, x i ^ d i - Q.coeff d * ∏ i, y i ^ d i)|
      ≤ ∑ d ∈ Q.support, |Q.coeff d * ∏ i, x i ^ d i - Q.coeff d * ∏ i, y i ^ d i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Q.support, |Q.coeff d| *
          ((Q.totalDegree : ℝ) * Bx ^ Q.totalDegree * ∑ i, |x i - y i|) := by
        apply Finset.sum_le_sum
        intro d hd
        rw [← mul_sub, abs_mul]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        have hdeg : (∑ i, d i) ≤ Q.totalDegree := by
          have := le_totalDegree hd
          simpa [Finsupp.sum_fintype, Finsupp.degree] using this
        refine (abs_monomial_sub_le_scaled d hB x y hx hy).trans ?_
        have hsum : ∑ i, (d i : ℝ) * |x i / Bx - y i / Bx| ≤
            (Q.totalDegree : ℝ) * (∑ i, |x i - y i|) / Bx := by
          rw [Finset.mul_sum, Finset.sum_div]
          apply Finset.sum_le_sum
          intro i _
          rw [← sub_div, abs_div, abs_of_pos hB0, mul_div_assoc]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast monomial_degree_le hd i
        calc Bx ^ (∑ i, d i) * ∑ i, (d i : ℝ) * |x i / Bx - y i / Bx|
            ≤ Bx ^ (∑ i, d i) * ((Q.totalDegree : ℝ) * (∑ i, |x i - y i|) / Bx) := by
              gcongr
          _ ≤ Bx ^ Q.totalDegree * ((Q.totalDegree : ℝ) * (∑ i, |x i - y i|) / Bx) := by
              gcongr
          _ ≤ Bx ^ Q.totalDegree * ((Q.totalDegree : ℝ) * (∑ i, |x i - y i|)) := by
              gcongr
              exact div_le_self (by positivity) hB
          _ = (Q.totalDegree : ℝ) * Bx ^ Q.totalDegree * ∑ i, |x i - y i| := by ring
    _ = Q.totalDegree * coeffL1 Q * Bx ^ Q.totalDegree * ∑ i, |x i - y i| := by
        rw [← Finset.sum_mul]; unfold coeffL1; ring

end

end Submission.Obl.k4_physical_parent_potential_candidates.Broad
