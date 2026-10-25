/- Adapted from this LOT tree, o114/x0680 commit133cc8c, Submission/Obl/k4_terminal_representative_atlas/PolynomialLipschitz.lean.
Existing attribution to o156/x0531,x0524,x0575 and accepted imports is retained below. -/

import Mathlib
import Submission.Obl.k4_paired_sheet_discrepancy_matching.PolynomialNorm

/-!
A uniform Lipschitz bound on a fixed complex coefficient box. The constant
only depends on the number of variables, the degree and the box radius.
-/

namespace Submission.Obl.k4_paired_sheet_discrepancy_matching

open Set Metric MvPolynomial

/-- Bounded-degree real polynomials with bounded coefficients have a common
complex Lipschitz bound on every fixed box. -/
theorem exists_complex_lipschitz_from_coefficients (n D : ℕ) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : MvPolynomial (Fin n) ℝ), P.totalDegree ≤ D →
      ∀ A : ℝ, 0 ≤ A → (∀ d, |P.coeff d| ≤ A) →
      ∀ z w : Fin n → ℂ, ‖z‖ ≤ R → ‖w‖ ≤ R →
        ‖eval₂ (algebraMap ℝ ℂ) z P - eval₂ (algebraMap ℝ ℂ) w P‖ ≤
          C * A * ‖z-w‖ := by
  classical
  let Exp := Fin n → Fin (D+1)
  let mon : Exp → (Fin n → ℂ) → ℂ := fun a z => ∏ i : Fin n, z i ^ (a i : ℕ)
  have hex (a : Exp) : ∃ K : NNReal, LipschitzOnWith K (mon a) (closedBall 0 R) := by
    have hdiff : ContDiff ℝ 1 (mon a) := by dsimp [mon]; fun_prop
    exact hdiff.contDiffOn.exists_lipschitzOnWith (by norm_num)
      (convex_closedBall 0 R) (isCompact_closedBall 0 R)
  choose K hK using hex
  let B : ℝ := (∑ a : Exp, (K a : ℝ)) + 1
  have hB : 0 < B := by
    dsimp [B]
    positivity
  have hKB (a : Exp) : (K a : ℝ) ≤ B := by
    have hh : (K a : ℝ) ≤ ∑ a : Exp, (K a : ℝ) :=
      Finset.single_le_sum (fun _ _ => NNReal.coe_nonneg _) (Finset.mem_univ a)
    dsimp [B]
    linarith
  refine ⟨((D+1 : ℕ) : ℝ)^n * B, mul_pos (by positivity) hB, ?_⟩
  intro P hP A hA hcoeff z w hz hw
  have heval (v : Fin n → ℂ) : eval₂ (algebraMap ℝ ℂ) v P =
      ∑ d ∈ P.support, (P.coeff d : ℂ) * d.prod (fun i k => v i ^ k) := by
    conv_lhs => rw [P.as_sum]
    rw [eval₂_sum]
    simp only [eval₂_monomial]
    rfl
  have hmon (d : Fin n →₀ ℕ) (hd : d ∈ P.support) :
      ‖d.prod (fun i k => z i ^ k) - d.prod (fun i k => w i ^ k)‖ ≤ B * ‖z-w‖ := by
    have hcoord (i : Fin n) : d i < D+1 := Nat.lt_succ_of_le
      ((le_degreeOf_of_mem_support i hd).trans ((degreeOf_le_totalDegree P i).trans hP))
    let a : Exp := fun i => ⟨d i, hcoord i⟩
    have hprod (v : Fin n → ℂ) : d.prod (fun i k => v i ^ k) = mon a v := by
      rw [Finsupp.prod_fintype _ _ (by intro i; simp)]
    rw [hprod z, hprod w]
    exact ((hK a).norm_sub_le (mem_closedBall_zero_iff.mpr hz)
      (mem_closedBall_zero_iff.mpr hw)).trans
        (mul_le_mul_of_nonneg_right (hKB a) (norm_nonneg _))
  rw [heval z, heval w, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ d ∈ P.support,
        ‖(P.coeff d : ℂ) * d.prod (fun i k => z i ^ k) -
          (P.coeff d : ℂ) * d.prod (fun i k => w i ^ k)‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ P.support, A * (B * ‖z-w‖) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [← mul_sub, norm_mul, Complex.norm_real]
      exact mul_le_mul (hcoeff d) (hmon d hd) (norm_nonneg _) hA
    _ = (P.support.card : ℝ) * (A * (B * ‖z-w‖)) := by simp [nsmul_eq_mul]
    _ ≤ ((D+1 : ℕ) : ℝ)^n * (A * (B * ‖z-w‖)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_support_le_degree_box n D P hP
    _ = _ := by ring

end Submission.Obl.k4_paired_sheet_discrepancy_matching
