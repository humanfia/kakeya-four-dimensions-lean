/- Adapted from this LOT tree, obligation o260, session x0919, commit 57638ddd7c07709143f61bbedd02efd72974929b,
   Submission/Obl/k4_contact_shifted_quadratic_candidates/ShiftedReturn.lean. Original attribution comments are retained below. -/
import Submission.Lib.K4ContactNormalization.ResidualNormalization

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open MvPolynomial
open Submission.Lib.K4ChartLifting

noncomputable section

/-- Return the horizontal quadratic to the original base coordinates while
keeping the arbitrary affine hidden shift in the evaluation point. -/
def shiftedChartPullback (σ : Fin 4 → MvPolynomial (Fin 4) ℝ) (a : ℝ)
    (Q : MvPolynomial (Fin 4) ℝ) : MvPolynomial (Fin 4) ℝ :=
  C a * bind₁ σ Q

theorem shiftedChartPullback_degree (σ : Fin 4 → MvPolynomial (Fin 4) ℝ)
    (hσ : ∀ i, (σ i).totalDegree ≤ 1) (a : ℝ) (Q : MvPolynomial (Fin 4) ℝ) :
    (shiftedChartPullback σ a Q).totalDegree ≤ Q.totalDegree := by
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  exact totalDegree_bind₁_le_of_le_one σ hσ Q

theorem eval_shiftedChartPullback (σ : Fin 4 → MvPolynomial (Fin 4) ℝ)
    (a : ℝ) (Q : MvPolynomial (Fin 4) ℝ) (y : Fin 4 → ℝ) :
    eval y (shiftedChartPullback σ a Q) = a * eval (fun i => eval y (σ i)) Q := by
  rw [shiftedChartPullback, eval_mul, eval_C, eval_bind₁']

/-- Only the normalized hidden coordinate has a hidden derivative. -/
theorem pderiv_shifted_chart (σ : Fin 4 → MvPolynomial (Fin 4) ℝ) (a : ℝ)
    (hσ : ∀ i, pderiv (3 : Fin 4) (σ i) = if i = 3 then C a⁻¹ else 0)
    (Q : MvPolynomial (Fin 4) ℝ) :
    pderiv (3 : Fin 4) (bind₁ σ Q) = C a⁻¹ * bind₁ σ (pderiv 3 Q) := by
  rw [pderiv_bind₁, Finset.sum_eq_single (3 : Fin 4)]
  · rw [hσ, ite_eq_left rfl, mul_comm]
  · intro i _ hi
    rw [hσ, ite_eq_right hi, mul_zero]
  · simp

theorem pderiv_shiftedChartPullback (σ : Fin 4 → MvPolynomial (Fin 4) ℝ)
    {a : ℝ} (ha : a ≠ 0)
    (hσ : ∀ i, pderiv (3 : Fin 4) (σ i) = if i = 3 then C a⁻¹ else 0)
    (Q : MvPolynomial (Fin 4) ℝ) :
    pderiv (3 : Fin 4) (shiftedChartPullback σ a Q) = bind₁ σ (pderiv 3 Q) := by
  rw [shiftedChartPullback, Derivation.leibniz]
  simp only [pderiv_C, smul_eq_mul, mul_zero, add_zero, pderiv_shifted_chart σ a hσ]
  rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]

theorem second_pderiv_shiftedChartPullback (σ : Fin 4 → MvPolynomial (Fin 4) ℝ)
    {a : ℝ} (ha : a ≠ 0)
    (hσ : ∀ i, pderiv (3 : Fin 4) (σ i) = if i = 3 then C a⁻¹ else 0)
    (Q : MvPolynomial (Fin 4) ℝ) :
    pderiv (3 : Fin 4) (pderiv 3 (shiftedChartPullback σ a Q)) =
      C a⁻¹ * bind₁ σ (pderiv 3 (pderiv 3 Q)) := by
  rw [pderiv_shiftedChartPullback σ ha hσ, pderiv_shifted_chart σ a hσ]

/-- The first derivative stays in physical units. In particular, its
observed nondegeneracy floor is unchanged under return. -/
theorem eval_pderiv_shiftedChartPullback (σ : Fin 4 → MvPolynomial (Fin 4) ℝ)
    {a : ℝ} (ha : a ≠ 0)
    (hσ : ∀ i, pderiv (3 : Fin 4) (σ i) = if i = 3 then C a⁻¹ else 0)
    (Q : MvPolynomial (Fin 4) ℝ) (y : Fin 4 → ℝ) :
    eval y (pderiv 3 (shiftedChartPullback σ a Q)) =
      eval (fun i => eval y (σ i)) (pderiv 3 Q) := by
  rw [pderiv_shiftedChartPullback σ ha hσ, eval_bind₁']

theorem eval_second_pderiv_shiftedChartPullback (σ : Fin 4 → MvPolynomial (Fin 4) ℝ)
    {a : ℝ} (ha : a ≠ 0)
    (hσ : ∀ i, pderiv (3 : Fin 4) (σ i) = if i = 3 then C a⁻¹ else 0)
    (Q : MvPolynomial (Fin 4) ℝ) (y : Fin 4 → ℝ) :
    eval y (pderiv 3 (pderiv 3 (shiftedChartPullback σ a Q))) =
      a⁻¹ * eval (fun i => eval y (σ i)) (pderiv 3 (pderiv 3 Q)) := by
  rw [second_pderiv_shiftedChartPullback σ ha hσ, eval_mul, eval_C, eval_bind₁']

/-- Whole-block fitting returns at the product physical width. This theorem
places no bound on the affine shift used to define the points `y t`. -/
theorem shiftedChartPullback_fit (σ : Fin 4 → MvPolynomial (Fin 4) ℝ)
    {a : ℝ} (ha : 0 < a)
    (hσ : ∀ i, pderiv (3 : Fin 4) (σ i) = if i = 3 then C a⁻¹ else 0)
    (Q : MvPolynomial (Fin 4) ℝ) (y : ℝ → Fin 4 → ℝ)
    (I : Set ℝ) (H c : ℝ)
    (hfit : ∀ t ∈ I, |eval (fun i => eval (y t) (σ i)) Q| ≤ H * c ∧
      |eval (fun i => eval (y t) (σ i)) (pderiv 3 Q)| ≤ H ∧
      |eval (fun i => eval (y t) (σ i)) (pderiv 3 (pderiv 3 Q))| ≤ H / c) :
    ∀ t ∈ I, |eval (y t) (shiftedChartPullback σ a Q)| ≤ H * (a * c) ∧
      |eval (y t) (pderiv 3 (shiftedChartPullback σ a Q))| ≤ H ∧
      |eval (y t) (pderiv 3 (pderiv 3 (shiftedChartPullback σ a Q)))| ≤ H / (a * c) := by
  intro t ht
  obtain ⟨hv, hd, hdd⟩ := hfit t ht
  rw [eval_shiftedChartPullback, eval_pderiv_shiftedChartPullback σ ha.ne' hσ,
    eval_second_pderiv_shiftedChartPullback σ ha.ne' hσ]
  refine ⟨?_, hd, ?_⟩
  · rw [abs_mul, abs_of_pos ha]
    convert mul_le_mul_of_nonneg_left hv ha.le using 1
    ring
  · rw [abs_mul, abs_of_pos (inv_pos.mpr ha)]
    convert mul_le_mul_of_nonneg_left hdd (inv_pos.mpr ha).le using 1
    field_simp

/-- This bound depends only on the normalized base substitution and hidden
scale. The arbitrary affine shift is absent. -/
theorem coeff_shiftedChartPullback_le (σ : Fin 4 → MvPolynomial (Fin 4) ℝ)
    {S : ℝ} (hS : 1 ≤ S) (hσ : ∀ i, coeffL1 (σ i) ≤ S)
    (a : ℝ) (Q : MvPolynomial (Fin 4) ℝ) (hQ : Q.totalDegree ≤ 2)
    (e : Fin 4 →₀ ℕ) :
    |(shiftedChartPullback σ a Q).coeff e| ≤ |a| * coeffL1 Q * S ^ 2 := by
  apply (abs_coeff_le_coeffL1 _ _).trans
  apply (coeffL1_C_mul_le _ _).trans
  calc
    _ ≤ |a| * (coeffL1 Q * S ^ Q.totalDegree) :=
      mul_le_mul_of_nonneg_left (coeffL1_bind₁_le σ S hS hσ Q) (abs_nonneg _)
    _ ≤ |a| * (coeffL1 Q * S ^ 2) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hS hQ) (coeffL1_nonneg Q))
        (abs_nonneg _)
    _ = _ := by ring

/-- Fixed powers in normalized coordinates give a fixed power after return,
uniformly in the unbounded affine hidden shift. -/
theorem coeff_shiftedChartPullback_power
    (σ : Fin 4 → MvPolynomial (Fin 4) ℝ) (a N A B C : ℝ)
    (hN : 2 ≤ N) (hB : 0 ≤ B)
    (ha : |a| ≤ N ^ A) (hσ : ∀ i, coeffL1 (σ i) ≤ N ^ B)
    (Q : MvPolynomial (Fin 4) ℝ) (hQ : Q.totalDegree ≤ 2)
    (hcoeff : ∀ e, |Q.coeff e| ≤ N ^ C) (e : Fin 4 →₀ ℕ) :
    |(shiftedChartPullback σ a Q).coeff e| ≤ N ^ (A + C + 2 * B + 7) := by
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hS : 1 ≤ N ^ B := Real.one_le_rpow hN1 hB
  have hnorm : coeffL1 Q ≤ 81 * N ^ C := by
    simpa using coeffL1_le_of_coeff_le Q hQ (N ^ C) hcoeff
  calc
    _ ≤ |a| * coeffL1 Q * (N ^ B) ^ 2 := coeff_shiftedChartPullback_le σ hS hσ a Q hQ e
    _ ≤ N ^ A * (81 * N ^ C) * (N ^ B) ^ 2 := by
      gcongr
      exact coeffL1_nonneg Q
    _ = 81 * N ^ (A + C + 2 * B) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
      rw [mul_left_comm, mul_assoc, ← Real.rpow_add hN0, ← Real.rpow_add hN0]
      congr 1
      ring
    _ ≤ N ^ (7 : ℝ) * N ^ (A + C + 2 * B) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hN0.le _)
      have hpow : (2 : ℝ) ^ (7 : ℕ) ≤ N ^ (7 : ℕ) := pow_le_pow_left₀ (by norm_num) hN 7
      rw [Real.rpow_ofNat]
      norm_num at hpow ⊢
      linarith
    _ = _ := by
      rw [← Real.rpow_add hN0]
      congr 1
      ring

end

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
