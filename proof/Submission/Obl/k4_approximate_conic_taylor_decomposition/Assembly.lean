import Submission.Obl.k4_approximate_conic_taylor_decomposition.Norming
import Submission.Obl.k4_approximate_conic_taylor_decomposition.JetTests
import Submission.Obl.k4_approximate_conic_taylor_decomposition.TaylorConic

namespace Submission.Obl.k4_approximate_conic_taylor_decomposition

open MvPolynomial

/-- Uniform coefficient control of a homogeneous form bounds its values on the unit ball. -/
lemma homogeneous_unit_ball_bound {n : ℕ} {F : MvPolynomial (Fin 3) ℝ}
    (hF : F.IsHomogeneous n) {B : ℝ} (hB : 0 ≤ B) (hcoeff : ∀ m, |F.coeff m| ≤ B)
    {u : E3} (hu : u ∈ Metric.closedBall (0 : E3) 1) :
    |eval (fun i => u i) F| ≤ 3 ^ n * B := by
  have hc (i : Fin 3) : |u i| ≤ 1 := (abs_apply_le_norm u i).trans (by simpa using hu)
  simpa using Kit.homogeneous_eval_abs_le 1 (by norm_num) (fun i => u i) hc n F hF B hB hcoeff

/-- Assemble the coefficient estimates for the raw third, fourth and fifth Taylor forms.
The factorial normalization is included in the resulting linear form and scalar. -/
theorem coefficient_decomposition_bounds (J d : ℕ) (hJ : 9 ≤ J)
    {A ε : ℝ} (hA : 2 ≤ A) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (Q : Matrix (Fin 3) (Fin 3) ℝ) (hQ : Q.IsSymm)
    (hlower : (A ^ 4)⁻¹ ≤ ∑ i : Fin 3, ∑ j : Fin 3, |Q i j|)
    (hentry : ∀ i j, |Q i j| ≤ A ^ 4) (hdet : (A ^ d)⁻¹ ≤ |Q.det|)
    (R : E3 → ℝ) (hR : ContDiffOn ℝ 6 R (Metric.ball (0 : E3) 3))
    (hbound : ∀ j : ℕ, j ≤ 6 → ∀ u ∈ Metric.closedBall (0 : E3) 2,
      ‖iteratedFDeriv ℝ j R u‖ ≤ A)
    (P : MvPolynomial (Fin 3) ℝ) (hP : P.IsHomogeneous 1) (lam : ℝ)
    (h3 : ∀ m, |(formPoly (iteratedFDeriv ℝ 3 R 0) - Kit.matrixQuadratic Q * P).coeff m| ≤ A ^ J * ε)
    (h4 : ∀ m, |(formPoly (iteratedFDeriv ℝ 4 R 0) - C lam * (Kit.matrixQuadratic Q) ^ 2).coeff m| ≤ A ^ J * ε)
    (h5 : ∀ u ∈ Metric.closedBall (0 : E3) 1, ∀ m,
      |(formPoly (iteratedFDeriv ℝ 5 R u)).coeff m| ≤ A ^ J * ε) :
    ‖((1 / 6 : ℝ) • polyLinearForm P)‖ ≤ A ^ (J + d + 40) ∧
    |lam / 24| ≤ A ^ (J + d + 40) ∧
    ∀ u ∈ Metric.closedBall (0 : E3) 1,
      |R u - (R 0 + fderiv ℝ R 0 u + iteratedFDeriv ℝ 2 R 0 (fun _ => u) / 2 +
        (∑ i : Fin 3, ∑ j : Fin 3, u i * Q i j * u j) * (((1 / 6 : ℝ) • polyLinearForm P) u) +
        (lam / 24) * (∑ i : Fin 3, ∑ j : Fin 3, u i * Q i j * u j) ^ 2)| ≤
        A ^ (J + d + 40) * ε := by
  have hA0 : 0 < A := by linarith
  have hA1 : 1 ≤ A := by linarith
  have hzero : (0 : E3) ∈ Metric.closedBall (0 : E3) 2 := by simp
  have hcoeff3 := coeff_formPoly_iteratedFDeriv_le hA hbound (by norm_num : 3 ≤ 5) hzero
  have hcoeff4 := coeff_formPoly_iteratedFDeriv_le hA hbound (by norm_num : 4 ≤ 5) hzero
  have hPnorm := polyLinearForm_norm_le_power J d hJ hA hε hε1 Q hQ hentry hdet
    _ P hP hcoeff3 h3
  have hlam := scalar_norm_le_power J hJ hA hε hε1 Q hQ hlower
    _ (formPoly_isHomogeneous _) hcoeff4 h4
  refine ⟨?_, ?_, ?_⟩
  · calc
      ‖((1 / 6 : ℝ) • polyLinearForm P)‖ = (1 / 6 : ℝ) * ‖polyLinearForm P‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 6)]
      _ ≤ ‖polyLinearForm P‖ := mul_le_of_le_one_left (norm_nonneg _) (by norm_num)
      _ ≤ A ^ (J + d + 17) := hPnorm
      _ ≤ A ^ (J + d + 40) := pow_le_pow_right₀ hA1 (by omega)
  · calc
      |lam / 24| = |lam| / 24 := by rw [abs_div]; norm_num
      _ ≤ |lam| := div_le_self (abs_nonneg _) (by norm_num)
      _ ≤ A ^ (J + 29) := hlam
      _ ≤ A ^ (J + d + 40) := pow_le_pow_right₀ hA1 (by omega)
  · let q : E3 → ℝ := fun u => ∑ i : Fin 3, ∑ j : Fin 3, u i * Q i j * u j
    let L : E3 →L[ℝ] ℝ := (1 / 6 : ℝ) • polyLinearForm P
    let B : ℝ := A ^ (J + 8) * ε
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have habsorb (n : ℕ) (hn : n ≤ 5) : (3 : ℝ) ^ n * (A ^ J * ε) ≤ B := by
      calc
        (3 : ℝ) ^ n * (A ^ J * ε) ≤ 3 ^ 5 * (A ^ J * ε) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hn) (by positivity)
        _ ≤ A ^ 8 * (A ^ J * ε) := mul_le_mul_of_nonneg_right (by
          calc (3 : ℝ) ^ 5 ≤ 2 ^ 8 := by norm_num
               _ ≤ A ^ 8 := pow_le_pow_left₀ (by norm_num) hA 8) (by positivity)
        _ = B := by dsimp [B]; ring
    have hthird : ∀ u ∈ Metric.closedBall (0 : E3) 1,
        |iteratedFDeriv ℝ 3 R 0 (fun _ => u) / 6 - q u * L u| ≤ B := by
      intro u hu
      have hhom : (formPoly (iteratedFDeriv ℝ 3 R 0) - Kit.matrixQuadratic Q * P).IsHomogeneous 3 :=
        (formPoly_isHomogeneous _).sub ((Kit.matrixQuadratic_isHomogeneous Q).mul hP)
      have hb := (homogeneous_unit_ball_bound hhom (by positivity) h3 hu).trans
        (habsorb 3 (by norm_num))
      have heq : iteratedFDeriv ℝ 3 R 0 (fun _ => u) / 6 - q u * L u =
          eval (fun i => u i) (formPoly (iteratedFDeriv ℝ 3 R 0) - Kit.matrixQuadratic Q * P) / 6 := by
        simp only [map_sub, map_mul, eval_formPoly, Kit.eval_matrixQuadratic, L, q,
          ContinuousLinearMap.smul_apply, smul_eq_mul, polyLinearForm_apply P hP u]
        ring
      rw [heq, abs_div]
      norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 6)]
      exact (div_le_div_of_nonneg_right hb (by norm_num)).trans (div_le_self hB (by norm_num))
    have hfourth : ∀ u ∈ Metric.closedBall (0 : E3) 1,
        |iteratedFDeriv ℝ 4 R 0 (fun _ => u) / 24 - (lam / 24) * (q u) ^ 2| ≤ B := by
      intro u hu
      have hhom : (formPoly (iteratedFDeriv ℝ 4 R 0) - C lam * (Kit.matrixQuadratic Q) ^ 2).IsHomogeneous 4 :=
        (formPoly_isHomogeneous _).sub (((Kit.matrixQuadratic_isHomogeneous Q).pow 2).C_mul lam)
      have hb := (homogeneous_unit_ball_bound hhom (by positivity) h4 hu).trans
        (habsorb 4 (by norm_num))
      have heq : iteratedFDeriv ℝ 4 R 0 (fun _ => u) / 24 - (lam / 24) * (q u) ^ 2 =
          eval (fun i => u i) (formPoly (iteratedFDeriv ℝ 4 R 0) - C lam * (Kit.matrixQuadratic Q) ^ 2) / 24 := by
        simp only [map_sub, map_mul, map_pow, eval_C, eval_formPoly, Kit.eval_matrixQuadratic, q]
        ring
      rw [heq, abs_div]
      norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 24)]
      exact (div_le_div_of_nonneg_right hb (by norm_num)).trans (div_le_self hB (by norm_num))
    have hfifth : ∀ u ∈ Metric.closedBall (0 : E3) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        |iteratedFDeriv ℝ 5 R (t • u) (fun _ => u)| ≤ B := by
      intro u hu t ht
      have htu : t • u ∈ Metric.closedBall (0 : E3) 1 := by
        simpa using norm_smul_le_one (by simpa using hu) ht
      have hb := (homogeneous_unit_ball_bound (formPoly_isHomogeneous _) (by positivity) (h5 _ htu) hu).trans
        (habsorb 5 le_rfl)
      simpa only [eval_formPoly] using hb
    intro u hu
    have ht := conic_taylor_diagonal_error_le (hR.of_le (by norm_num)) hfifth hthird hfourth hu
    change |R u - (R 0 + fderiv ℝ R 0 u + iteratedFDeriv ℝ 2 R 0 (fun _ => u) / 2 +
      q u * L u + (lam / 24) * (q u) ^ 2)| ≤ _
    refine ht.trans ?_
    calc
      B / 120 + B + B ≤ 4 * B := by linarith
      _ ≤ A ^ 2 * B := mul_le_mul_of_nonneg_right (by nlinarith only [hA, sq_nonneg (A - 2)]) hB
      _ = A ^ (J + 10) * ε := by dsimp [B]; ring
      _ ≤ A ^ (J + d + 40) * ε := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hA1 (by omega)) hε

end Submission.Obl.k4_approximate_conic_taylor_decomposition
