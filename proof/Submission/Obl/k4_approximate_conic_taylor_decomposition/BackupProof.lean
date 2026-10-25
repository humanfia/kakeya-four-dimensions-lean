import Submission.Obl.k4_approximate_conic_taylor_decomposition.Assembly
import Submission.Obl.k4_approximate_conic_taylor_decomposition.RestoredDirections
import Submission.Obl.k4_approximate_conic_taylor_decomposition.Numerics
import Submission.Obl.k4_approximate_conic_taylor_decomposition.CubicPerturbation
import Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit.ConicTestPerturbation

namespace Submission.Obl.k4_approximate_conic_taylor_decomposition.Backup

open MvPolynomial

/-- The frozen decomposition, assembled through the common restored-test error budget. -/
theorem decomposition : ∃ K : ℕ, 6 ≤ K ∧ ∀ (A ε h : ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) (R : (EuclideanSpace ℝ (Fin 3)) → ℝ) (p : Fin 7 → (EuclideanSpace ℝ (Fin 3))), 2 ≤ A → 0 < ε → ε ≤ 1 → 0 < h → h * A ^ K ≤ ε → M.IsSymm → (A ^ 4)⁻¹ ≤ ∑ i : Fin 3, ∑ j : Fin 3, |M i j| → (∑ i : Fin 3, ∑ j : Fin 3, |M i j|) ≤ A ^ 4 → (∀ i, p i 0 = 1 ∧ ‖p i‖ ≤ A) → (∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k → A⁻¹ ≤ |Matrix.det (Matrix.of fun r t : Fin 3 => (![p i, p j, p k] r) t)|) → (∀ i : Fin 7, |(fun u : (EuclideanSpace ℝ (Fin 3)) => ∑ i : Fin 3, ∑ j : Fin 3, u i * M i j * u j) (p i)| ≤ A * h) → ContDiffOn ℝ 6 R (Metric.ball (0 : (EuclideanSpace ℝ (Fin 3))) 3) → (∀ j : ℕ, j ≤ 6 → ∀ u ∈ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 2, ‖iteratedFDeriv ℝ j R u‖ ≤ A) → (∀ i : Fin 7, ∀ j : ℕ, j ≤ 2 → ∀ u ∈ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 2, ‖iteratedFDeriv ℝ j (fun v : (EuclideanSpace ℝ (Fin 3)) => iteratedFDeriv ℝ 3 R v (fun _ => p i)) u‖ ≤ A * ε) → ∃ (L : (EuclideanSpace ℝ (Fin 3)) →L[ℝ] ℝ) (lam : ℝ), ‖L‖ ≤ A ^ K ∧ |lam| ≤ A ^ K ∧ ∀ u ∈ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 1, |R u - (R 0 + fderiv ℝ R 0 u + iteratedFDeriv ℝ 2 R 0 (fun _ => u) / 2 + (fun u : (EuclideanSpace ℝ (Fin 3)) => ∑ i : Fin 3, ∑ j : Fin 3, u i * M i j * u j) u * L u + lam * ((fun u : (EuclideanSpace ℝ (Fin 3)) => ∑ i : Fin 3, ∑ j : Fin 3, u i * M i j * u j) u) ^ 2)| ≤ A ^ K * ε := by
  obtain ⟨D, hD, hrestore⟩ := conditioned_conic_restoration
  let J : ℕ := 900 + 400 * D
  let d : ℕ := 4 * D
  let K : ℕ := J + d + 40
  refine ⟨K, by dsimp [K, J, d]; omega, ?_⟩
  intro A ε h M R p hA hε hε1 hh hscale hM hlo hup hp htr hq hR hbound htest
  have hA0 : 0 < A := by linarith
  have hA1 : 1 ≤ A := by linarith
  have hAB : A ≤ A ^ 6 := by simpa using pow_le_pow_right₀ hA1 (by norm_num : 1 ≤ 6)
  have hB2 : 2 ≤ A ^ 6 := hA.trans hAB
  have hB1 : 1 ≤ A ^ 6 := hA1.trans hAB
  have hKs : 4 * D + 1 ≤ K := by dsimp [K, J, d]; omega
  have hKt : 4 * D + 22 ≤ K := by dsimp [K, J, d]; omega
  have hsmall : h * A ^ (4 * D + 1) ≤ 1 := by
    have ht := scale_error_mono hA1 hh.le hKs hscale
    exact (by simpa only [mul_comm] using ht : h * A ^ (4 * D + 1) ≤ ε).trans hε1
  obtain ⟨hdet, p', hp', htr'⟩ := hrestore A h hA hh.le p M hp htr hM hlo hup hq hsmall
  let a : Fin 7 → Fin 3 → ℝ := fun i j => p i j
  let b : Fin 7 → Fin 3 → ℝ := fun i j => p' i j
  let Δ : ℝ := A ^ (4 * D + 1) * h
  have hΔ : 0 ≤ Δ := by dsimp [Δ]; positivity
  have ha (i : Fin 7) (j : Fin 3) : |a i j| ≤ A ^ 6 :=
    (abs_apply_le_norm (p i) j).trans ((hp i).2.trans hAB)
  have hb (i : Fin 7) (j : Fin 3) : |b i j| ≤ A ^ 6 :=
    (abs_apply_le_norm (p' i) j).trans (hp' i).2.2.1
  have hab (i : Fin 7) (j : Fin 3) : |b i j - a i j| ≤ Δ := by
    exact (abs_apply_le_norm (p' i - p i) j).trans (hp' i).2.2.2
  have htrb (i j k : Fin 7) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      (A ^ 6)⁻¹ ≤ |Matrix.det (Matrix.of ![b i, b j, b k])| := by
    convert htr' i j k hij hik hjk using 3
    ext r t
    fin_cases r <;> rfl
  have hentry (i j : Fin 3) : |M i j| ≤ A ^ 4 :=
    (Submission.Obl.k4_real_conic_restoration.entry_le_coeff M i j).trans hup
  have hentryB (i j : Fin 3) : |M i j| ≤ (A ^ 6) ^ d := by
    refine (hentry i j).trans ?_
    rw [← pow_mul]
    apply pow_le_pow_right₀ hA1
    dsimp [d]
    omega
  have hdetB : ((A ^ 6) ^ d)⁻¹ ≤ |M.det| := by
    refine le_trans ?_ hdet
    simpa only [one_div] using one_div_le_one_div_of_le (pow_pos hA0 (4 * D)) (by
      rw [← pow_mul]
      apply pow_le_pow_right₀ hA1
      dsimp [d]
      omega)
  have hqzero (i : Fin 7) : eval (b i) (Kit.matrixQuadratic M) = 0 := by
    rw [Kit.eval_matrixQuadratic]
    exact (hp' i).2.1
  have hqne : Kit.matrixQuadratic M ≠ 0 :=
    Kit.matrixQuadratic_ne_zero M hM (abs_pos.mp ((inv_pos.mpr (pow_pos hA0 _)).trans_le hdet))
  have hzero : (0 : E3) ∈ Metric.closedBall (0 : E3) 2 := by simp
  have htests0 := directional_form_tests p hR hzero (fun i j hj => htest i j hj 0 hzero)
  have hcoeff0 (n : ℕ) (hn : n ≤ 5) (m : Fin 3 →₀ ℕ) :
      |(formPoly (iteratedFDeriv ℝ n R 0)).coeff m| ≤ A ^ 9 :=
    coeff_formPoly_iteratedFDeriv_le hA hbound hn hzero m
  have hbudget : 20 * A * ε + 1620 * (A ^ 6) ^ 2 * A ^ 9 * Δ ≤ A ^ 12 * ε := by
    exact restored_test_error_le D K hA hε.le hh.le hKt hscale
  have hbudget3 : A * ε + 81 * (A ^ 6) ^ 2 * A ^ 9 * Δ ≤ A ^ 12 * ε := by
    refine le_trans ?_ hbudget
    gcongr <;> norm_num <;> linarith
  have hbudget4 : (4 * (A * ε)) + 324 * (A ^ 6) ^ 2 * A ^ 9 * Δ ≤ A ^ 12 * ε := by
    refine le_trans ?_ hbudget
    have he : 4 * (A * ε) = 4 * A * ε := by ring
    rw [he]
    gcongr <;> norm_num <;> linarith
  have hmax3 : (A ^ 6) ^ 109 ≤ (A ^ 6) ^ (137 + 16 * d) :=
    pow_le_pow_right₀ hB1 (by omega)
  have hmax4 : (A ^ 6) ^ (137 + 8 * d) ≤ (A ^ 6) ^ (137 + 16 * d) :=
    pow_le_pow_right₀ hB1 (by omega)
  have hkernel : (A ^ 6) ^ (137 + 16 * d) * (A ^ 12 * ε) ≤ A ^ J * ε :=
    restored_kernel_error_le D hA hε.le
  obtain ⟨P, hP, hPerr⟩ := exists_cubic_approximation_near_conic a b (A ^ 6) (A ^ 9) Δ (A * ε)
    hB2 (by positivity) hΔ (by positivity) ha hb hab htrb (Kit.matrixQuadratic M)
    (Kit.matrixQuadratic_isHomogeneous M) hqne hqzero (formPoly (iteratedFDeriv ℝ 3 R 0))
    (formPoly_isHomogeneous _) (hcoeff0 3 (by norm_num)) htests0.1
  have h3 (m : Fin 3 →₀ ℕ) :
      |(formPoly (iteratedFDeriv ℝ 3 R 0) - Kit.matrixQuadratic M * P).coeff m| ≤ A ^ J * ε := by
    refine (hPerr m).trans (le_trans ?_ hkernel)
    exact mul_le_mul hmax3 hbudget3 (by positivity) (by positivity)
  obtain ⟨lam, hlam⟩ := Kit.exists_quartic_approximation_near_conic a b (A ^ 6) (A ^ 9) Δ (4 * (A * ε))
    hB2 (by positivity) hΔ (by positivity) d ha hb hab htrb M hM hentryB hdetB hqzero
    (formPoly (iteratedFDeriv ℝ 4 R 0)) (formPoly_isHomogeneous _)
    (hcoeff0 4 (by norm_num)) htests0.2.1
  have h4 (m : Fin 3 →₀ ℕ) :
      |(formPoly (iteratedFDeriv ℝ 4 R 0) - C lam * (Kit.matrixQuadratic M) ^ 2).coeff m| ≤ A ^ J * ε := by
    refine (hlam m).trans (le_trans ?_ hkernel)
    exact mul_le_mul hmax4 hbudget4 (by positivity) (by positivity)
  have h5 (u : E3) (hu : u ∈ Metric.closedBall (0 : E3) 1) (m : Fin 3 →₀ ℕ) :
      |(formPoly (iteratedFDeriv ℝ 5 R u)).coeff m| ≤ A ^ J * ε := by
    have hu2 := Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) hu
    have htu := directional_form_tests p hR hu2 (fun i j hj => htest i j hj u hu2)
    have hcf := coeff_formPoly_iteratedFDeriv_le hA hbound (by norm_num : 5 ≤ 5) hu2
    have ht := Kit.quintic_coefficients_le_near_conic_tests a b (A ^ 6) (A ^ 9) Δ (20 * (A * ε))
      hB2 (by positivity) hΔ (by positivity) d ha hb hab htrb M hM hentryB hdetB hqzero
      (formPoly (iteratedFDeriv ℝ 5 R u)) (formPoly_isHomogeneous _) hcf htu.2.2 m
    refine ht.trans (le_trans ?_ hkernel)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    convert hbudget using 1 <;> ring
  obtain ⟨hnorm, hlamnorm, happrox⟩ := coefficient_decomposition_bounds J d
    (by dsimp [J]; omega) hA hε.le hε1 M hM hlo hentry
    (by simpa only [d] using hdet) R hR hbound P hP lam h3 h4 h5
  exact ⟨(1 / 6 : ℝ) • polyLinearForm P, lam / 24, hnorm, hlamnorm, happrox⟩

end Submission.Obl.k4_approximate_conic_taylor_decomposition.Backup
