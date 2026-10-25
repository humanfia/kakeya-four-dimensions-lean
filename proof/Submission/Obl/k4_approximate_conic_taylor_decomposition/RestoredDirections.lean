/- Adapted from this LOT tree, o144, session x0488, commit 5ed40f2, Submission/Obl/k4_seven_direction_local_degree_restoration/ConicRestore.lean. -/
import Submission.Obl.k4_approximate_conic_taylor_decomposition.Forms
import Submission.Obl.k4_real_conic_restoration

namespace Submission.Obl.k4_approximate_conic_taylor_decomposition.Backup

open Submission.Obl.k4_real_conic_restoration (quad coeff)

/-- The accepted real-conic restoration theorem, with a natural power budget. -/
theorem conic_restoration_nat_exponent :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ (A : ℝ), 2 ≤ A → ∀ (p : Fin 7 → E3)
      (Q : Matrix (Fin 3) (Fin 3) ℝ) (ε : ℝ),
      (∀ i, p i 0 = 1 ∧ ‖p i‖ ≤ A) →
      (∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
        A⁻¹ ≤ |Matrix.det (Matrix.of fun r t : Fin 3 => (![p i, p j, p k] r) t)|) →
      Q.IsSymm → A⁻¹ ≤ coeff Q → coeff Q ≤ A → 0 ≤ ε → ε * A ^ D ≤ 1 →
      (∀ i : Fin 7, |quad Q (fun j => p i j)| ≤ ε) →
      (A ^ D)⁻¹ ≤ |Q.det| ∧ ∃ p' : Fin 7 → E3,
        (∀ i, p' i 0 = 1 ∧ quad Q (fun j => p' i j) = 0 ∧ ‖p' i - p i‖ ≤ A ^ D * ε) ∧
        (∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
          (2 * A)⁻¹ ≤ |Matrix.det (Matrix.of fun r t : Fin 3 => (![p' i, p' j, p' k] r) t)|) := by
  obtain ⟨c, hc, hrestore⟩ := Submission.k4_real_conic_restoration
  obtain ⟨N, hN⟩ := exists_nat_ge c
  refine ⟨N + 1, by omega, ?_⟩
  intro A hA p Q ε hp htr hQ hlo hup hε hsmall htest
  have hA0 : 0 < A := by linarith
  have hA1 : 1 ≤ A := by linarith
  have hNc : c ≤ ((N + 1 : ℕ) : ℝ) := by
    exact hN.trans (by exact_mod_cast Nat.le_succ N)
  have hpow : A ^ c ≤ A ^ (N + 1) := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hA1 hNc
  have hinv : (A ^ (N + 1))⁻¹ ≤ (A ^ c)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (Real.rpow_pos_of_pos hA0 c) hpow
  have hsmall' : ε ≤ A ^ (-c) := by
    rw [Real.rpow_neg hA0.le]
    have ht : ε ≤ 1 / A ^ (N + 1) := (le_div_iff₀ (pow_pos hA0 _)).2 (by simpa using hsmall)
    have ht' : ε ≤ (A ^ (N + 1))⁻¹ := by simpa only [one_div] using ht
    exact ht'.trans hinv
  obtain ⟨hdet, p', hp', htr'⟩ := hrestore A hA p Q ε hp htr hQ hlo hup hε hsmall' htest
  refine ⟨hinv.trans (by simpa only [Real.rpow_neg hA0.le] using hdet), p', ?_, htr'⟩
  intro i
  exact ⟨(hp' i).1, (hp' i).2.1, ((hp' i).2.2).trans (mul_le_mul_of_nonneg_right hpow hε)⟩

/-- Restore a conic with the coefficient normalization produced by `large_normalizedHessian`.
The resulting seven exact zeros satisfy a common power conditioning bound. -/
theorem conditioned_conic_restoration :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ (A h : ℝ), 2 ≤ A → 0 ≤ h →
      ∀ (p : Fin 7 → E3) (Q : Matrix (Fin 3) (Fin 3) ℝ),
      (∀ i, p i 0 = 1 ∧ ‖p i‖ ≤ A) →
      (∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
        A⁻¹ ≤ |Matrix.det (Matrix.of fun r t : Fin 3 => (![p i, p j, p k] r) t)|) →
      Q.IsSymm → (A ^ 4)⁻¹ ≤ coeff Q → coeff Q ≤ A ^ 4 →
      (∀ i : Fin 7, |quad Q (fun j => p i j)| ≤ A * h) → h * A ^ (4 * D + 1) ≤ 1 →
      (A ^ (4 * D))⁻¹ ≤ |Q.det| ∧ ∃ p' : Fin 7 → E3,
        (∀ i, p' i 0 = 1 ∧ quad Q (fun j => p' i j) = 0 ∧
          ‖p' i‖ ≤ A ^ 6 ∧ ‖p' i - p i‖ ≤ A ^ (4 * D + 1) * h) ∧
        (∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
          (A ^ 6)⁻¹ ≤ |Matrix.det (Matrix.of fun r t : Fin 3 => (![p' i, p' j, p' k] r) t)|) := by
  obtain ⟨D, hD, hrestore⟩ := conic_restoration_nat_exponent
  refine ⟨D, hD, ?_⟩
  intro A h hA hh p Q hp htr hQ hlo hup htest hsmall
  have hA0 : 0 < A := by linarith
  have hA1 : 1 ≤ A := by linarith
  have hA4 : A ≤ A ^ 4 := by simpa using pow_le_pow_right₀ hA1 (by norm_num : 1 ≤ 4)
  have hfloor : (A ^ 4)⁻¹ ≤ A⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hA0 hA4
  have hp4 : ∀ i, p i 0 = 1 ∧ ‖p i‖ ≤ A ^ 4 := fun i => ⟨(hp i).1, (hp i).2.trans hA4⟩
  have htr4 : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
      (A ^ 4)⁻¹ ≤ |Matrix.det (Matrix.of fun r t : Fin 3 => (![p i, p j, p k] r) t)| := by
    intro i j k hij hik hjk
    exact hfloor.trans (htr i j k hij hik hjk)
  have he : (A * h) * (A ^ 4) ^ D = h * A ^ (4 * D + 1) := by
    rw [pow_add, pow_one, pow_mul]
    ring
  obtain ⟨hdet, p', hp', htr'⟩ := hrestore (A ^ 4) (hA.trans hA4) p Q (A * h)
    hp4 htr4 hQ hlo hup (mul_nonneg hA0.le hh) (by simpa only [he] using hsmall) htest
  have hshift (i : Fin 7) : ‖p' i - p i‖ ≤ A ^ (4 * D + 1) * h := by
    refine ((hp' i).2.2).trans_eq ?_
    rw [pow_add, pow_one, pow_mul]
    ring
  have h2 : (2 : ℝ) ≤ A ^ 2 := by nlinarith only [hA, sq_nonneg (A - 2)]
  have h2A4 : 2 * A ^ 4 ≤ A ^ 6 := by
    calc 2 * A ^ 4 ≤ A ^ 2 * A ^ 4 := mul_le_mul_of_nonneg_right h2 (pow_nonneg hA0.le _)
         _ = A ^ 6 := by ring
  have hfloor' : (A ^ 6)⁻¹ ≤ (2 * A ^ 4)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (by positivity : 0 < 2 * A ^ 4) h2A4
  refine ⟨by simpa only [← pow_mul] using hdet, p', ?_, ?_⟩
  · intro i
    refine ⟨(hp' i).1, (hp' i).2.1, ?_, hshift i⟩
    have hs1 : ‖p' i - p i‖ ≤ 1 := (hshift i).trans (by nlinarith only [hsmall])
    calc ‖p' i‖ = ‖(p' i - p i) + p i‖ := by congr 1; abel
         _ ≤ ‖p' i - p i‖ + ‖p i‖ := norm_add_le _ _
         _ ≤ 1 + A := add_le_add hs1 (hp i).2
         _ ≤ A ^ 2 := by nlinarith only [hA, sq_nonneg (A - 2)]
         _ ≤ A ^ 6 := pow_le_pow_right₀ hA1 (by norm_num)
  · intro i j k hij hik hjk
    exact hfloor'.trans (htr' i j k hij hik hjk)

end Submission.Obl.k4_approximate_conic_taylor_decomposition.Backup
