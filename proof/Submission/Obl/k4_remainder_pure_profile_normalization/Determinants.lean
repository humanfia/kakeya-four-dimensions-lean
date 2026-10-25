import Mathlib
import Submission.Obl.k4_matching_endpoint_volume.MatrixEstimates

namespace Submission.Obl.k4_remainder_pure_profile_normalization

/-- Polynomial bounds on a frame and its inverse control its Jacobian in both
 directions, with constants depending only on the fixed format exponent. -/
theorem determinant_bounds {N : ℝ} {M : ℕ} (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (hN : 2 ≤ N) (hQ : Q.det ≠ 0)
    (hsize : (∑ i : Fin 2, ∑ j : Fin 2, (|Q i j| + |Q⁻¹ i j|)) ≤ N ^ M) :
    N ^ (-((2 * M + 1 : ℕ) : ℝ)) ≤ |Q.det| ∧ |Q.det| ≤ N ^ (2 * M + 1) := by
  have hN0 : 0 < N := by linarith
  have hentry (i j : Fin 2) : |Q i j| + |Q⁻¹ i j| ≤ N ^ M := by
    calc
      _ ≤ ∑ j' : Fin 2, (|Q i j'| + |Q⁻¹ i j'|) :=
        Finset.single_le_sum (fun _ _ => by positivity) (Finset.mem_univ j)
      _ ≤ ∑ i' : Fin 2, ∑ j' : Fin 2, (|Q i' j'| + |Q⁻¹ i' j'|) :=
        Finset.single_le_sum (f := fun i' : Fin 2 =>
          ∑ j' : Fin 2, (|Q i' j'| + |Q⁻¹ i' j'|))
          (fun _ _ => by positivity) (Finset.mem_univ i)
      _ ≤ _ := hsize
  have upper (A : Matrix (Fin 2) (Fin 2) ℝ) (he : ∀ i j, |A i j| ≤ N ^ M) :
      |A.det| ≤ N ^ (2 * M + 1) := by
    have hd := Submission.Obl.k4_matching_endpoint_volume.abs_det_le_factorial_mul_pow
      A (show 0 ≤ N ^ M by positivity) he
    norm_num at hd
    refine hd.trans ?_
    calc
      2 * (N ^ M) ^ 2 ≤ N * (N ^ M) ^ 2 := by gcongr
      _ = N ^ (2 * M + 1) := by rw [← pow_mul, Nat.mul_comm M 2, pow_succ, mul_comm]
  have hupper : |Q.det| ≤ N ^ (2 * M + 1) := upper Q (fun i j => by
    linarith [hentry i j, abs_nonneg (Q⁻¹ i j)])
  have hinv : |Q.det|⁻¹ ≤ N ^ (2 * M + 1) := by
    simpa only [Matrix.det_nonsing_inv, Ring.inverse_eq_inv, abs_inv] using
      upper Q⁻¹ (fun i j => by linarith [hentry i j, abs_nonneg (Q i j)])
  refine ⟨?_, hupper⟩
  rw [Real.rpow_neg hN0.le, Real.rpow_natCast]
  rw [inv_le_iff_one_le_mul₀ (pow_pos hN0 _)]
  simpa only [mul_comm] using (inv_le_iff_one_le_mul₀ (abs_pos.mpr hQ)).mp hinv

/-- Assignment masses bounded below by a fixed reciprocal polynomial keep the
Jacobian-to-prior ratio in a fixed logarithmic compact interval. -/
theorem jacobian_prior_ratio_bounds {N a : ℝ} {M A : ℕ}
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (hN : 2 ≤ N) (hQ : Q.det ≠ 0)
    (hsize : (∑ i : Fin 2, ∑ j : Fin 2, (|Q i j| + |Q⁻¹ i j|)) ≤ N ^ M)
    (ha : 0 < a) (ha1 : a ≤ 1) (hal : (N ^ A)⁻¹ ≤ a) :
    N ^ (-((2 * M + 1 : ℕ) : ℝ)) ≤ |Q.det| / a ∧
      |Q.det| / a ≤ N ^ (2 * M + 1 + A) := by
  have hN0 : 0 < N := by linarith
  obtain ⟨hlo, hhi⟩ := determinant_bounds Q hN hQ hsize
  constructor
  · refine hlo.trans ?_
    apply (le_div_iff₀ ha).mpr
    exact mul_le_of_le_one_right (abs_nonneg _) ha1
  · have hai : a⁻¹ ≤ N ^ A := by
      simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr (pow_pos hN0 A)) hal
    calc
      |Q.det| / a = |Q.det| * a⁻¹ := div_eq_mul_inv _ _
      _ ≤ N ^ (2 * M + 1) * N ^ A := mul_le_mul hhi hai (by positivity) (by positivity)
      _ = _ := (pow_add _ _ _).symm

end Submission.Obl.k4_remainder_pure_profile_normalization
