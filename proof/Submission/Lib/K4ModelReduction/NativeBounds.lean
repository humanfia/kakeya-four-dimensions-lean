import Submission.Lib.K4ModelReduction.NativeSmoothing

/-!
Adapted from: here:o009
Original proofs developed for Theorem 2.17 of the supplied Kakeya paper.
 Native version-two bounds for the initial polynomial P = w, B = 1. -/

namespace Submission.Lib.K4ModelReduction

open MeasureTheory Set MvPolynomial

theorem norm_pair_le_two_bound {C a b : ℝ} (hC : 0 ≤ C)
    (ha : |a| ≤ C) (hb : |b| ≤ C) :
    ‖(WithLp.toLp 2 ![a, b] : EuclideanSpace ℝ (Fin 2))‖ ≤ 2 * C := by
  have ha2 : a ^ 2 ≤ C ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg a) ha 2
  have hb2 : b ^ 2 ≤ C ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg b) hb 2
  have hnorm : ‖(WithLp.toLp 2 ![a, b] : EuclideanSpace ℝ (Fin 2))‖ ^ 2 =
      a ^ 2 + b ^ 2 := by simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  nlinarith [norm_nonneg (WithLp.toLp 2 ![a, b] : EuclideanSpace ℝ (Fin 2))]

theorem raw_affine_coordinate_bound {a b C t : ℝ} (ha : |a| ≤ C) (hb : |b| ≤ C)
    (ht : t ∈ Icc (0 : ℝ) 1) : |a + t * b| ≤ 2 * C := by
  have htAbs : |t| ≤ 1 := by simpa only [abs_of_nonneg ht.1] using ht.2
  have hmul : |t * b| ≤ C := by
    rw [abs_mul]
    exact (mul_le_mul htAbs hb (abs_nonneg b) zero_le_one).trans_eq (one_mul C)
  exact (abs_add_le a (t * b)).trans (by linarith)

theorem raw_initial_native_estimates (l : ℕ × (Fin 6 → ℝ)) {C : ℝ}
    (hC : 0 ≤ C) (hl : ∀ j, |l.2 j| ≤ C) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖(WithLp.toLp 2 ![l.2 0 + t * l.2 3, l.2 1 + t * l.2 4] : EuclideanSpace ℝ (Fin 2))‖ +
        ‖(WithLp.toLp 2 ![l.2 3, l.2 4] : EuclideanSpace ℝ (Fin 2))‖ ≤ 6 * C ∧
      |MvPolynomial.eval (fun j => rawGraphPoint l t j) (X (3 : Fin 4))| ≤ 2 * C ∧
      MvPolynomial.eval (fun j => rawGraphPoint l t j) (pderiv (3 : Fin 4) (X 3)) = 1 ∧
      MvPolynomial.eval (fun j => rawGraphPoint l t j) (pderiv (3 : Fin 4) (pderiv 3 (X 3))) = 0 := by
  have h0 := raw_affine_coordinate_bound (hl 0) (hl 3) ht
  have h1 := raw_affine_coordinate_bound (hl 1) (hl 4) ht
  have h2 := raw_affine_coordinate_bound (hl 2) (hl 5) ht
  have hbase := norm_pair_le_two_bound (by positivity : 0 ≤ 2 * C) h0 h1
  have hslope := norm_pair_le_two_bound hC (hl 3) (hl 4)
  refine ⟨by linarith, ?_, ?_, ?_⟩
  · rw [eval_X]
    exact h2
  · simp
  · simp

theorem raw_initial_native_bounds (l : ℕ × (Fin 6 → ℝ)) {C K : ℝ}
    (hC : 0 ≤ C) (hK : 1 ≤ K) (hCK : 6 * C ≤ K) (hl : ∀ j, |l.2 j| ≤ C)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖(WithLp.toLp 2 ![l.2 0 + t * l.2 3, l.2 1 + t * l.2 4] : EuclideanSpace ℝ (Fin 2))‖ +
        ‖(WithLp.toLp 2 ![l.2 3, l.2 4] : EuclideanSpace ℝ (Fin 2))‖ ≤ K ∧
      |MvPolynomial.eval (fun j => rawGraphPoint l t j) (X (3 : Fin 4))| ≤ K ∧
      |MvPolynomial.eval (fun j => rawGraphPoint l t j) (pderiv (3 : Fin 4) (X 3))| ≤ K ∧
      |MvPolynomial.eval (fun j => rawGraphPoint l t j) (pderiv (3 : Fin 4) (pderiv 3 (X 3)))| ≤ K ∧
      K⁻¹ ≤ |MvPolynomial.eval (fun j => rawGraphPoint l t j) (pderiv (3 : Fin 4) (X 3))| := by
  obtain ⟨hnorm, hval, hd1, hd2⟩ := raw_initial_native_estimates l hC hl t ht
  rw [hd1, hd2]
  simp only [abs_one, abs_zero]
  have hpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hinv := mul_le_mul_of_nonneg_right hK (inv_nonneg.mpr hpos.le)
  rw [one_mul, mul_inv_cancel₀ hpos.ne'] at hinv
  exact ⟨hnorm.trans hCK, by linarith, hK, hpos.le, hinv⟩

end Submission.Lib.K4ModelReduction
