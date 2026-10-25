import Submission.Obl.k4_dyadic_crop_worlds.Partition
import Submission.Lib.K4XInterface.Charts

/-! Polynomial bounds needed to select normalized world parameters. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_dyadic_crop_worlds

/-- The finite prior format bounds the hidden trajectory even when its native
polynomial test does not bound the hidden coordinate itself. -/
theorem priorFormat_hidden_bound {N B : ℝ} {M D : ℕ}
    {ν : Measure (ℕ × (Fin 6 → ℝ))} (hN : 2 ≤ N)
    (hν : PriorFormat (N ^ M) D ν) (hB : 0 ≤ B) (hBle : B ≤ N ^ M) :
    ∀ᵐ l ∂ν, ∀ t ∈ Icc (0 : ℝ) 1,
      |B * (l.2 2 + t * l.2 5)| ≤ N ^ (2 * M + 1) := by
  have hbox := (measure_eq_zero_iff_ae_notMem).mp (priorFormat_far_null hν)
  filter_upwards [hbox] with l hl t ht
  have hl' : ∀ e, |l.2 e| ≤ N ^ M := by
    intro e
    exact le_of_not_gt (fun he => hl ⟨e, he⟩)
  have ht' : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  have hhidden : |l.2 2 + t * l.2 5| ≤ 2 * N ^ M := by
    calc
      _ ≤ |l.2 2| + |t * l.2 5| := abs_add_le _ _
      _ = |l.2 2| + |t| * |l.2 5| := by rw [abs_mul]
      _ ≤ N ^ M + 1 * N ^ M := by gcongr; exact hl' 2; exact hl' 5
      _ = 2 * N ^ M := by ring
  calc
    _ = B * |l.2 2 + t * l.2 5| := by rw [abs_mul, abs_of_nonneg hB]
    _ ≤ N ^ M * (2 * N ^ M) := mul_le_mul hBle hhidden (abs_nonneg _) (by positivity)
    _ = 2 * N ^ (2 * M) := by rw [show 2 * M = M + M by omega, pow_add]; ring
    _ ≤ N * N ^ (2 * M) := mul_le_mul_of_nonneg_right hN (by positivity)
    _ = N ^ (2 * M + 1) := by rw [pow_succ]; ring

/-- Each matrix entry is bounded by the total absolute-entry sum. -/
theorem entry_abs_le_sum (Q : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2) :
    |Q i j| ≤ ∑ a : Fin 2, ∑ b : Fin 2, |Q a b| := by
  calc
    _ ≤ ∑ b : Fin 2, |Q i b| :=
      Finset.single_le_sum (fun b _ => abs_nonneg (Q i b)) (Finset.mem_univ j)
    _ ≤ _ := Finset.single_le_sum
      (fun a _ => Finset.sum_nonneg (fun b _ => abs_nonneg (Q a b))) (Finset.mem_univ i)

/-- A coarse determinant bound with a convenient universal factor. -/
theorem det_abs_le_two_mul_sq (Q : Matrix (Fin 2) (Fin 2) ℝ) {R : ℝ}
    (hQ : (∑ a : Fin 2, ∑ b : Fin 2, |Q a b|) ≤ R) : |Q.det| ≤ 2 * R ^ 2 := by
  have hentry : ∀ i j, |Q i j| ≤ R := fun i j => (entry_abs_le_sum Q i j).trans hQ
  have hR : 0 ≤ R := (abs_nonneg (Q 0 0)).trans (hentry 0 0)
  calc
    |Q.det| ≤ |Q 0 0 * Q 1 1| + |Q 0 1 * Q 1 0| := by
      rw [Matrix.det_fin_two]
      exact abs_sub _ _
    _ = |Q 0 0| * |Q 1 1| + |Q 0 1| * |Q 1 0| := by rw [abs_mul, abs_mul]
    _ ≤ R * R + R * R := by gcongr <;> apply hentry
    _ = 2 * R ^ 2 := by ring

/-- The full-assignment prior ratio of an invertible chart frame has a fixed
polynomial range, uniformly in its world and sample. -/
theorem frame_prior_ratio_band {N m : ℝ} {M : ℕ}
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (hN : 2 ≤ N) (hQ : Q.det ≠ 0)
    (hentries : (∑ a : Fin 2, ∑ b : Fin 2, (|Q a b| + |Q⁻¹ a b|)) ≤ N ^ M)
    (hm : 0 < m) (hm1 : m ≤ 1) (hminv : m⁻¹ ≤ N ^ M) :
    N ^ (-((3 * M + 1 : ℕ) : ℝ)) ≤ |Q.det| / m ∧
      |Q.det| / m ≤ N ^ (3 * M + 1) := by
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hsumQ : (∑ a : Fin 2, ∑ b : Fin 2, |Q a b|) ≤ N ^ M := by
    refine le_trans ?_ hentries
    exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
      le_add_of_nonneg_right (abs_nonneg _)
  have hsumQi : (∑ a : Fin 2, ∑ b : Fin 2, |Q⁻¹ a b|) ≤ N ^ M := by
    refine le_trans ?_ hentries
    exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
      le_add_of_nonneg_left (abs_nonneg _)
  have hpoly (A : Matrix (Fin 2) (Fin 2) ℝ)
      (hA : (∑ a : Fin 2, ∑ b : Fin 2, |A a b|) ≤ N ^ M) :
      |A.det| ≤ N ^ (2 * M + 1) := by
    calc
      _ ≤ 2 * (N ^ M) ^ 2 := det_abs_le_two_mul_sq A hA
      _ ≤ N * (N ^ M) ^ 2 := mul_le_mul_of_nonneg_right hN (sq_nonneg _)
      _ = N ^ (2 * M + 1) := by rw [← pow_mul, show M * 2 = 2 * M by omega, pow_succ]; ring
  have hJ : 0 < |Q.det| := abs_pos.mpr hQ
  have hJinv : |Q.det|⁻¹ ≤ N ^ (2 * M + 1) := by
    simpa only [Submission.Lib.K4XInterface.det_inv_fin2, abs_inv] using hpoly Q⁻¹ hsumQi
  have hJinv' : |Q.det|⁻¹ ≤ N ^ (3 * M + 1) :=
    hJinv.trans (pow_le_pow_right₀ hN1 (by omega))
  constructor
  · have hlow : (N ^ (3 * M + 1))⁻¹ ≤ |Q.det| := by
      rw [← one_div, div_le_iff₀ (by positivity : (0 : ℝ) < N ^ (3 * M + 1))]
      have h1 := (div_le_iff₀ hJ).mp
        (show 1 / |Q.det| ≤ N ^ (3 * M + 1) by simpa only [one_div] using hJinv')
      nlinarith
    rw [Real.rpow_neg hN0.le, Real.rpow_natCast]
    exact hlow.trans ((le_div_iff₀ hm).mpr (mul_le_of_le_one_right hJ.le hm1))
  · calc
      _ = |Q.det| * m⁻¹ := div_eq_mul_inv _ _
      _ ≤ N ^ (2 * M + 1) * N ^ M := mul_le_mul (hpoly Q hsumQ) hminv
        (inv_nonneg.mpr hm.le) (by positivity)
      _ = N ^ (3 * M + 1) := by rw [← pow_add]; congr 1 <;> omega

end Submission.Obl.k4_native_calibrated_homogeneous_remainder
