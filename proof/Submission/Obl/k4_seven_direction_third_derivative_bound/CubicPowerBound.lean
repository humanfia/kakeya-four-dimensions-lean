/-
Adapted from: here:root
Original proofs by session x0001, root branch x0001-cubiclib, commit f6ada26.
Source: Submission/Lib/K4CubicTests/CubicPowerBound.lean.
This helper has not entered lib; only the cubic two-copy argument is used here.
-/
import Submission.Obl.k4_seven_direction_third_derivative_bound.TensorConditioning

namespace Submission.Obl.k4_seven_direction_third_derivative_bound

private theorem linearMap_abs_le_of_coordinate_tests
    (f : (Fin 3 → ℝ) →ₗ[ℝ] ℝ) (v : Fin 3 → ℝ) (A ε : ℝ) (hA : 0 ≤ A)
    (hv : ∀ i, |v i| ≤ A) (hf : ∀ i, |f (Pi.single i 1)| ≤ ε) : |f v| ≤ 3 * A * ε := by
  classical
  have hexp : v = ∑ i : Fin 3, v i • (Pi.single i 1 : Fin 3 → ℝ) := by
    funext j
    fin_cases j <;> simp [Fin.sum_univ_three, Pi.single_apply]
  have hfexp : f v = ∑ i : Fin 3, v i * f (Pi.single i 1) := by
    calc
      _ = f (∑ i : Fin 3, v i • (Pi.single i 1 : Fin 3 → ℝ)) := congrArg f hexp
      _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]
  rw [hfexp]
  calc
    _ ≤ ∑ i : Fin 3, |v i * f (Pi.single i 1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, A * ε := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul (hv i) (hf i) (abs_nonneg _) hA
    _ = _ := by simp; ring

/-- The cubic two-copy test has a uniform power inverse bound at four
projectively general directions. Coefficients are measured in the standard
basis and no conic hypothesis is needed. -/
theorem cubic_two_copy_coefficients_le_power
    (p : Fin 4 → Fin 3 → ℝ) (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 ≤ ε)
    (hcoord : ∀ i j, |p i j| ≤ A)
    (hp : ∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k →
      A⁻¹ ≤ |Matrix.det (Matrix.of ![p i, p j, p k])|)
    (T : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] ℝ)
    (h01 : ∀ x y z, T x y z = T y x z) (h12 : ∀ x y z, T x y z = T x z y)
    (hsmall : ∀ i : Fin 4, ∀ j : Fin 3, |T (p i) (p i) (Pi.single j 1)| ≤ ε) :
    ∀ i j k : Fin 3, |T (Pi.single i 1) (Pi.single j 1) (Pi.single k 1)| ≤ A ^ 126 * ε := by
  classical
  have hApos : 0 < A := by linarith
  have hA0 : 0 ≤ A := hApos.le
  have hκ : 0 < A⁻¹ := inv_pos.mpr hApos
  have hdet0 : Matrix.det (Matrix.of ![p 0, p 1, p 2]) ≠ 0 :=
    abs_pos.mp (hκ.trans_le (hp 0 1 2 (by decide) (by decide) (by decide)))
  have hlin : LinearIndependent ℝ ![p 0, p 1, p 2] := by
    have h := Matrix.linearIndependent_rows_of_det_ne_zero hdet0
    convert h using 1
    funext i j
    rfl
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ (Fin 3 → ℝ) := by simp
  let b : Module.Basis (Fin 3) ℝ (Fin 3 → ℝ) := basisOfLinearIndependentOfCardEqFinrank hlin hcard
  have hb (i : Fin 3) : b i = ![p 0, p 1, p 2] i :=
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hlin hcard) i
  have hbpoint (i : Fin 3) : b i = p i.castSucc := by
    rw [hb i]
    fin_cases i <;> rfl
  have hbc (i j : Fin 3) : |b i j| ≤ A := by rw [hbpoint i]; exact hcoord _ _
  have hRows : basisRows b = Matrix.of ![p 0, p 1, p 2] := by
    ext i j
    simpa only [basisRows, Matrix.of_apply] using congrFun (hb i) j
  have hdetb : A⁻¹ ≤ |(basisRows b).det| := by
    rw [hRows]
    exact hp 0 1 2 (by decide) (by decide) (by decide)
  have hrep1 : A⁻¹ ≤ |((basisRows b).updateRow 1 (p 3)).det| := by
    have he : (basisRows b).updateRow 1 (p 3) = Matrix.of ![p 0, p 3, p 2] := by
      ext j k
      fin_cases j <;> simp [basisRows, hb, Matrix.updateRow_apply]
    rw [he]
    exact hp 0 3 2 (by decide) (by decide) (by decide)
  have hrep2 : A⁻¹ ≤ |((basisRows b).updateRow 2 (p 3)).det| := by
    have he : (basisRows b).updateRow 2 (p 3) = Matrix.of ![p 0, p 1, p 3] := by
      ext j k
      fin_cases j <;> simp [basisRows, hb, Matrix.updateRow_apply]
    rw [he]
    exact hp 0 1 3 (by decide) (by decide) (by decide)
  have hB (i j : Fin 3) : |T (b i) (b i) (b j)| ≤ 3 * A * ε := by
    apply linearMap_abs_le_of_coordinate_tests (T (b i) (b i)) (b j) A ε hA0 (hbc j)
    intro k
    rw [hbpoint i]
    exact hsmall i.castSucc k
  have hv : |T (p 3) (p 3) (b 0)| ≤ 3 * A * ε :=
    linearMap_abs_le_of_coordinate_tests (T (p 3) (p 3)) (b 0) A ε hA0 (hbc 0) (hsmall 3)
  have hraw := cubic_standard_coefficients_le_of_frame_determinants b T h01 h12 (p 3) A A⁻¹
    (3 * A * ε) hApos hκ (by positivity) hbc (hcoord 3) hdetb hrep1 hrep2 hB hv
  have hC : (90699264 : ℝ) ≤ A ^ 100 :=
    (show (90699264 : ℝ) ≤ 2 ^ 100 by norm_num).trans (pow_le_pow_left₀ (by norm_num) hA 100)
  intro i j k
  calc
    _ ≤ 27 * (6 * A ^ 2 / A⁻¹) ^ 3 * (4 * (6 * A ^ 3 / A⁻¹) ^ 4 * (3 * A * ε)) := hraw i j k
    _ = 90699264 * A ^ 26 * ε := by simp only [div_eq_mul_inv, inv_inv]; ring
    _ ≤ A ^ 100 * A ^ 26 * ε := by gcongr
    _ = _ := by ring

end Submission.Obl.k4_seven_direction_third_derivative_bound
