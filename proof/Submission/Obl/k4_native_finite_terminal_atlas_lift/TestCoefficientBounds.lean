/- Adapted from this LOT tree, o151, session x0508, commit 274d45f,
   Submission/Obl/k4_known_atlas_normalization_composition/TestCoefficientBounds.lean. Earlier provenance comments are retained. -/
import Submission.Obl.k4_native_finite_terminal_atlas_lift.NativeTests
import Submission.Obl.k4_native_finite_terminal_atlas_lift.PolynomialBounds

namespace Submission.Obl.k4_native_finite_terminal_atlas_lift

open MvPolynomial

theorem coefficientMass_C_mul {n : ℕ} (a : ℝ) (P : MvPolynomial (Fin n) ℝ) :
    coefficientMass (C a * P) ≤ |a| * coefficientMass P := by
  simpa only [coefficientMass_C] using coefficientMass_mul (C a) P

/-- Uniform coefficient control of the inverse affine base map. -/
theorem inverseBasePolynomials_coefficientMass {t₀ q H : ℝ} {c u : Spatial} {V : Frame}
    (hH : 1 ≤ H) (ht : |t₀| ≤ 1) (hq : |q⁻¹| ≤ H)
    (hc : ∀ i, |c i| ≤ H) (hu : ∀ i, |u i| ≤ H) (hV : ∀ i j, |V i j| ≤ H)
    (i : Fin 4) : coefficientMass (inverseBasePolynomials t₀ q c u V i) ≤ 8 * H ^ 2 := by
  have hH0 : 0 ≤ H := le_trans zero_le_one hH
  have hres (i : Fin 4) (a b : ℝ) (ha : |a| ≤ H) (hb : |b| ≤ H) :
      coefficientMass (X i - C a - X 0 * C b : Test) ≤ 1 + 2 * H := by
    calc
      _ ≤ coefficientMass (X i - C a : Test) + coefficientMass (X 0 * C b : Test) :=
        coefficientMass_sub _ _
      _ ≤ (coefficientMass (X i : Test) + coefficientMass (C a : Test)) +
          coefficientMass (X 0 : Test) * coefficientMass (C b : Test) :=
        add_le_add (coefficientMass_sub _ _) (coefficientMass_mul _ _)
      _ ≤ 1 + 2 * H := by
        simp only [coefficientMass_X, coefficientMass_C, one_mul]
        linarith
  have hterm (i : Fin 4) (a b v : ℝ) (ha : |a| ≤ H) (hb : |b| ≤ H) (hv : |v| ≤ H) :
      coefficientMass (C v * (X i - C a - X 0 * C b) : Test) ≤ H * (1 + 2 * H) := by
    exact (coefficientMass_C_mul _ _).trans
      (mul_le_mul hv (hres i a b ha hb) (coefficientMass_nonneg _) hH0)
  fin_cases i <;> dsimp only [inverseBasePolynomials]
  · calc
      _ ≤ |q⁻¹| * coefficientMass (X 0 - C t₀ : Test) := coefficientMass_C_mul _ _
      _ ≤ H * (1 + |t₀|) := by
        apply mul_le_mul hq _ (coefficientMass_nonneg _) hH0
        simpa only [coefficientMass_X, coefficientMass_C] using
          coefficientMass_sub (X 0 : Test) (C t₀)
      _ ≤ 8 * H ^ 2 := by nlinarith
  · exact (coefficientMass_add _ _).trans
      ((add_le_add (hterm 1 _ _ _ (hc 0) (hu 0) (hV 0 0))
        (hterm 2 _ _ _ (hc 1) (hu 1) (hV 0 1))).trans (by nlinarith))
  · exact (coefficientMass_add _ _).trans
      ((add_le_add (hterm 1 _ _ _ (hc 0) (hu 0) (hV 1 0))
        (hterm 2 _ _ _ (hc 1) (hu 1) (hV 1 1))).trans (by nlinarith))
  · change coefficientMass (X 3 : Test) ≤ 8 * H ^ 2
    rw [coefficientMass_X]
    nlinarith

/-- Every coefficient of a lifted quadratic has one fixed polynomial bound.
The constants are independent of subpower tolerance and of the child horizon. -/
theorem liftedTest_coefficient_bound {a t₀ q H H' : ℝ} {c u : Spatial} {V : Frame}
    (P : Test) (hP : P.totalDegree ≤ 2) (hcoeff : ∀ e, |P.coeff e| ≤ H')
    (hH' : 0 ≤ H') (hH : 1 ≤ H) (ha : |a| ≤ 1) (ht : |t₀| ≤ 1) (hq : |q⁻¹| ≤ H)
    (hc : ∀ i, |c i| ≤ H) (hu : ∀ i, |u i| ≤ H) (hV : ∀ i j, |V i j| ≤ H)
    (e : Fin 4 →₀ ℕ) :
    |(liftedTest a t₀ q c u V P).coeff e| ≤ 5184 * H' * H ^ 4 := by
  have hmass : coefficientMass P ≤ 81 * H' := by
    simpa using coefficientMass_le_of_coeff_bound P hP hH' hcoeff
  calc
    _ ≤ coefficientMass (liftedTest a t₀ q c u V P) := abs_coeff_le_coefficientMass _ _
    _ ≤ |a| * coefficientMass (aeval (inverseBasePolynomials t₀ q c u V) P) :=
      coefficientMass_C_mul _ _
    _ ≤ coefficientMass (aeval (inverseBasePolynomials t₀ q c u V) P) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right ha
        (coefficientMass_nonneg (aeval (inverseBasePolynomials t₀ q c u V) P))
    _ ≤ coefficientMass P * (8 * H ^ 2) ^ 2 :=
      coefficientMass_aeval P hP _ (by nlinarith)
        (inverseBasePolynomials_coefficientMass hH ht hq hc hu hV)
    _ ≤ (81 * H') * (8 * H ^ 2) ^ 2 := mul_le_mul_of_nonneg_right hmass (by positivity)
    _ = _ := by ring

end Submission.Obl.k4_native_finite_terminal_atlas_lift
