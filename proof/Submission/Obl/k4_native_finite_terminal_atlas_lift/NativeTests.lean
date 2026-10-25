/- Adapted from this LOT tree, o151, session x0508, commit 274d45f,
   Submission/Obl/k4_known_atlas_normalization_composition/NativeTests.lean. Earlier provenance comments are retained. -/
import Submission.Obl.k4_native_finite_terminal_atlas_lift.AffineGeometry
import Submission.Obl.k4_eligibility_sign_description.Families

namespace Submission.Obl.k4_native_finite_terminal_atlas_lift

open MvPolynomial

/-- Inverse base coordinates, with the native hidden coordinate unchanged. -/
noncomputable def inverseBasePolynomials (t₀ q : ℝ) (c u : Spatial) (V : Frame) :
    Fin 4 → MvPolynomial (Fin 4) ℝ :=
  ![C q⁻¹ * (X 0 - C t₀),
    C (V 0 0) * (X 1 - C (c 0) - X 0 * C (u 0)) +
      C (V 0 1) * (X 2 - C (c 1) - X 0 * C (u 1)),
    C (V 1 0) * (X 1 - C (c 0) - X 0 * C (u 0)) +
      C (V 1 1) * (X 2 - C (c 1) - X 0 * C (u 1)),
    X 3]

theorem inverseBasePolynomials_hidden_derivative (t₀ q : ℝ) (c u : Spatial) (V : Frame)
    (i : Fin 4) :
    pderiv (3 : Fin 4) (inverseBasePolynomials t₀ q c u V i) =
      pderiv (3 : Fin 4) (X i : Test) := by
  fin_cases i <;> simp [inverseBasePolynomials, pderiv_mul, pderiv_C, Pi.single_apply]

/-- Affine substitution which fixes the hidden variable and is independent of
it in the other coordinates commutes with native partial differentiation. -/
theorem pderiv_aeval_native (f : Fin 4 → Test)
    (hf : ∀ i, pderiv (3 : Fin 4) (f i) = pderiv (3 : Fin 4) (X i : Test))
    (P : Test) :
    pderiv (3 : Fin 4) (aeval f P) = aeval f (pderiv (3 : Fin 4) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [pderiv_C]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    simp only [map_mul, aeval_X, pderiv_mul, hP, hf, map_add]
    fin_cases i <;> simp [pderiv_X, Pi.single_apply]

/-- Lift a child test with the depth thickness. The native coordinate is not
rescaled, so first and second hidden derivatives acquire the same factor. -/
noncomputable def liftedTest (a t₀ q : ℝ) (c u : Spatial) (V : Frame) (P : Test) : Test :=
  C a * aeval (inverseBasePolynomials t₀ q c u V) P

theorem liftedTest_pderiv (a t₀ q : ℝ) (c u : Spatial) (V : Frame) (P : Test) :
    pderiv (3 : Fin 4) (liftedTest a t₀ q c u V P) =
      liftedTest a t₀ q c u V (pderiv (3 : Fin 4) P) := by
  rw [liftedTest, pderiv_C_mul,
    pderiv_aeval_native _ (inverseBasePolynomials_hidden_derivative t₀ q c u V)]
  rfl

theorem liftedTest_pderiv_pderiv (a t₀ q : ℝ) (c u : Spatial) (V : Frame) (P : Test) :
    pderiv (3 : Fin 4) (pderiv (3 : Fin 4) (liftedTest a t₀ q c u V P)) =
      liftedTest a t₀ q c u V (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P)) := by
  rw [liftedTest_pderiv, liftedTest_pderiv]


theorem inverseBasePolynomials_degree (t₀ q : ℝ) (c u : Spatial) (V : Frame) (i : Fin 4) :
    (inverseBasePolynomials t₀ q c u V i).totalDegree ≤ 1 := by
  have hX (i : Fin 4) : (X i : Test).totalDegree ≤ 1 := by simp
  have hC (a : ℝ) : (C a : Test).totalDegree ≤ 1 := by simp only [totalDegree_C]; omega
  have hm (a : ℝ) (P : Test) (hp : P.totalDegree ≤ 1) : (C a * P).totalDegree ≤ 1 :=
    (Submission.Obl.k4_eligibility_sign_description.degree_C_mul_le a P).trans hp
  have hd (i : Fin 4) (a b : ℝ) :
      (X i - C a - X 0 * C b : Test).totalDegree ≤ 1 := by
    rw [mul_comm (X 0) (C b)]
    exact Submission.Obl.k4_eligibility_sign_description.degree_sub_le
      (Submission.Obl.k4_eligibility_sign_description.degree_sub_le (hX _) (hC _))
      (hm _ _ (hX _))
  fin_cases i <;> dsimp only [inverseBasePolynomials]
  · exact hm _ _ (Submission.Obl.k4_eligibility_sign_description.degree_sub_le (hX _) (hC _))
  · exact Submission.Obl.k4_eligibility_sign_description.degree_add_le
      (hm _ _ (hd _ _ _)) (hm _ _ (hd _ _ _))
  · exact Submission.Obl.k4_eligibility_sign_description.degree_add_le
      (hm _ _ (hd _ _ _)) (hm _ _ (hd _ _ _))
  · exact hX _

theorem liftedTest_degree (a t₀ q : ℝ) (c u : Spatial) (V : Frame) (P : Test) :
    (liftedTest a t₀ q c u V P).totalDegree ≤ P.totalDegree := by
  exact (Submission.Obl.k4_eligibility_sign_description.degree_C_mul_le _ _).trans
    (Submission.Obl.k4_eligibility_sign_description.degree_aeval_le P _
      (inverseBasePolynomials_degree t₀ q c u V))

theorem inverseBasePolynomials_point (t₀ q : ℝ) (hq : q ≠ 0)
    (c u : Spatial) (V : Frame) (l : Trajectory) (τ : ℝ) :
    (fun i => eval (x l (t₀ + q * τ)) (inverseBasePolynomials t₀ q c u V i)) =
      x (normalizedTrajectory t₀ q c u V l) τ := by
  funext i
  fin_cases i <;>
    simp [inverseBasePolynomials, x, normalizedTrajectory, normalizedCoefficients]
  all_goals field_simp [hq] <;> ring

theorem eval_liftedTest (a t₀ q : ℝ) (hq : q ≠ 0)
    (c u : Spatial) (V : Frame) (P : Test) (l : Trajectory) (τ : ℝ) :
    eval (x l (t₀ + q * τ)) (liftedTest a t₀ q c u V P) =
      a * eval (x (normalizedTrajectory t₀ q c u V l) τ) P := by
  simp only [liftedTest, map_mul, eval_C,
    Submission.Obl.k4_eligibility_sign_description.eval_aeval_real,
    inverseBasePolynomials_point t₀ q hq c u V l τ]

end Submission.Obl.k4_native_finite_terminal_atlas_lift
