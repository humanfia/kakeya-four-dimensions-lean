import Submission.Obl.k4_eligibility_sign_description.Signs

namespace Submission.Obl.k4_stable_native_signal_oscillation
open MvPolynomial Set Metric MeasureTheory

noncomputable def dilatePolynomial (r : ℝ) (P : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial (Fin 3) ℝ := aeval (fun i => C r * X i) P

lemma dilatePolynomial_degree (r : ℝ) (P : MvPolynomial (Fin 3) ℝ) :
    (dilatePolynomial r P).totalDegree ≤ P.totalDegree := by
  apply Submission.Obl.k4_eligibility_sign_description.degree_aeval_le
  intro i
  simpa using totalDegree_mul (C r : MvPolynomial (Fin 3) ℝ) (X i)

lemma eval_dilatePolynomial (r : ℝ) (P : MvPolynomial (Fin 3) ℝ) (x : Fin 3 → ℝ) :
    eval x (dilatePolynomial r P) = eval (fun i => r * x i) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [dilatePolynomial]
  | add P Q hP hQ => simpa only [dilatePolynomial, map_add] using congrArg₂ (· + ·) hP hQ
  | mul_X P i hP => simpa only [dilatePolynomial, map_mul, aeval_X, eval_C, eval_X] using congrArg₂ (· * ·) hP (Eq.refl (r * x i))

lemma continuous_real_polynomial (P : MvPolynomial (Fin 3) ℝ) :
    Continuous (fun x : EuclideanSpace ℝ (Fin 3) => eval (fun i => x i) P) :=
  (MvPolynomial.continuous_eval P).comp (by fun_prop)

lemma normalized_witness_mass (K : ℝ) (hK : 0 < K)
    (P : MvPolynomial (Fin 3) ℝ) (E : Set (EuclideanSpace ℝ (Fin 3))) (V : ℝ)
    (hE : E ⊆ closedBall 0 K) (hmass : ENNReal.ofReal K⁻¹ ≤ volume E)
    (hbound : ∀ x ∈ E, |eval (fun i => x i) P| ≤ V) :
    ENNReal.ofReal ((8 * K ^ 4)⁻¹) ≤
      volume {x : EuclideanSpace ℝ (Fin 3) | ‖x‖ ≤ 1 / 2 ∧
        |eval (fun i => x i) (dilatePolynomial (2 * K) P)| ≤ V} := by
  have hsub : (fun x : EuclideanSpace ℝ (Fin 3) => (2 * K) • x) ⁻¹' E ⊆
      {x : EuclideanSpace ℝ (Fin 3) | ‖x‖ ≤ 1 / 2 ∧
        |eval (fun i => x i) (dilatePolynomial (2 * K) P)| ≤ V} := by
    intro x hx
    have hnorm : ‖(2 * K) • x‖ ≤ K := mem_closedBall_zero_iff.mp (hE hx)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * K)] at hnorm
    refine ⟨by nlinarith, ?_⟩
    simpa only [eval_dilatePolynomial, PiLp.smul_apply, smul_eq_mul] using hbound ((2 * K) • x) hx
  calc
    ENNReal.ofReal ((8 * K ^ 4)⁻¹) =
        ENNReal.ofReal |((2 * K) ^ 3)⁻¹| * ENNReal.ofReal K⁻¹ := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [abs_of_pos (by positivity)]
      field_simp
      ring
    _ ≤ ENNReal.ofReal |((2 * K) ^ 3)⁻¹| * volume E := by gcongr
    _ = volume ((fun x : EuclideanSpace ℝ (Fin 3) => (2 * K) • x) ⁻¹' E) := by
      rw [Measure.addHaar_preimage_smul volume (by positivity : (2 * K) ≠ 0), finrank_euclideanSpace_fin]
    _ ≤ _ := measure_mono hsub

lemma normalized_witness_mass_power (m : ℕ) (K : ℝ) (hK : 0 < K)
    (P : MvPolynomial (Fin 3) ℝ) (E : Set (EuclideanSpace ℝ (Fin 3))) (V : ℝ)
    (hE : E ⊆ closedBall 0 K) (hmass : ENNReal.ofReal ((K ^ m)⁻¹) ≤ volume E)
    (hbound : ∀ x ∈ E, |eval (fun i => x i) P| ≤ V) :
    ENNReal.ofReal ((8 * K ^ (m + 3))⁻¹) ≤
      volume {x : EuclideanSpace ℝ (Fin 3) | ‖x‖ ≤ 1 / 2 ∧
        |eval (fun i => x i) (dilatePolynomial (2 * K) P)| ≤ V} := by
  have hsub : (fun x : EuclideanSpace ℝ (Fin 3) => (2 * K) • x) ⁻¹' E ⊆
      {x : EuclideanSpace ℝ (Fin 3) | ‖x‖ ≤ 1 / 2 ∧
        |eval (fun i => x i) (dilatePolynomial (2 * K) P)| ≤ V} := by
    intro x hx
    have hnorm : ‖(2 * K) • x‖ ≤ K := mem_closedBall_zero_iff.mp (hE hx)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * K)] at hnorm
    refine ⟨by nlinarith, ?_⟩
    simpa only [eval_dilatePolynomial, PiLp.smul_apply, smul_eq_mul] using hbound ((2 * K) • x) hx
  calc
    ENNReal.ofReal ((8 * K ^ (m + 3))⁻¹) =
        ENNReal.ofReal |((2 * K) ^ 3)⁻¹| * ENNReal.ofReal ((K ^ m)⁻¹) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [abs_of_pos (by positivity)]
      rw [pow_add]
      field_simp
      ring
    _ ≤ ENNReal.ofReal |((2 * K) ^ 3)⁻¹| * volume E := by gcongr
    _ = volume ((fun x : EuclideanSpace ℝ (Fin 3) => (2 * K) • x) ⁻¹' E) := by
      rw [Measure.addHaar_preimage_smul volume (by positivity : (2 * K) ≠ 0), finrank_euclideanSpace_fin]
    _ ≤ _ := measure_mono hsub

lemma norm_normalized_point (K : ℝ) (hK : 0 < K)
    (x : EuclideanSpace ℝ (Fin 3)) (hx : ‖x‖ ≤ K) :
    ‖(2 * K)⁻¹ • x‖ ≤ 1 / 2 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (2 * K)⁻¹)]
  calc
    (2 * K)⁻¹ * ‖x‖ ≤ (2 * K)⁻¹ * K := mul_le_mul_of_nonneg_left hx (by positivity)
    _ = 1 / 2 := by field_simp

lemma eval_dilatePolynomial_inv (r : ℝ) (hr : r ≠ 0)
    (P : MvPolynomial (Fin 3) ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    eval (fun i => ((r⁻¹ • x : EuclideanSpace ℝ (Fin 3)) i)) (dilatePolynomial r P) =
      eval (fun i => x i) P := by
  rw [eval_dilatePolynomial]
  apply congrArg (fun f : Fin 3 → ℝ => eval f P)
  funext i
  simp [PiLp.smul_apply, smul_eq_mul, hr]

end Submission.Obl.k4_stable_native_signal_oscillation
