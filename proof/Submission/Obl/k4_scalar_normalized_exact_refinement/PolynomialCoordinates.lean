import Submission.Obl.k4_scalar_normalized_exact_refinement.Coordinates
import Submission.Obl.k4_scalar_normalized_exact_refinement.Transport
import Submission.Obl.k4_scalar_conditional_crop_worlds.SignFormat
import Submission.Obl.k4_quadratic_atlas_normalization.RefinementFormat

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_normalized_exact_refinement

open MvPolynomial Set

noncomputable section

/-- Positive normalization of sign tests means polynomial pullbacks cost only
degree, and leave the bound on the number of tests unchanged. -/
lemma format_polynomial_preimage {n m D d : ℕ} {R : ℝ} {S : Set (Fin n → ℝ)}
    (hS : k4_scalar_linear_critical_extremizers.Split.Format n R D S) (hR : 1 ≤ R)
    (f : Fin n → MvPolynomial (Fin m) ℝ) (hf : ∀ i, (f i).totalDegree ≤ d) :
    k4_scalar_linear_critical_extremizers.Split.Format m R (d * D)
      ((fun a i => eval a (f i)) ⁻¹' S) := by
  classical
  obtain ⟨k, hk, p, hp, T, rfl⟩ := hS
  apply k4_scalar_conditional_crop_worlds.format_of_signRep hR hk
  refine ⟨(fun j => aeval f (p j)), T, ?_, ?_⟩
  · intro j
    exact (k4_quadratic_atlas_normalization.degree_aeval_le_mul _ _ d hf).trans
      (Nat.mul_le_mul_left d (hp j).1)
  · intro a
    simp only [mem_preimage, mem_ofPred_eq, id_eq,
      k4_eligibility_sign_description.eval_aeval_real]

/-- Fixed-time evaluation of the predictor as a polynomial in line coefficients. -/
def predictorPolynomial {n : ℕ} (a : Fin 5 → MvPolynomial (Fin n) ℝ)
    (P : MvPolynomial (Fin 2) ℝ) (t : ℝ) : MvPolynomial (Fin n) ℝ :=
  aeval ![C t, a 0 + C t * a 1] P

def residualPolynomial {n : ℕ} (a : Fin 5 → MvPolynomial (Fin n) ℝ)
    (P : MvPolynomial (Fin 2) ℝ) (t δ : ℝ) : MvPolynomial (Fin n) ℝ :=
  C δ⁻¹ * (a 2 + C t * a 3 + C (t ^ 2) * a 4 - predictorPolynomial a P t)

def normalizationPolynomials {n : ℕ} (a : Fin 5 → MvPolynomial (Fin n) ℝ)
    (P : MvPolynomial (Fin 2) ℝ) (t₀ dt u v J δ : ℝ) : Fin 5 → MvPolynomial (Fin n) ℝ :=
  let R := fun s : ℝ => residualPolynomial a P (t₀ + dt * s) δ
  ![C J⁻¹ * (a 0 + C t₀ * a 1 - C (u + t₀ * v)),
    C (dt / J) * (a 1 - C v),
    R 0, C 4 * R (1 / 2) - R 1 - C 3 * R 0,
    C 2 * (R 1 - C 2 * R (1 / 2) + R 0)]

lemma eval_predictorPolynomial {n : ℕ} (a : Fin 5 → MvPolynomial (Fin n) ℝ)
    (P : MvPolynomial (Fin 2) ℝ) (t : ℝ) (z : Fin n → ℝ) :
    eval z (predictorPolynomial a P t) = eval ![t, eval z (a 0) + t * eval z (a 1)] P := by
  rw [predictorPolynomial, k4_eligibility_sign_description.eval_aeval_real]
  apply congrArg (fun b : Fin 2 → ℝ => eval b P)
  funext i
  fin_cases i <;> simp

lemma eval_normalizationPolynomials {n : ℕ} (a : Fin 5 → MvPolynomial (Fin n) ℝ)
    (P : MvPolynomial (Fin 2) ℝ) (t₀ dt u v J δ : ℝ) (z : Fin n → ℝ) (label : ℕ) :
    (fun i => eval z (normalizationPolynomials a P t₀ dt u v J δ i)) =
      (normalizeLine P t₀ dt u v J δ (label, fun i => eval z (a i))).2 := by
  funext i
  fin_cases i <;>
    simp [normalizationPolynomials, residualPolynomial, eval_predictorPolynomial,
      normalizeLine, y, x, k4_scalar_linear_critical_extremizers.Split.y,
      k4_scalar_linear_critical_extremizers.Split.x] <;> ring

lemma predictorPolynomial_degree {n : ℕ} (a : Fin 5 → MvPolynomial (Fin n) ℝ)
    (ha : ∀ i, (a i).totalDegree ≤ 1) (P : MvPolynomial (Fin 2) ℝ) (t : ℝ) :
    (predictorPolynomial a P t).totalDegree ≤ P.totalDegree := by
  apply k4_eligibility_sign_description.degree_aeval_le
  intro i
  fin_cases i
  · simp
  · apply k4_eligibility_sign_description.degree_add_le (ha 0)
    exact (k4_eligibility_sign_description.degree_C_mul_le _ _).trans (ha 1)

lemma residualPolynomial_degree {n d : ℕ} (a : Fin 5 → MvPolynomial (Fin n) ℝ)
    (ha : ∀ i, (a i).totalDegree ≤ 1) (hd : 1 ≤ d)
    (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ d) (t δ : ℝ) :
    (residualPolynomial a P t δ).totalDegree ≤ d := by
  apply (k4_eligibility_sign_description.degree_C_mul_le _ _).trans
  apply k4_eligibility_sign_description.degree_sub_le
  · apply k4_eligibility_sign_description.degree_add_le
    · apply k4_eligibility_sign_description.degree_add_le ((ha 2).trans hd)
      exact (k4_eligibility_sign_description.degree_C_mul_le _ _).trans ((ha 3).trans hd)
    · exact (k4_eligibility_sign_description.degree_C_mul_le _ _).trans ((ha 4).trans hd)
  · exact (predictorPolynomial_degree a ha P t).trans hP

lemma normalizationPolynomials_degree {n d : ℕ} (a : Fin 5 → MvPolynomial (Fin n) ℝ)
    (ha : ∀ i, (a i).totalDegree ≤ 1) (hd : 1 ≤ d)
    (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ d)
    (t₀ dt u v J δ : ℝ) :
    ∀ i, (normalizationPolynomials a P t₀ dt u v J δ i).totalDegree ≤ d := by
  have hr (s : ℝ) := residualPolynomial_degree a ha hd P hP (t₀ + dt * s) δ
  intro i
  fin_cases i <;> dsimp [normalizationPolynomials]
  · apply (k4_eligibility_sign_description.degree_C_mul_le _ _).trans
    apply k4_eligibility_sign_description.degree_sub_le
    · apply k4_eligibility_sign_description.degree_add_le ((ha 0).trans hd)
      exact (k4_eligibility_sign_description.degree_C_mul_le _ _).trans ((ha 1).trans hd)
    · simpa only [← map_mul, ← map_add, totalDegree_C] using Nat.zero_le d
  · apply (k4_eligibility_sign_description.degree_C_mul_le _ _).trans
    exact k4_eligibility_sign_description.degree_sub_le ((ha 1).trans hd) (by simp)
  · exact hr 0
  · apply k4_eligibility_sign_description.degree_sub_le
    · apply k4_eligibility_sign_description.degree_sub_le
      · exact (k4_eligibility_sign_description.degree_C_mul_le _ _).trans (hr (1 / 2))
      · exact hr 1
    · exact (k4_eligibility_sign_description.degree_C_mul_le _ _).trans (hr 0)
  · apply (k4_eligibility_sign_description.degree_C_mul_le _ _).trans
    apply k4_eligibility_sign_description.degree_add_le
    · apply k4_eligibility_sign_description.degree_sub_le (hr 1)
      exact (k4_eligibility_sign_description.degree_C_mul_le _ _).trans (hr (1 / 2))
    · exact hr 0

def inverseNormalizationPolynomials {n : ℕ} (a : Fin 5 → MvPolynomial (Fin n) ℝ)
    (P : MvPolynomial (Fin 2) ℝ) (t₀ dt u v J δ : ℝ) : Fin 5 → MvPolynomial (Fin n) ℝ :=
  normalizationPolynomials
    (normalizationPolynomials a 0 (-t₀ / dt) dt⁻¹
      (-(u + t₀ * v) / J) (-dt * v / J) J⁻¹ δ⁻¹)
    (-P) 0 1 0 0 1 1

lemma eval_inverseNormalizationPolynomials {n : ℕ} (a : Fin 5 → MvPolynomial (Fin n) ℝ)
    (P : MvPolynomial (Fin 2) ℝ) (t₀ dt u v J δ : ℝ) (z : Fin n → ℝ) (label : ℕ) :
    (fun i => eval z (inverseNormalizationPolynomials a P t₀ dt u v J δ i)) =
      (normalizeLine (-P) 0 1 0 0 1 1
        (normalizeLine 0 (-t₀ / dt) dt⁻¹ (-(u + t₀ * v) / J)
          (-dt * v / J) J⁻¹ δ⁻¹ (label, fun i => eval z (a i)))).2 := by
  rw [inverseNormalizationPolynomials, eval_normalizationPolynomials _ _ _ _ _ _ _ _ z label,
    eval_normalizationPolynomials _ _ _ _ _ _ _ _ z label]
  rfl

lemma inverseNormalizationPolynomials_degree {n : ℕ} (a : Fin 5 → MvPolynomial (Fin n) ℝ)
    (ha : ∀ i, (a i).totalDegree ≤ 1) (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2)
    (t₀ dt u v J δ : ℝ) :
    ∀ i, (inverseNormalizationPolynomials a P t₀ dt u v J δ i).totalDegree ≤ 2 := by
  apply normalizationPolynomials_degree
  · exact normalizationPolynomials_degree a ha le_rfl 0 (by simp) _ _ _ _ _ _
  · norm_num
  · simpa using hP

lemma format_normalizeLine_preimage {D : ℕ} {R : ℝ} {S : Set (Fin 5 → ℝ)}
    (hS : k4_scalar_linear_critical_extremizers.Split.Format 5 R D S) (hR : 1 ≤ R)
    (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2) (t₀ dt u v J δ : ℝ) (label : ℕ) :
    k4_scalar_linear_critical_extremizers.Split.Format 5 R (2 * D)
      ((fun a => (normalizeLine P t₀ dt u v J δ (label, a)).2) ⁻¹' S) := by
  have h := format_polynomial_preimage hS hR
    (normalizationPolynomials (fun i => X i) P t₀ dt u v J δ)
    (normalizationPolynomials_degree _ (by intro i; simp) (by norm_num) P hP _ _ _ _ _ _)
  convert h using 1
  ext a
  simp only [mem_preimage, eval_normalizationPolynomials _ _ _ _ _ _ _ _ a label, eval_X]

lemma format_normalizeEquiv_image {D : ℕ} {R : ℝ} {S : Set (Fin 5 → ℝ)}
    (hS : k4_scalar_linear_critical_extremizers.Split.Format 5 R D S) (hR : 1 ≤ R)
    (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2) (t₀ dt u v J δ : ℝ)
    (hdt : dt ≠ 0) (hJ : J ≠ 0) (hδ : δ ≠ 0) (label : ℕ) :
    k4_scalar_linear_critical_extremizers.Split.Format 5 R (2 * D)
      {a | (normalizeEquiv P hP t₀ dt u v J δ hdt hJ hδ).symm (label, a) ∈
        (fun b => (label, b)) '' S} := by
  have h := format_polynomial_preimage hS hR
    (inverseNormalizationPolynomials (fun i => X i) P t₀ dt u v J δ)
    (inverseNormalizationPolynomials_degree _ (by intro i; simp) P hP _ _ _ _ _ _)
  convert h using 1
  ext a
  simp only [mem_ofPred_eq, mem_preimage,
    eval_inverseNormalizationPolynomials _ _ _ _ _ _ _ _ a label, eval_X]
  change ((normalizeEquiv P hP t₀ dt u v J δ hdt hJ hδ).symm (label, a) ∈
    (fun b => (label, b)) '' S) ↔
    ((normalizeEquiv P hP t₀ dt u v J δ hdt hJ hδ).symm (label, a)).2 ∈ S
  constructor
  · rintro ⟨b, hb, heq⟩
    rw [← heq]
    exact hb
  · intro ha
    refine ⟨_, ha, ?_⟩
    rfl

def coefficientState (label : ℕ) (a : Fin 6 → ℝ) : Line × ℝ :=
  ((label, fun i : Fin 5 => a i.castSucc), a 5)

def incidenceNormalizationPolynomials (P : MvPolynomial (Fin 2) ℝ)
    (t₀ dt u v J δ : ℝ) : Fin 6 → MvPolynomial (Fin 6) ℝ :=
  Fin.snoc (normalizationPolynomials (fun i : Fin 5 => X i.castSucc) P t₀ dt u v J δ)
    (C dt⁻¹ * (X 5 - C t₀))

def inverseIncidenceNormalizationPolynomials (P : MvPolynomial (Fin 2) ℝ)
    (t₀ dt u v J δ : ℝ) : Fin 6 → MvPolynomial (Fin 6) ℝ :=
  Fin.snoc (inverseNormalizationPolynomials (fun i : Fin 5 => X i.castSucc) P t₀ dt u v J δ)
    (C t₀ + C dt * X 5)

lemma timeEquiv_symm_apply (t₀ dt : ℝ) (hdt : dt ≠ 0) (t : ℝ) :
    (timeEquiv t₀ dt hdt).symm t = t₀ + dt * t := by
  apply (timeEquiv t₀ dt hdt).injective
  rw [MeasurableEquiv.apply_symm_apply, timeEquiv_apply]
  field_simp
  ring

lemma eval_incidenceNormalizationPolynomials (P : MvPolynomial (Fin 2) ℝ)
    (hP : P.totalDegree ≤ 2) (t₀ dt u v J δ : ℝ)
    (hdt : dt ≠ 0) (hJ : J ≠ 0) (hδ : δ ≠ 0) (label : ℕ) (a : Fin 6 → ℝ) :
    coefficientState label (fun i => eval a (incidenceNormalizationPolynomials P t₀ dt u v J δ i)) =
      ((normalizeEquiv P hP t₀ dt u v J δ hdt hJ hδ).prodCongr (timeEquiv t₀ dt hdt))
        (coefficientState label a) := by
  apply Prod.ext
  · change (label, _) = normalizeEquiv P hP t₀ dt u v J δ hdt hJ hδ _
    rw [normalizeEquiv_apply]
    apply Prod.ext
    · rfl
    · simpa only [incidenceNormalizationPolynomials, Fin.snoc_castSucc, eval_X] using
        eval_normalizationPolynomials (fun i : Fin 5 => X i.castSucc) P t₀ dt u v J δ a label
  · change eval a (C dt⁻¹ * (X 5 - C t₀)) = timeEquiv t₀ dt hdt (a 5)
    rw [timeEquiv_apply]
    simp only [map_mul, map_sub, eval_C, eval_X]
    ring

lemma eval_inverseIncidenceNormalizationPolynomials (P : MvPolynomial (Fin 2) ℝ)
    (hP : P.totalDegree ≤ 2) (t₀ dt u v J δ : ℝ)
    (hdt : dt ≠ 0) (hJ : J ≠ 0) (hδ : δ ≠ 0) (label : ℕ) (a : Fin 6 → ℝ) :
    coefficientState label
      (fun i => eval a (inverseIncidenceNormalizationPolynomials P t₀ dt u v J δ i)) =
      ((normalizeEquiv P hP t₀ dt u v J δ hdt hJ hδ).prodCongr (timeEquiv t₀ dt hdt)).symm
        (coefficientState label a) := by
  apply Prod.ext
  · change (label, _) = (normalizeEquiv P hP t₀ dt u v J δ hdt hJ hδ).symm _
    apply Prod.ext
    · rfl
    · change _ =
        (normalizeLine (-P) 0 1 0 0 1 1
          (normalizeLine 0 (-t₀ / dt) dt⁻¹ (-(u + t₀ * v) / J)
            (-dt * v / J) J⁻¹ δ⁻¹ (label, fun i : Fin 5 => a i.castSucc))).2
      simpa only [inverseIncidenceNormalizationPolynomials, Fin.snoc_castSucc, eval_X] using
        eval_inverseNormalizationPolynomials (fun i : Fin 5 => X i.castSucc) P t₀ dt u v J δ a label
  · change eval a (C t₀ + C dt * X 5) = (timeEquiv t₀ dt hdt).symm (a 5)
    rw [timeEquiv_symm_apply]
    simp

lemma incidenceNormalizationPolynomials_degree (P : MvPolynomial (Fin 2) ℝ)
    (hP : P.totalDegree ≤ 2) (t₀ dt u v J δ : ℝ) :
    ∀ i, (incidenceNormalizationPolynomials P t₀ dt u v J δ i).totalDegree ≤ 2 := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · change (C dt⁻¹ * (X 5 - C t₀) : MvPolynomial (Fin 6) ℝ).totalDegree ≤ 2
    apply (k4_eligibility_sign_description.degree_C_mul_le _ _).trans
    exact k4_eligibility_sign_description.degree_sub_le (by simp) (by simp)
  · simpa only [incidenceNormalizationPolynomials, Fin.snoc_castSucc] using
      normalizationPolynomials_degree (fun i : Fin 5 => (X i.castSucc : MvPolynomial (Fin 6) ℝ))
        (by intro i; simp) (by norm_num) P hP t₀ dt u v J δ j

lemma inverseIncidenceNormalizationPolynomials_degree (P : MvPolynomial (Fin 2) ℝ)
    (hP : P.totalDegree ≤ 2) (t₀ dt u v J δ : ℝ) :
    ∀ i, (inverseIncidenceNormalizationPolynomials P t₀ dt u v J δ i).totalDegree ≤ 2 := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · change (C t₀ + C dt * X 5 : MvPolynomial (Fin 6) ℝ).totalDegree ≤ 2
    apply k4_eligibility_sign_description.degree_add_le (by simp)
    exact (k4_eligibility_sign_description.degree_C_mul_le _ _).trans (by simp)
  · simpa only [inverseIncidenceNormalizationPolynomials, Fin.snoc_castSucc] using
      inverseNormalizationPolynomials_degree (fun i : Fin 5 => (X i.castSucc : MvPolynomial (Fin 6) ℝ))
        (by intro i; simp) P hP t₀ dt u v J δ j

lemma format_incidence_normalization_preimage {D : ℕ} {R : ℝ} {S : Set (Line × ℝ)}
    (label : ℕ)
    (hS : k4_scalar_linear_critical_extremizers.Split.Format 6 R D {a | coefficientState label a ∈ S})
    (hR : 1 ≤ R) (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2)
    (t₀ dt u v J δ : ℝ) (hdt : dt ≠ 0) (hJ : J ≠ 0) (hδ : δ ≠ 0) :
    k4_scalar_linear_critical_extremizers.Split.Format 6 R (2 * D)
      {a | coefficientState label a ∈
        ((normalizeEquiv P hP t₀ dt u v J δ hdt hJ hδ).prodCongr (timeEquiv t₀ dt hdt)) ⁻¹' S} := by
  have h := format_polynomial_preimage hS hR
    (incidenceNormalizationPolynomials P t₀ dt u v J δ)
    (incidenceNormalizationPolynomials_degree P hP t₀ dt u v J δ)
  convert h using 1
  ext a
  simp only [mem_ofPred_eq, mem_preimage]
  rw [eval_incidenceNormalizationPolynomials P hP t₀ dt u v J δ hdt hJ hδ label a]

lemma format_incidence_normalization_image {D : ℕ} {R : ℝ} {S : Set (Line × ℝ)}
    (label : ℕ)
    (hS : k4_scalar_linear_critical_extremizers.Split.Format 6 R D {a | coefficientState label a ∈ S})
    (hR : 1 ≤ R) (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2)
    (t₀ dt u v J δ : ℝ) (hdt : dt ≠ 0) (hJ : J ≠ 0) (hδ : δ ≠ 0) :
    k4_scalar_linear_critical_extremizers.Split.Format 6 R (2 * D)
      {a | coefficientState label a ∈
        ((normalizeEquiv P hP t₀ dt u v J δ hdt hJ hδ).prodCongr (timeEquiv t₀ dt hdt)) '' S} := by
  have h := format_polynomial_preimage hS hR
    (inverseIncidenceNormalizationPolynomials P t₀ dt u v J δ)
    (inverseIncidenceNormalizationPolynomials_degree P hP t₀ dt u v J δ)
  convert h using 1
  ext a
  simp only [mem_ofPred_eq, mem_preimage]
  rw [eval_inverseIncidenceNormalizationPolynomials P hP t₀ dt u v J δ hdt hJ hδ label a]
  constructor
  · rintro ⟨b, hb, heq⟩
    rw [← heq, MeasurableEquiv.symm_apply_apply]
    exact hb
  · intro ha
    exact ⟨_, ha, MeasurableEquiv.apply_symm_apply _ _⟩

end

end Submission.Obl.k4_scalar_normalized_exact_refinement
