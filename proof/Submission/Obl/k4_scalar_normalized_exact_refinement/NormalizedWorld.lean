import Submission.Obl.k4_scalar_normalized_exact_refinement.CoefficientVolume
import Submission.Obl.k4_scalar_normalized_exact_refinement.PolynomialCoordinates
import Submission.Obl.k4_scalar_normalized_exact_refinement.PriorTransport

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_normalized_exact_refinement

open MeasureTheory Set MvPolynomial
open scoped ENNReal

noncomputable section

lemma normalized_prior_format {R RA R' : ℝ} {D DA D' : ℕ}
    (ν : Measure Line) [IsFiniteMeasure ν]
    (hν : k4_scalar_conditional_crop_worlds.PriorData R D ν)
    (A : Set Line) (hA : MeasurableSet A) (hApos : ν A ≠ 0)
    (hFA : ∀ label, k4_scalar_conditional_crop_worlds.Format 5 RA DA {a | (label, a) ∈ A})
    (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2)
    (t₀ dt u v J δ : ℝ) (hdt : 0 < dt) (hJ : 0 < J) (hδ : 0 < δ)
    (hRsum : 1 ≤ R + RA) (hRcount : R + RA ≤ R') (hRR' : R ≤ R')
    (hD : 2 * max D DA ≤ D')
    (hheight : R * (J ^ 2 * δ ^ 3 / dt ^ 4) / (ν A).toReal ≤ R')
    (hbound : ∀ l ∈ A, ∀ i, |(normalizeLine P t₀ dt u v J δ l).2 i| ≤ R') :
    k4_scalar_conditional_crop_worlds.PriorData R' D'
      ((ν A)⁻¹ • (ν.restrict A).map
        (normalizeEquiv P hP t₀ dt u v J δ hdt.ne' hJ.ne' hδ.ne')) := by
  let σ := normalizationCoefficientEquiv P t₀ dt u v J δ hdt.ne' hJ.ne' hδ.ne'
  rw [normalizeEquiv_eq_prod]
  refine normalized_prior_data ν hν A hA hApos hFA σ (by positivity)
    (map_normalizationCoefficientEquiv P t₀ dt u v J δ hdt hJ hδ) ?_ hRR' hheight ?_
  · intro B hB
    have h := format_polynomial_preimage hB hRsum
      (inverseNormalizationPolynomials (fun i => X i) P t₀ dt u v J δ)
      (inverseNormalizationPolynomials_degree _ (by intro i; simp) P hP _ _ _ _ _ _)
    have heval : (fun a i => eval a
        (inverseNormalizationPolynomials (fun i => X i) P t₀ dt u v J δ i)) =
        (σ.symm : (Fin 5 → ℝ) → (Fin 5 → ℝ)) := by
      funext a
      rw [normalizationCoefficientEquiv_symm_apply P hP]
      simpa only [eval_X] using
        eval_inverseNormalizationPolynomials (fun i => X i) P t₀ dt u v J δ a 0
    rw [heval] at h
    exact k4_scalar_conditional_crop_worlds.Format.mono h hRcount hD
  · intro label a ha i
    rw [normalizationCoefficientEquiv_apply P hP]
    exact hbound (label, a) ha i

lemma normalized_prior_ae_bound (ν : Measure Line) (A : Set Line) (hA : MeasurableSet A)
    (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2)
    (t₀ dt u v J δ K : ℝ) (hdt : dt ≠ 0) (hJ : J ≠ 0) (hδ : δ ≠ 0)
    (hbound : ∀ l ∈ A, ∀ i, |(normalizeLine P t₀ dt u v J δ l).2 i| ≤ K) :
    ∀ᵐ l ∂((ν A)⁻¹ • (ν.restrict A).map
      (normalizeEquiv P hP t₀ dt u v J δ hdt hJ hδ)), ∀ i, |l.2 i| ≤ K := by
  apply Measure.smul_absolutelyContinuous.ae_le
  apply (normalizeEquiv P hP t₀ dt u v J δ hdt hJ hδ).measurableEmbedding.ae_map_iff.mpr
  filter_upwards [ae_restrict_mem hA] with l hl
  rw [normalizeEquiv_apply]
  exact hbound l hl

lemma normalized_event_data {RC R' : ℝ} {DC D' : ℕ}
    (C : Set (Line × ℝ)) (hC : MeasurableSet C)
    (hFC : ∀ label, k4_scalar_conditional_crop_worlds.Format 6 RC DC
      {a | coefficientState label a ∈ C})
    (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2)
    (t₀ dt u v J δ : ℝ) (hdt : 0 < dt) (hJ : J ≠ 0) (hδ : δ ≠ 0)
    (hRC : 1 ≤ RC) (hR : RC ≤ R') (hD : 2 * DC ≤ D')
    (htime : C ⊆ univ ×ˢ Icc t₀ (t₀ + dt))
    (hlabel : ∀ z ∈ C, (z.1.1 : ℝ) ≤ R') :
    k4_scalar_conditional_crop_worlds.EventData R' D'
      (((normalizeEquiv P hP t₀ dt u v J δ hdt.ne' hJ hδ).prodCongr
        (timeEquiv t₀ dt hdt.ne')) '' C) := by
  let e := (normalizeEquiv P hP t₀ dt u v J δ hdt.ne' hJ hδ).prodCongr
    (timeEquiv t₀ dt hdt.ne')
  refine ⟨e.measurableSet_image.mpr hC, ?_, ?_, ?_⟩
  · rintro z ⟨q, hq, rfl⟩
    refine ⟨mem_univ _, ?_⟩
    change timeEquiv t₀ dt hdt.ne' q.2 ∈ Icc 0 1
    rw [timeEquiv_apply]
    have ht := (htime hq).2
    exact ⟨div_nonneg (sub_nonneg.mpr ht.1) hdt.le, (div_le_one hdt).mpr (by linarith [ht.2])⟩
  · rintro z ⟨q, hq, rfl⟩
    change ((normalizeEquiv P hP t₀ dt u v J δ hdt.ne' hJ hδ q.1).1 : ℝ) ≤ R'
    rw [normalizeEquiv_apply, normalizeLine_label]
    exact hlabel q hq
  · intro label
    exact k4_scalar_conditional_crop_worlds.Format.mono
      (format_incidence_normalization_image label (hFC label) hRC P hP
        t₀ dt u v J δ hdt.ne' hJ hδ) hR hD

/-- A single assigned chart produces all the finite raw-world clauses. The
conditional prior retains every assigned trajectory; the event uses exactly the
chosen incidences. -/
theorem normalized_world_data {R RA RC R' Rfit : ℝ} {D DA DC D' : ℕ}
    (ν : Measure Line) [IsProbabilityMeasure ν]
    (hν : k4_scalar_conditional_crop_worlds.PriorData R D ν)
    (A : Set Line) (C : Set (Line × ℝ)) (hA : MeasurableSet A) (hC : MeasurableSet C)
    (hApos : ν A ≠ 0)
    (hFA : ∀ label, k4_scalar_conditional_crop_worlds.Format 5 RA DA {a | (label, a) ∈ A})
    (hFC : ∀ label, k4_scalar_conditional_crop_worlds.Format 6 RC DC {a | coefficientState label a ∈ C})
    (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2)
    (t₀ dt u v J δ : ℝ) (hdt : 0 < dt) (hJ : 0 < J) (hδ : 0 < δ)
    (hRsum : 1 ≤ R + RA) (hRcount : R + RA ≤ R') (hRR' : R ≤ R')
    (hDP : 2 * max D DA ≤ D') (hRC : 1 ≤ RC) (hRCC : RC ≤ R') (hDC : 2 * DC ≤ D')
    (hheight : R * (J ^ 2 * δ ^ 3 / dt ^ 4) / (ν A).toReal ≤ R')
    (hRfit : 0 ≤ Rfit) (hRfit' : 8 * Rfit ≤ R')
    (hlabel : ∀ l ∈ A, (l.1 : ℝ) ≤ R')
    (hCA : C ⊆ A ×ˢ Icc t₀ (t₀ + dt))
    (hfit : ∀ l ∈ A, ∀ t ∈ Icc (0 : ℝ) 1,
      |y l (t₀ + dt * t) - u - (t₀ + dt * t) * v| ≤ Rfit * J ∧
      |x l (t₀ + dt * t) -
        eval ![t₀ + dt * t, y l (t₀ + dt * t)] P| ≤ Rfit * δ) :
    k4_scalar_conditional_crop_worlds.WorldData R' D' (8 * Rfit)
      ((ν A)⁻¹ • (ν.restrict A).map
        (normalizeEquiv P hP t₀ dt u v J δ hdt.ne' hJ.ne' hδ.ne'))
      (((normalizeEquiv P hP t₀ dt u v J δ hdt.ne' hJ.ne' hδ.ne').prodCongr
        (timeEquiv t₀ dt hdt.ne')) '' C) := by
  have hcoeff : ∀ l ∈ A, ∀ i, |(normalizeLine P t₀ dt u v J δ l).2 i| ≤ 8 * Rfit := by
    intro l hl
    exact normalizeLine_bound P hP t₀ dt u v J δ Rfit hJ hδ hRfit l
      (fun t ht => (hfit l hl t ht).1) (fun t ht => (hfit l hl t ht).2)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact k4_dyadic_crop_affine_laws.Framework.conditionedPrior_probability ν A
      (normalizeEquiv P hP t₀ dt u v J δ hdt.ne' hJ.ne' hδ.ne') hApos (measure_ne_top ν A)
  · exact normalized_prior_format ν hν A hA hApos hFA P hP t₀ dt u v J δ hdt hJ hδ
      hRsum hRcount hRR' hDP hheight (fun l hl i => (hcoeff l hl i).trans hRfit')
  · exact normalized_prior_ae_bound ν A hA P hP t₀ dt u v J δ (8 * Rfit)
      hdt.ne' hJ.ne' hδ.ne' hcoeff
  · exact normalized_event_data C hC hFC P hP t₀ dt u v J δ hdt hJ.ne' hδ.ne'
      hRC hRCC hDC (fun z hz => ⟨mem_univ _, (hCA hz).2⟩)
      (fun z hz => hlabel z.1 (hCA hz).1)

end

end Submission.Obl.k4_scalar_normalized_exact_refinement
