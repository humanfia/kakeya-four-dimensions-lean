import Submission.Obl.k4_adapted_oscillation_tests.Basic
import Submission.Obl.k4_adapted_oscillation_tests.Affine
import Submission.Lib.K4PolynomialGeometry.ProductOscillation

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Obl.k4_adapted_oscillation_tests

/-- The coordinate derivative integrals are finite for a continuously differentiable function. -/
theorem cube_integral_bound_of_lintegral_bound {n : ℕ}
    (L : Space n ≃L[ℝ] Space n) (c : Space n) (f : Space n → ℝ)
    (hf : ContDiff ℝ 1 f)
    (hbound :
      (∫⁻ p : (Fin n → ℝ) × (Fin n → ℝ),
        ENNReal.ofReal |f (c + L (WithLp.toLp 2 p.1)) - f (c + L (WithLp.toLp 2 p.2))|
        ∂(volume.restrict (Set.Icc 0 1)).prod (volume.restrict (Set.Icc 0 1))) ≤
      ∑ i : Fin n, ∫⁻ x in Set.Icc (0 : Fin n → ℝ) 1,
        ENNReal.ofReal ‖fderiv ℝ f (c + L (WithLp.toLp 2 x))
          (L (EuclideanSpace.single i 1))‖) :
    (∫ x in Set.Icc (0 : Fin n → ℝ) 1,
      ∫ y in Set.Icc (0 : Fin n → ℝ) 1,
        |f (c + L (WithLp.toLp 2 x)) - f (c + L (WithLp.toLp 2 y))|) ≤
      ∑ i : Fin n, ∫ x in Set.Icc (0 : Fin n → ℝ) 1,
        ‖fderiv ℝ f (c + L (WithLp.toLp 2 x)) (L (EuclideanSpace.single i 1))‖ := by
  let μ : Measure (Fin n → ℝ) := volume.restrict (Set.Icc 0 1)
  let g : (Fin n → ℝ) → ℝ := fun x => f (c + L (WithLp.toLp 2 x))
  let F (i : Fin n) (x : Fin n → ℝ) :=
    ‖fderiv ℝ f (c + L (WithLp.toLp 2 x)) (L (EuclideanSpace.single i 1))‖
  have : IsProbabilityMeasure μ := ⟨by simp [μ, Real.volume_Icc_pi]⟩
  have hT : Continuous (fun x : Fin n → ℝ => c + L (WithLp.toLp 2 x)) :=
    continuous_const.add (L.continuous.comp (PiLp.continuous_toLp 2 _))
  have hg : Integrable g μ :=
    (hf.continuous.comp hT).continuousOn.integrableOn_compact isCompact_Icc
  have hF (i : Fin n) : Integrable (F i) μ :=
    ((((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).norm).comp hT).continuousOn.integrableOn_compact isCompact_Icc
  exact pairwise_integral_le_sum_of_lintegral_bound hg F hF (fun i x => norm_nonneg _) hbound

/-- Transport a normalized coordinate-cube oscillation estimate to ambient volume. -/
theorem tile_poincare_of_cube_bound {n : ℕ}
    (L : Space n ≃L[ℝ] Space n) (c : Space n) (f : Space n → ℝ)
    (hf : Continuous f)
    (hbound :
      (∫ x in Set.Icc (0 : Fin n → ℝ) 1,
        ∫ y in Set.Icc (0 : Fin n → ℝ) 1,
          |f (c + L (WithLp.toLp 2 x)) - f (c + L (WithLp.toLp 2 y))|) ≤
      ∑ i : Fin n, ∫ x in Set.Icc (0 : Fin n → ℝ) 1,
        ‖fderiv ℝ f (c + L (WithLp.toLp 2 x)) (L (EuclideanSpace.single i 1))‖) :
    (∫ x in affineCube L c, |f x|) - |∫ x in affineCube L c, f x| ≤
      ∑ i : Fin n, ∫ x in affineCube L c,
        ‖fderiv ℝ f x (L (EuclideanSpace.single i 1))‖ := by
  let μ : Measure (Fin n → ℝ) := volume.restrict (Set.Icc 0 1)
  let g : (Fin n → ℝ) → ℝ := fun x => f (c + L (WithLp.toLp 2 x))
  let d : ℝ := |LinearMap.det (L : Space n →ₗ[ℝ] Space n)|
  have hd : 0 ≤ d := abs_nonneg _
  have : IsProbabilityMeasure μ := ⟨by simp [μ, Real.volume_Icc_pi]⟩
  have hg : Integrable g μ := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact (hf.comp (continuous_const.add (L.continuous.comp
      (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ))))).continuousOn
  have hraw := (integral_abs_sub_abs_integral_le_pairwise hg).trans hbound
  have hsum :
      (∑ i : Fin n, ∫ x in affineCube L c,
        ‖fderiv ℝ f x (L (EuclideanSpace.single i 1))‖) =
      d * ∑ i : Fin n, ∫ x in Set.Icc (0 : Fin n → ℝ) 1,
        ‖fderiv ℝ f (c + L (WithLp.toLp 2 x)) (L (EuclideanSpace.single i 1))‖ := by
    simp_rw [integral_affineCube]
    exact (Finset.mul_sum _ _ _).symm
  rw [hsum, integral_affineCube, integral_affineCube]
  change d * (∫ x, |g x| ∂μ) - |d * ∫ x, g x ∂μ| ≤ d * _
  rw [abs_mul, abs_of_nonneg hd, ← mul_sub]
  exact mul_le_mul_of_nonneg_left hraw hd

/-- The two normalized oscillation tests force a definite directional variation. -/
theorem tile_oscillation_of_cube_bound {n : ℕ}
    (L : Space n ≃L[ℝ] Space n) (c : Space n) (f : Space n → ℝ)
    (hf : Continuous f)
    (hbound :
      (∫ x in Set.Icc (0 : Fin n → ℝ) 1,
        ∫ y in Set.Icc (0 : Fin n → ℝ) 1,
          |f (c + L (WithLp.toLp 2 x)) - f (c + L (WithLp.toLp 2 y))|) ≤
      ∑ i : Fin n, ∫ x in Set.Icc (0 : Fin n → ℝ) 1,
        ‖fderiv ℝ f (c + L (WithLp.toLp 2 x)) (L (EuclideanSpace.single i 1))‖)
    (hmean : |∫ x in affineCube L c, f x| ≤ (volume (affineCube L c)).toReal / 2)
    (habs : (volume (affineCube L c)).toReal ≤ ∫ x in affineCube L c, |f x|) :
    (volume (affineCube L c)).toReal / 2 ≤
      ∑ i : Fin n, ∫ x in affineCube L c,
        ‖fderiv ℝ f x (L (EuclideanSpace.single i 1))‖ := by
  have h := tile_poincare_of_cube_bound L c f hf hbound
  linarith

theorem cube_integral_bound {n : ℕ}
    (L : Space n ≃L[ℝ] Space n) (c : Space n) (f : Space n → ℝ)
    (hf : ContDiff ℝ 1 f) :
    (∫ x in Set.Icc (0 : Fin n → ℝ) 1,
      ∫ y in Set.Icc (0 : Fin n → ℝ) 1,
        |f (c + L (WithLp.toLp 2 x)) - f (c + L (WithLp.toLp 2 y))|) ≤
      ∑ i : Fin n, ∫ x in Set.Icc (0 : Fin n → ℝ) 1,
        ‖fderiv ℝ f (c + L (WithLp.toLp 2 x)) (L (EuclideanSpace.single i 1))‖ := by
  let A : (Fin n → ℝ) →L[ℝ] Space n :=
    (L : Space n →L[ℝ] Space n).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.toContinuousLinearMap
  have h := Submission.Lib.K4PolynomialGeometry.affine_cube_oscillation_le A c f hf
  simp only [Submission.Lib.K4PolynomialGeometry.unitCubeVolume,
    Submission.Lib.K4PolynomialGeometry.unitIntervalVolume, pi_unitInterval_restrict] at h
  apply cube_integral_bound_of_lintegral_bound L c f hf
  exact h

theorem tile_poincare {n : ℕ}
    (L : Space n ≃L[ℝ] Space n) (c : Space n) (f : Space n → ℝ)
    (hf : ContDiff ℝ 1 f) :
    (∫ x in affineCube L c, |f x|) - |∫ x in affineCube L c, f x| ≤
      ∑ i : Fin n, ∫ x in affineCube L c,
        ‖fderiv ℝ f x (L (EuclideanSpace.single i 1))‖ :=
  tile_poincare_of_cube_bound L c f hf.continuous (cube_integral_bound L c f hf)

theorem tile_oscillation {n : ℕ}
    (L : Space n ≃L[ℝ] Space n) (c : Space n) (f : Space n → ℝ)
    (hf : ContDiff ℝ 1 f)
    (hmean : |∫ x in affineCube L c, f x| ≤ (volume (affineCube L c)).toReal / 2)
    (habs : (volume (affineCube L c)).toReal ≤ ∫ x in affineCube L c, |f x|) :
    (volume (affineCube L c)).toReal / 2 ≤
      ∑ i : Fin n, ∫ x in affineCube L c,
        ‖fderiv ℝ f x (L (EuclideanSpace.single i 1))‖ := by
  have h := tile_poincare L c f hf
  linarith

theorem basis_cube_directional_poincare :
    ∀ n : ℕ, 1 ≤ n → ∃ P : ℝ, 0 < P ∧
      ∀ (b : Module.Basis (Fin n) ℝ (Space n)) (η : ℝ), 0 < η →
      ∀ (a : Space n) (Q : Set (Space n)),
      Q = (fun t : Fin n → ℝ => a + η • (∑ i : Fin n, t i • b i)) '' Set.Icc (0 : Fin n → ℝ) 1 →
      ∀ f : Space n → ℝ, ContDiff ℝ 1 f →
      (∫ x in Q, |f x|) - |∫ x in Q, f x| ≤
        η * P * (∑ i : Fin n, ∫ x in Q, ‖fderiv ℝ f x (b i)‖) := by
  intro n hn
  refine ⟨1, zero_lt_one, ?_⟩
  intro b η hη a Q hQ f hf
  subst Q
  have h := tile_poincare (basisScaleEquiv b η hη.ne') a f hf
  simp_rw [basisScaleEquiv_single, map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos hη, integral_const_mul] at h
  rw [← Finset.mul_sum] at h
  simpa only [affineCube_basisScaleEquiv, Real.norm_eq_abs, mul_one] using h


end Submission.Obl.k4_adapted_oscillation_tests
