import Submission.Lib.K4PolynomialGeometry.ProductOscillation

/-!
# The L1 Poincaré inequality on the coordinate unit cube

For a `C¹` function `g` on `Fin n → ℝ` and the unit cube `Icc 0 1` (a probability space),

  `∫ |g| - |∫ g| ≤ ∑ i, ∫ ‖Dg(t) eᵢ‖`,

and the same along an affine map `t ↦ c + A t` into any normed space (`affine_cube_poincare`).

The coordinate tensorization and fundamental theorem of calculus estimates are
imported from the accepted `Submission.Lib.K4PolynomialGeometry.ProductOscillation`.

The real-integral conversion helpers are adapted from original proofs by session
x0138 in this LOT tree (g-oai-074), obligation o046, branch x0138, commit 0b78964,
`Submission/Obl/k4_adapted_oscillation_tests/Basic.lean` and `Affine.lean`:
`integral_abs_sub_abs_integral_le_pairwise`,
`pairwise_integral_le_sum_of_lintegral_bound`, and `pi_unitInterval_restrict`.
-/

namespace Submission.Obl.k4_affine_cube_directional_poincare

open MeasureTheory Set
open scoped ENNReal
open Submission.Lib.K4PolynomialGeometry

/-! ### From lower integrals to real integrals (from o046/x0138) -/

/-- The product of unit-interval measures is Lebesgue measure restricted to the unit cube. -/
theorem pi_unitInterval_restrict (n : ℕ) :
    Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1)) =
      (volume : Measure (Fin n → ℝ)).restrict (Set.Icc 0 1) := by
  rw [← Measure.restrict_pi_pi]
  exact congrArg (fun s : Set (Fin n → ℝ) =>
    (volume : Measure (Fin n → ℝ)).restrict s)
    (pi_univ_Icc (x := (0 : Fin n → ℝ)) (y := (1 : Fin n → ℝ)))

theorem unitCubeVolume_eq (n : ℕ) :
    unitCubeVolume n = (volume : Measure (Fin n → ℝ)).restrict (Set.Icc 0 1) :=
  pi_unitInterval_restrict n

/-- On a probability space, pairwise oscillation controls the excess of the
absolute integral over the absolute mean. -/
theorem integral_abs_sub_abs_integral_le_pairwise
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → ℝ} (hf : Integrable f μ) :
    (∫ x, |f x| ∂μ) - |∫ x, f x ∂μ| ≤
      ∫ x, ∫ y, |f x - f y| ∂μ ∂μ := by
  have hd : Integrable (fun p : α × α => |f p.1 - f p.2|) (μ.prod μ) :=
    ((hf.comp_fst μ).sub (hf.comp_snd μ)).abs
  have hx (x : α) : |f x| - |∫ y, f y ∂μ| ≤ ∫ y, |f x - f y| ∂μ := by
    refine (abs_sub_abs_le_abs_sub _ _).trans ?_
    have heq : (∫ y, f x - f y ∂μ) = f x - ∫ y, f y ∂μ := by
      rw [integral_sub (integrable_const _) hf]
      simp
    rw [← heq]
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
      (fun y => f x - f y) (μ := μ)
  have h := integral_mono (hf.abs.sub (integrable_const _)) hd.integral_prod_left hx
  change (∫ x, |f x| - |∫ y, f y ∂μ| ∂μ) ≤
    ∫ x, ∫ y, |f x - f y| ∂μ ∂μ at h
  rw [integral_sub hf.abs (integrable_const _)] at h
  simpa using h

/-- Convert a nonnegative cube oscillation bound from lower integrals to real integrals. -/
theorem pairwise_integral_le_sum_of_lintegral_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] {f : α → ℝ} (hf : Integrable f μ)
    (F : ι → α → ℝ) (hF : ∀ i, Integrable (F i) μ) (hFpos : ∀ i x, 0 ≤ F i x)
    (hbound : (∫⁻ p : α × α, ENNReal.ofReal |f p.1 - f p.2| ∂μ.prod μ) ≤
      ∑ i, ∫⁻ x, ENNReal.ofReal (F i x) ∂μ) :
    (∫ x, ∫ y, |f x - f y| ∂μ ∂μ) ≤ ∑ i, ∫ x, F i x ∂μ := by
  have hpair : Integrable (fun p : α × α => |f p.1 - f p.2|) (μ.prod μ) :=
    ((hf.comp_fst μ).sub (hf.comp_snd μ)).abs
  have hfin (i : ι) : (∫⁻ x, ENNReal.ofReal (F i x) ∂μ) ≠ ∞ := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hF i)
      (Filter.Eventually.of_forall (hFpos i))]
    exact ENNReal.ofReal_ne_top
  have hreal := ENNReal.toReal_mono
    (ENNReal.sum_ne_top.mpr (fun i hi => hfin i)) hbound
  rw [ENNReal.toReal_sum (fun i hi => hfin i)] at hreal
  have hleft :
      (∫⁻ p : α × α, ENNReal.ofReal |f p.1 - f p.2| ∂μ.prod μ).toReal =
      ∫ x, ∫ y, |f x - f y| ∂μ ∂μ := by
    rw [← integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun p : α × α => abs_nonneg (f p.1 - f p.2))
      hpair.aestronglyMeasurable]
    exact integral_prod _ hpair
  rw [hleft] at hreal
  have hright (i : ι) : (∫⁻ x, ENNReal.ofReal (F i x) ∂μ).toReal = ∫ x, F i x ∂μ :=
    (integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (hFpos i))
      (hF i).aestronglyMeasurable).symm
  simpa only [hright] using hreal

/-! ### The cube Poincaré inequality with real integrals -/

/-- **L1 Poincaré inequality on the unit cube, along an affine map.** For a `C¹` function `f`
on a normed space, a continuous linear `A : (Fin n → ℝ) →L[ℝ] E` and `c : E`,
`∫ |f(c + A t)| - |∫ f(c + A t)| ≤ ∑ i, ∫ ‖Df(c + A t) (A eᵢ)‖`, all integrals over the unit
cube `Icc 0 1`. -/
theorem affine_cube_poincare {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : (Fin n → ℝ) →L[ℝ] E) (c : E) (f : E → ℝ) (hf : ContDiff ℝ 1 f) :
    (∫ t in Set.Icc (0 : Fin n → ℝ) 1, |f (c + A t)|) -
        |∫ t in Set.Icc (0 : Fin n → ℝ) 1, f (c + A t)| ≤
      ∑ i : Fin n, ∫ t in Set.Icc (0 : Fin n → ℝ) 1,
        ‖fderiv ℝ f (c + A t) (A (Pi.single i 1))‖ := by
  have : IsProbabilityMeasure ((volume : Measure (Fin n → ℝ)).restrict (Set.Icc 0 1)) :=
    ⟨by simp [Real.volume_Icc_pi]⟩
  have hT : Continuous (fun t : Fin n → ℝ => c + A t) := continuous_const.add A.continuous
  have hg : Integrable (fun t => f (c + A t))
      ((volume : Measure (Fin n → ℝ)).restrict (Set.Icc 0 1)) :=
    (hf.continuous.comp hT).continuousOn.integrableOn_compact isCompact_Icc
  have hF (i : Fin n) : Integrable (fun t => ‖fderiv ℝ f (c + A t) (A (Pi.single i 1))‖)
      ((volume : Measure (Fin n → ℝ)).restrict (Set.Icc 0 1)) :=
    ((((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).norm).comp
      hT).continuousOn.integrableOn_compact isCompact_Icc
  have hlint := affine_cube_oscillation_le A c f hf
  rw [unitCubeVolume_eq] at hlint
  exact (integral_abs_sub_abs_integral_le_pairwise hg).trans
    (pairwise_integral_le_sum_of_lintegral_bound hg _ hF (fun i x => norm_nonneg _) hlint)

/-- **L1 Poincaré inequality on the unit cube.** -/
theorem cube_poincare {n : ℕ} (g : (Fin n → ℝ) → ℝ) (hg : ContDiff ℝ 1 g) :
    (∫ t in Set.Icc (0 : Fin n → ℝ) 1, |g t|) - |∫ t in Set.Icc (0 : Fin n → ℝ) 1, g t| ≤
      ∑ i : Fin n, ∫ t in Set.Icc (0 : Fin n → ℝ) 1, ‖fderiv ℝ g t (Pi.single i 1)‖ := by
  simpa using affine_cube_poincare (ContinuousLinearMap.id ℝ (Fin n → ℝ)) 0 g hg

end Submission.Obl.k4_affine_cube_directional_poincare
