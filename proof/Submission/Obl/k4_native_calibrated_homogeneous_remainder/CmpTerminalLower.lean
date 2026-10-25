import Submission.Obl.k4_native_calibrated_homogeneous_remainder.CmpPure
import Submission.Obl.k4_native_grid_profile_extension.CountedRefinement

/-! The new terminal density dominates the old restricted fine density.
Only the exact affine transport and discrete coarsening are used. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder.Cmp

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_finite_width_output_exclusion (x y v δ obs)
open Submission.Obl.k4_native_grid_profile_extension (observation_refinement_density_le)

theorem chart_fine_density_lower (ν : Measure Line) [IsFiniteMeasure ν] (A : Set Line)
    (θ : Line ≃ᵐ Line) {D t₀ : ℝ} (hD : 0 < D) {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0) (hνA : ν A ≠ 0)
    (hy : ∀ l t, y (θ l) t =
      Matrix.toEuclideanLin Q⁻¹ (y l (t₀ + t / D) - c - (t₀ + t / D) • u))
    (hx : ∀ l t, x (θ l) t 3 = x l (t₀ + t / D) 3)
    {E : Set Point} (hE : MeasurableSet E) (B : ℝ) {ρ σ f : ℝ}
    (hρ : ρ ≠ 0) (hσ : σ ≠ 0) (n : ℕ) (hwidth : ρ * σ = (n : ℝ) * f)
    {H G : EuclideanSpace ℝ (Fin 3) × ℤ → ENNReal} (hH : Measurable H) (hG : Measurable G)
    (hHlaw : Measure.map (obs B f)
      (((ν.restrict A).prod volume).restrict (incEquiv θ D t₀ hD ⁻¹' E)) =
        obsRef.withDensity H)
    (hGlaw : Measure.map (obs (B / ρ) σ)
      ((((ν A)⁻¹ • Measure.map θ (ν.restrict A)).prod volume).restrict E) =
        obsRef.withDensity G) :
    ∀ᵐ z ∂((((ν A)⁻¹ • Measure.map θ (ν.restrict A)).prod volume).restrict E),
      (ENNReal.ofReal |Q.det| / ν A) * H (obs B f ((incEquiv θ D t₀ hD).symm z)) ≤
        G (obs (B / ρ) σ z) := by
  set e := incEquiv θ D t₀ hD
  set μS := ((ν.restrict A).prod volume).restrict (e ⁻¹' E)
  set Jf := obs B f
  set Jn := obs B (ρ * σ)
  set cc := ENNReal.ofReal |Q.det| / ν A
  have hcc : cc ≠ 0 :=
    (ENNReal.div_pos_iff.mpr ⟨(ENNReal.ofReal_pos.mpr (abs_pos.mpr hQ)).ne', measure_ne_top ν A⟩).ne'
  have hJf : Measurable Jf := measurable_obs _ _
  have hJn : Measurable Jn := measurable_obs _ _
  have hcoarse : ∀ z : Point, ((Jf z).1, (Jf z).2 / (n : ℤ)) = Jn z := by
    intro z
    apply Prod.ext
    · rfl
    · change ⌊B * x z.1 z.2 3 / f⌋ / (n : ℤ) =
        ⌊B * x z.1 z.2 3 / (ρ * σ)⌋
      rw [hwidth, show B * x z.1 z.2 3 / ((n : ℝ) * f) =
        (B * x z.1 z.2 3 / f) / n by ring, Int.floor_div_natCast]
  have hcomm : ∀ z, obs (B / ρ) σ (e z) = (chartAff D t₀ c u Q (Jn z).1, (Jn z).2) :=
    obs_incEquiv hD hy hx hρ hσ
  have hlawG := pullback_law ν A θ hD hQ hνA hE (obs (B / ρ) σ)
    (measurable_obs _ _) Jn hJn hcomm hG hGlaw
  have hfine : Measure.map Jf (cc • μS) = obsRef.withDensity (fun o => cc * H o) := by
    rw [Measure.map_smul _ hJf.aemeasurable, hHlaw, smul_withDensity_eq _ _ hH]
  have hcoarselaw : Measure.map (fun z => ((Jf z).1, (Jf z).2 / (n : ℤ))) (cc • μS) =
      obsRef.withDensity (fun o => G (chartAff D t₀ c u Q o.1, o.2)) := by
    simp_rw [hcoarse]
    rw [Measure.map_smul _ hJn.aemeasurable]
    exact hlawG
  have hcomp := observation_refinement_density_le (cc • μS) volume Jf hJf
    (fun m : ℤ => m / (n : ℤ))
    (fun o => G (chartAff D t₀ c u Q o.1, o.2)) (fun o => cc * H o)
    (hG.comp ((measurable_chartAff D t₀ c u Q).prodMap measurable_id))
    (measurable_const.mul hH) hcoarselaw hfine
  have hcomp' := (Measure.ae_ennreal_smul_measure_iff hcc).mp hcomp
  rw [selected_law_transport ν A θ hD hE]
  refine Measure.ae_smul_measure ?_ (ENNReal.ofReal D / ν A)
  have hP : MeasurableSet {z : Point |
      cc * H (Jf (e.symm z)) ≤ G (obs (B / ρ) σ z)} :=
    measurableSet_le (measurable_const.mul (hH.comp (hJf.comp e.symm.measurable)))
      (hG.comp (measurable_obs _ _))
  apply (ae_map_iff e.measurable.aemeasurable hP).mpr
  filter_upwards [hcomp'] with z hz
  simpa only [e.symm_apply_apply, hcomm, ← hcoarse z] using hz

end Submission.Obl.k4_native_calibrated_homogeneous_remainder.Cmp
