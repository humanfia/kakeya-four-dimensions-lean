import Submission.Obl.k4_remainder_pure_profile_normalization.Normalization.NormDensityFormula

namespace Submission.Obl.k4_remainder_pure_profile_normalization.Normalization
open MeasureTheory
open scoped ENNReal

namespace Frame
variable (F : Frame)

/-- The observation-base Jacobian contains exactly one time-block factor. -/
theorem inverse_observation_jacobian (hq : 0 < F.q) :
    |F.obsMatrix.det|⁻¹ = F.q * |F.D.det| := by
  rw [F.det_obsMatrix, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  simp only [abs_mul, abs_inv, abs_of_pos hq, mul_inv_rev, inv_inv, mul_comm]

/-- Conditioning the prior and changing the time coordinate cancel the time
factor in the density, leaving the spatial Jacobian divided by the full prior. -/
theorem normalized_density_factor (hq : 0 < F.q) {a : ENNReal}
    (ha : a ≠ ∞) (hapos : 0 < a.toReal) :
    (a * ENNReal.ofReal F.q)⁻¹ * ENNReal.ofReal |F.obsMatrix.det|⁻¹ =
      ENNReal.ofReal (|F.D.det| / a.toReal) := by
  rw [F.inverse_observation_jacobian hq]
  conv_lhs => arg 1; arg 1; arg 1; rw [← ENNReal.ofReal_toReal ha]
  rw [← ENNReal.ofReal_mul hapos.le, ← ENNReal.ofReal_inv_of_pos (mul_pos hapos hq),
    ← ENNReal.ofReal_mul (inv_pos.mpr (mul_pos hapos hq)).le]
  congr 1
  field_simp

/-- The density transport formula in its final, time-independent form. -/
theorem normalized_obs_density_ratio (hq : 0 < F.q) (hD : IsUnit F.D.det)
    (ν : Measure Trajectory) [IsFiniteMeasure ν] {A₀ : Set Trajectory} {E : Set Incidence}
    (hA : MeasurableSet A₀) (hE : MeasurableSet E)
    (hsub : ∀ p ∈ E, p.1 ∈ A₀ ∧ p.2 ∈ Set.Icc F.t₀ (F.t₀ + F.q))
    (ha : 0 < (ν A₀).toReal) (B δ a : ℝ) (hδ : δ ≠ 0)
    (d : EuclideanSpace ℝ (Fin 3) × ℤ → ENNReal) (hd : Measurable d)
    (hlaw : ((ν.prod volume).restrict E).map (obs B (δ * a)) =
      (volume.prod Measure.count).withDensity d) :
    ((((ν A₀)⁻¹ • (ν.restrict A₀).map F.normTraj).prod volume).restrict
      (F.normEvent A₀ E)).map (obs (B / δ) a) =
      (volume.prod Measure.count).withDensity (fun z =>
        ENNReal.ofReal (|F.D.det| / (ν A₀).toReal) *
          d ((F.obsEquiv hq.ne' hD).symm z)) := by
  rw [F.normalized_obs_density hq hD ν hA hE hsub B δ a hδ d hd hlaw]
  congr 1
  funext z
  rw [← mul_assoc, F.normalized_density_factor hq (measure_ne_top _ _) ha]

/-- A fixed measurable version of the transported density. -/
noncomputable def transportedDensity (hq : F.q ≠ 0) (hD : IsUnit F.D.det)
    (prior : ℝ) (d : EuclideanSpace ℝ (Fin 3) × ℤ → ENNReal) :
    EuclideanSpace ℝ (Fin 3) × ℤ → ENNReal :=
  fun z => ENNReal.ofReal (|F.D.det| / prior) * d ((F.obsEquiv hq hD).symm z)

theorem measurable_transportedDensity (hq : F.q ≠ 0) (hD : IsUnit F.D.det)
    (prior : ℝ) {d : EuclideanSpace ℝ (Fin 3) × ℤ → ENNReal} (hd : Measurable d) :
    Measurable (F.transportedDensity hq hD prior d) :=
  measurable_const.mul (hd.comp (F.obsEquiv hq hD).symm.measurable)

/-- Sampling the transformed density at a normalized incidence removes the
observation coordinate change exactly. -/
theorem transportedDensity_observed (hq : F.q ≠ 0) (hD : IsUnit F.D.det)
    (prior B δ a : ℝ) (hδ : δ ≠ 0)
    (d : EuclideanSpace ℝ (Fin 3) × ℤ → ENNReal) (p : Incidence) :
    F.transportedDensity hq hD prior d (obs (B / δ) a (F.normInc p)) =
      ENNReal.ofReal (|F.D.det| / prior) * d (obs B (δ * a) p) := by
  rw [transportedDensity, F.obs_normInc hq B δ a hδ]
  change _ * d ((F.obsEquiv hq hD).symm ((F.obsEquiv hq hD) (obs B (δ * a) p))) = _
  rw [MeasurableEquiv.symm_apply_apply]

end Frame
end Submission.Obl.k4_remainder_pure_profile_normalization.Normalization
