import Submission.Obl.k4_native_shear_source_transport.NativeLaw
import Submission.Obl.k4_dyadic_crop_worlds.BooleanFormat
import Submission.Obl.k4_dyadic_crop_affine_laws.Framework.IncidenceTransport
import Submission.Obl.k4_finite_width_output_exclusion.Models

/-! Exact observation densities from the full finite prior representation.
The accepted native pushforward formulas apply without the native height and
mass bounds included in o095's larger frozen interface. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_native_shear_source_transport
open Submission.Obl.k4_dyadic_crop_worlds (PriorFormat)
open Submission.Obl.k4_dyadic_crop_affine_laws.Framework
open Submission.Obl.k4_finite_width_output_exclusion (obs v x)

/-- Every measurable selection of a formatted prior has a joint native density. -/
theorem joint_density_of_priorFormat {R : ℝ} {D : ℕ}
    {ν : Measure (ℕ × (Fin 6 → ℝ))} (hprior : PriorFormat R D ν)
    (E : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (hE : MeasurableSet E) (a b : ℝ) :
    ∃ G : ObsSpace → ENNReal, Measurable G ∧
      Measure.map (obsMap a b) ((ν.prod volume).restrict E) = refMeasure.withDensity G := by
  obtain ⟨m, -, c, i, A, hA, hν⟩ := hprior
  have hAm : ∀ j, MeasurableSet (A j) := fun j => (hA j).2.2.2.1.measurableSet
  refine ⟨_, measurable_labelDensity volume (measurable_hidLabel a) (measurable_velLabel b)
    ((measurable_nativeDensity c i hAm hE).comp baseFiberEquiv.symm.measurable), ?_⟩
  rw [map_obs_native a b c i hAm hν hE,
    map_shObs_withDensity a b (measurable_nativeDensity c i hAm hE)]

/-- Derivative units may be built into the hidden observation without changing
absolute continuity or requiring a bound for the hidden coordinate. -/
theorem scaled_joint_density_of_priorFormat {R : ℝ} {D : ℕ}
    {ν : Measure (ℕ × (Fin 6 → ℝ))} (hprior : PriorFormat R D ν)
    (E : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (hE : MeasurableSet E) (B a b : ℝ) :
    ∃ G : ObsSpace → ENNReal, Measurable G ∧
      Measure.map (fun p => (obs B a p, fun j : Fin 2 => ⌊v p.1 j / b⌋))
        ((ν.prod volume).restrict E) = refMeasure.withDensity G := by
  obtain ⟨G, hG, hlaw⟩ := joint_density_of_priorFormat hprior E hE (a / B) b
  refine ⟨G, hG, ?_⟩
  have hobs : (fun p => (obs B a p, fun j : Fin 2 => ⌊v p.1 j / b⌋)) = obsMap (a / B) b := by
    funext p
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · change ⌊B * (p.1.2 2 + p.2 * p.1.2 5) / a⌋ =
          ⌊(p.1.2 2 + p.2 * p.1.2 5) / (a / B)⌋
        congr 1
        rw [div_div_eq_mul_div]
        ring
    · rfl
  rw [hobs]
  exact hlaw

/-- The continuous base law is absolutely continuous, and adding any counted
hidden observation therefore gives a pure density. -/
theorem pure_density_of_priorFormat {R : ℝ} {D : ℕ}
    {ν : Measure (ℕ × (Fin 6 → ℝ))} [IsProbabilityMeasure ν]
    (hprior : PriorFormat R D ν)
    (E : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (hE : MeasurableSet E)
    (hsub : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) (B a : ℝ) :
    ∃ g : EuclideanSpace ℝ (Fin 3) × ℤ → ENNReal, Measurable g ∧
      Measure.map (obs B a) ((ν.prod volume).restrict E) =
        (volume.prod Measure.count).withDensity g := by
  let μ := ((ν.prod volume).restrict E)
  have : IsFiniteMeasure μ := finite_selected_incidence ν E hsub
  obtain ⟨G, hG, hlaw⟩ := scaled_joint_density_of_priorFormat hprior E hE B a 1
  have hobs : Measurable (obs B a) := by
    unfold obs x
    apply Measurable.prodMk
    · apply (WithLp.measurable_toLp 2 (Fin 3 → ℝ)).comp
      apply Measurable.of_eval
      intro i
      fin_cases i <;> fun_prop
    · fun_prop
  have hj : Measurable (fun p => (obs B a p, fun j : Fin 2 => ⌊v p.1 j / (1 : ℝ)⌋)) := by
    refine hobs.prodMk ?_
    apply Measurable.of_eval
    intro j
    unfold v
    fin_cases j <;> fun_prop
  have hac : Measure.map (fun p => (obs B a p, fun j : Fin 2 => ⌊v p.1 j / (1 : ℝ)⌋)) μ ≪
      (volume.prod Measure.count).prod Measure.count := by
    rw [hlaw]
    exact withDensity_absolutelyContinuous _ _
  have hbase := base_marginal_ac_of_joint μ volume _ hj hac
  exact exists_counted_observation_density μ volume (obs B a) hobs hbase

end Submission.Obl.k4_native_calibrated_homogeneous_remainder
