import Submission.Obl.k4_native_calibrated_homogeneous_remainder.Models
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.DensityExistence
import Submission.Obl.k4_profile_density_bounds.Support

/-! Observation laws and elementary mass facts for a raw native family. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_finite_width_output_exclusion
open Submission.Obl.k4_dyadic_crop_worlds (PriorFormat)

theorem measurable_nativeObs (B a : ℝ) : Measurable (obs B a) := by
  unfold obs x
  apply Measurable.prodMk
  · apply (WithLp.measurable_toLp 2 (Fin 3 → ℝ)).comp
    apply Measurable.of_eval
    intro i
    fin_cases i <;> fun_prop
  · fun_prop

theorem measurable_velocityLabel (b : ℝ) :
    Measurable (fun p : Incidence => fun j : Fin 2 => ⌊v p.1 j / b⌋) := by
  apply Measurable.of_eval
  intro j
  unfold v
  fin_cases j <;> fun_prop

theorem RawValid.probability {p : Data} (hp : RawValid p) (k : ℕ) (b : Fin (p.W k)) :
    IsProbabilityMeasure (p.ν k b) := by
  obtain ⟨-, -, -, -, -, -, -, -, M, D, hfmt⟩ := hp
  exact ((hfmt k).2.2.2.1 b).1

theorem RawValid.selected_mass_le_one {p : Data} (hp : RawValid p)
    (k : ℕ) (b : Fin (p.W k)) : selected p k b univ ≤ 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, M, D, hfmt⟩ := hp
  letI := ((hfmt k).2.2.2.1 b).1
  have hsub := ((hfmt k).2.2.2.1 b).2.2.2.2.2.2.2.2.1
  change ((p.ν k b).prod volume).restrict (p.E k b) univ ≤ 1
  rw [Measure.restrict_apply_univ]
  calc
    _ ≤ ((p.ν k b).prod volume) (univ ×ˢ Icc (0 : ℝ) 1) := measure_mono hsub
    _ = 1 := by rw [Measure.prod_prod]; simp

theorem RawValid.unit_velocity_labels {p : Data} (hp : RawValid p)
    (k : ℕ) (b : Fin (p.W k)) :
    ∀ᵐ z ∂selected p k b, (fun j : Fin 2 => ⌊v z.1 j / (1 : ℝ)⌋) ∈
      Submission.Obl.k4_profile_density_bounds.velocityBins (p.K k) := by
  obtain ⟨-, -, hK, -, -, -, -, -, M, D, hfmt⟩ := hp
  rcases (hfmt k).2.2.2.1 b with ⟨-, -, -, -, -, -, -, -, -, -, -, hnative, -⟩
  have hvel : ∀ᵐ l ∂p.ν k b, ‖v l‖ ≤ p.K k := by
    filter_upwards [hnative] with l hl
    have hz := (hl 0 (by simp)).1
    linarith [norm_nonneg (y l 0)]
  have hsample := Submission.Obl.k4_profile_density_bounds.ae_velocity_bound
    (p.ν k b) hvel (p.E k b)
  filter_upwards [hsample] with z hz
  simpa only [div_one, Submission.Obl.k4_profile_density_bounds.velocity, v] using
    Submission.Obl.k4_profile_density_bounds.mem_velocityBins (hK.1 k) hz

theorem RawValid.pure_density_exists {p : Data} (hp : RawValid p)
    (k : ℕ) (b : Fin (p.W k)) (a : ℝ) :
    ∃ g : Observation → ENNReal, Measurable g ∧
      (selected p k b).map (obs (p.B k b) a) = (volume.prod Measure.count).withDensity g := by
  obtain ⟨-, -, -, -, -, -, -, -, M, D, hfmt⟩ := hp
  rcases (hfmt k).2.2.2.1 b with
    ⟨hν, -, -, -, -, -, hprior, hEm, hEt, -, -, -, -⟩
  letI := hν
  exact pure_density_of_priorFormat (show PriorFormat (p.N k ^ M) D (p.ν k b) from hprior)
    (p.E k b) hEm hEt (p.B k b) a

theorem RawValid.joint_density_exists {p : Data} (hp : RawValid p)
    (k : ℕ) (b : Fin (p.W k)) (a u : ℝ) :
    ∃ G : JointObservation → ENNReal, Measurable G ∧
      (selected p k b).map (fun z => (obs (p.B k b) a z,
        fun j : Fin 2 => ⌊v z.1 j / u⌋)) =
          ((volume.prod Measure.count).prod Measure.count).withDensity G := by
  obtain ⟨-, -, -, -, -, -, -, -, M, D, hfmt⟩ := hp
  rcases (hfmt k).2.2.2.1 b with ⟨-, -, -, -, -, -, hprior, hEm, -⟩
  exact scaled_joint_density_of_priorFormat
    (show PriorFormat (p.N k ^ M) D (p.ν k b) from hprior)
    (p.E k b) hEm (p.B k b) a u

noncomputable def pureDensity {p : Data} (hp : RawValid p) (k : ℕ) (b : Fin (p.W k))
    (a : ℝ) : Observation → ENNReal := (hp.pure_density_exists k b a).choose

theorem pureDensity_spec {p : Data} (hp : RawValid p) (k : ℕ) (b : Fin (p.W k)) (a : ℝ) :
    Measurable (pureDensity hp k b a) ∧
      (selected p k b).map (obs (p.B k b) a) =
        (volume.prod Measure.count).withDensity (pureDensity hp k b a) :=
  (hp.pure_density_exists k b a).choose_spec

noncomputable def jointDensity {p : Data} (hp : RawValid p) (k : ℕ) (b : Fin (p.W k))
    (a u : ℝ) : JointObservation → ENNReal := (hp.joint_density_exists k b a u).choose

theorem jointDensity_spec {p : Data} (hp : RawValid p) (k : ℕ) (b : Fin (p.W k)) (a u : ℝ) :
    Measurable (jointDensity hp k b a u) ∧
      (selected p k b).map (fun z => (obs (p.B k b) a z,
        fun j : Fin 2 => ⌊v z.1 j / u⌋)) =
          ((volume.prod Measure.count).prod Measure.count).withDensity (jointDensity hp k b a u) :=
  (hp.joint_density_exists k b a u).choose_spec

end Submission.Obl.k4_native_calibrated_homogeneous_remainder
