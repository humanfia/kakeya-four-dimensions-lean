import Submission.Obl.k4_remainder_pure_profile_normalization.NormalizeSamples
import Submission.Lib.K4Homogenization.NativeDensityBounds
import Submission.Obl.k4_scalar_marked_coefficient_smoothing.RawCeiling

namespace Submission.Obl.k4_remainder_pure_profile_normalization
open MeasureTheory Filter
open Submission.Lib.K4Homogenization

noncomputable def jointObs (B a u : ℝ) (z : Incidence) : JointObservation :=
  (obs B a z, fun j : Fin 2 => ⌊v z.1 j / u⌋)

theorem measurable_obs (B a : ℝ) : Measurable (obs B a) := by
  unfold obs x
  fun_prop

theorem measurable_jointObs (B a u : ℝ) : Measurable (jointObs B a u) := by
  unfold jointObs
  exact (measurable_obs B a).prodMk (by unfold v; fun_prop)

/-- Every measurable countable observation label has a polynomial ceiling; its
width does not enter that ceiling. -/
theorem Normalization.SampleProblem.labeled_measure_le
    {N K : ℝ} {M D W : ℕ} {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {P : Fin W → Test} {B : Fin W → ℝ}
    (hs : Normalization.SampleProblem N K M D W ω ν E P B)
    (hN : 2 ≤ N) (b : Fin W) (S : Set Incidence)
    {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    (q : Incidence → I) (hq : Measurable q) :
    ((((ν b).prod volume).restrict S).map
      (fun z => (nativeBasePoint (z.1.2, z.2), q z))) ≤
      ENNReal.ofReal (N ^ (6 * M + 4)) •
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod (Measure.count : Measure I)) := by
  obtain ⟨m, hm, c, i, A, hj, hν⟩ := hs.prior b
  have hρ : ((ν b).prod volume).restrict S ≤
      (∑ j, ENNReal.ofReal (c j) • (volume.restrict (A j)).map (fun x => (i j, x))).prod volume := by
    rw [← hν]
    exact Measure.restrict_le_self
  refine (native_dominated_observation_le (fun j => ENNReal.ofReal (c j)) i A (N ^ M)
    (fun j x hx => (hj j).2.2.2.2 x hx) _ hρ q hq).trans ?_
  intro U
  simp only [Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul' (native_ceiling_polynomial_bound c N M hN hm (fun j => (hj j).2.1)) le_rfl

/-- A pure density exists at every width, also after any event restriction. -/
theorem Normalization.SampleProblem.pure_density
    {N K : ℝ} {M D W : ℕ} {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {P : Fin W → Test} {B : Fin W → ℝ}
    (hs : Normalization.SampleProblem N K M D W ω ν E P B)
    (hN : 2 ≤ N) (b : Fin W) (S : Set Incidence) (a : ℝ) :
    ∃ g : Observation → ENNReal, Measurable g ∧
      (((ν b).prod volume).restrict S).map (obs (B b) a) =
        (volume.prod Measure.count).withDensity g ∧
      g ≤ᵐ[volume.prod Measure.count] fun _ => ENNReal.ofReal (N ^ (6 * M + 4)) := by
  have hq : Measurable (fun z : Incidence => ⌊B b * (x z.1 z.2) 3 / a⌋) := by
    unfold x
    fun_prop
  have hbound := hs.labeled_measure_le hN b S _ hq
  change (((ν b).prod volume).restrict S).map (obs (B b) a) ≤ _ at hbound
  exact ⟨_, Submission.Obl.k4_scalar_marked_coefficient_smoothing.Raw.exists_density_le
    ENNReal.ofReal_ne_top hbound⟩

/-- Joint observation densities have the same depth-independent ceiling. -/
theorem Normalization.SampleProblem.joint_density
    {N K : ℝ} {M D W : ℕ} {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {P : Fin W → Test} {B : Fin W → ℝ}
    (hs : Normalization.SampleProblem N K M D W ω ν E P B)
    (hN : 2 ≤ N) (b : Fin W) (S : Set Incidence) (a u : ℝ) :
    ∃ G : JointObservation → ENNReal, Measurable G ∧
      (((ν b).prod volume).restrict S).map (jointObs (B b) a u) =
        ((volume.prod Measure.count).prod Measure.count).withDensity G ∧
      G ≤ᵐ[(volume.prod Measure.count).prod Measure.count]
        fun _ => ENNReal.ofReal (N ^ (6 * M + 4)) := by
  obtain ⟨m, hm, c, i, A, hj, hν⟩ := hs.prior b
  have hρ : ((ν b).prod volume).restrict S ≤
      (∑ j, ENNReal.ofReal (c j) • (volume.restrict (A j)).map (fun x => (i j, x))).prod volume := by
    rw [← hν]
    exact Measure.restrict_le_self
  have hq : Measurable (fun z : Incidence => ⌊B b * (x z.1 z.2) 3 / a⌋) := by
    unfold x
    fun_prop
  have hv : Measurable (fun z : Incidence => fun j : Fin 2 => ⌊v z.1 j / u⌋) := by
    unfold v
    fun_prop
  have hbound := native_joint_observation_le (fun j => ENNReal.ofReal (c j)) i A (N ^ M)
    (fun j x hx => (hj j).2.2.2.2 x hx) _ hρ _ hq _ hv
  have hfinal : (((ν b).prod volume).restrict S).map (jointObs (B b) a u) ≤
      ENNReal.ofReal (N ^ (6 * M + 4)) •
        ((volume.prod Measure.count).prod Measure.count) := by
    refine hbound.trans ?_
    intro U
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul' (native_ceiling_polynomial_bound c N M hN hm (fun j => (hj j).2.1)) le_rfl
  exact ⟨_, Submission.Obl.k4_scalar_marked_coefficient_smoothing.Raw.exists_density_le
    ENNReal.ofReal_ne_top hfinal⟩

end Submission.Obl.k4_remainder_pure_profile_normalization
