import Submission.Obl.k4_coarsened_outer_horizon_composition.Interface
import Submission.Lib.K4Homogenization.DyadicObservations
import Submission.Obl.k4_dyadic_crop_affine_laws.Framework.CountedDensity
import Submission.Obl.k4_dyadic_crop_affine_laws.Framework.IncidenceTransport

namespace Submission.Obl.k4_coarsened_outer_horizon_composition

open MeasureTheory Set
open scoped ENNReal

abbrev Line := ℕ × (Fin 6 → ℝ)
abbrev Inc := Line × ℝ
abbrev E2 := EuclideanSpace ℝ (Fin 2)
abbrev E3 := EuclideanSpace ℝ (Fin 3)
abbrev Obs := E3 × ℤ
abbrev Joint := Obs × (Fin 2 → ℤ)

noncomputable def selected (ν : Measure Line) (E : Set Inc) : Measure Inc :=
  (ν.prod volume).restrict E

noncomputable def ang (N u : ℝ) (p : Inc) : Fin 2 → ℤ :=
  fun j => ⌊v p.1 j / δ N u⌋

noncomputable def joint (B N r u : ℝ) (p : Inc) : Joint :=
  (obs B (δ N r) p, ang N u p)

lemma measurable_x : Measurable (fun p : Inc => x p.1 p.2) := by
  unfold x
  fun_prop

lemma measurable_v : Measurable (v : Line → E2) := by
  unfold v
  fun_prop

lemma measurable_obs (B a : ℝ) : Measurable (obs B a) := by
  unfold obs x
  fun_prop

lemma measurable_ang (N u : ℝ) : Measurable (ang N u) := by
  unfold ang v
  fun_prop

lemma measurable_joint (B N r u : ℝ) : Measurable (joint B N r u) :=
  (measurable_obs _ _).prodMk (measurable_ang _ _)

lemma obs_factorization {N r s : ℝ} (hN : 1 ≤ N) (hrs : r ≤ s) (B : ℝ) :
    obs B (δ N r) =
      Submission.Lib.K4Homogenization.coarsenObservation N r s ∘ obs B (δ N s) := by
  funext p
  exact Submission.Lib.K4Homogenization.observation_factorization
    (fun p : Inc => WithLp.toLp 2 ![p.2, x p.1 p.2 1, x p.1 p.2 2])
    (fun p : Inc => B * x p.1 p.2 3) hN hrs p

/-- Adding the velocity label to the coarse pure observation preserves absolute
continuity. The chosen density is defined for every angular scale. -/
theorem exists_joint_density
    (ν : Measure Inc) [IsFiniteMeasure ν] (B N r u : ℝ)
    (g : Obs → ℝ≥0∞) (hg : Measurable g)
    (hlaw : ν.map (obs B (δ N r)) = (volume.prod Measure.count).withDensity g) :
    ∃ G : Joint → ℝ≥0∞, Measurable G ∧
      ν.map (joint B N r u) = ((volume.prod Measure.count).prod Measure.count).withDensity G := by
  apply Submission.Obl.k4_dyadic_crop_affine_laws.Framework.exists_counted_observation_density
    ν (volume.prod Measure.count) (joint B N r u) (measurable_joint _ _ _ _)
  change ν.map (obs B (δ N r)) ≪ volume.prod Measure.count
  rw [hlaw]
  exact withDensity_absolutelyContinuous _ _

end Submission.Obl.k4_coarsened_outer_horizon_composition
