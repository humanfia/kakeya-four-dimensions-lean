import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.DensityMasks

/-! Fixed finite original pure/angular test menus, chosen separately for
each candidate parent before the common residual or entropy window. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures

open MeasureTheory Set Filter
open scoped ENNReal Topology
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_native_grid_profile_extension.Profiles

noncomputable section

structure DensityTests (p : Code) where
  pure : Finset ℝ
  angular : Finset ℝ
  tolerance : ℝ
  tolerance_pos : 0 < tolerance
  pure_valid : ∀ r ∈ pure, 0 ≤ r ∧ r ≤ L p
  angular_valid : ∀ u ∈ angular, 0 < u ∧ u ≤ U p

namespace DensityTests

variable {p : Code}

def pureBad (t : DensityTests p) (k : ℕ) : Set (Fin (W p k) × State) :=
  ⋃ r : t.pure, taggedEvent (fun g => pureException p k g r.val t.tolerance)

def angularBad (t : DensityTests p) (k : ℕ) : Set (Fin (W p k) × State) :=
  ⋃ u : t.angular, taggedEvent (fun g => angularException p k g u.val t.tolerance)

def bad (t : DensityTests p) (k : ℕ) : Set (Fin (W p k) × State) :=
  t.pureBad k ∪ t.angularBad k

theorem measurableSet_bad (t : DensityTests p) (hp : Exact p) (k : ℕ) :
    MeasurableSet (t.bad k) := by
  apply MeasurableSet.union
  · apply MeasurableSet.iUnion
    intro r
    have hr := t.pure_valid r.val r.property
    exact measurableSet_taggedEvent _
      (fun g => measurableSet_pureException hp k g hr.1 hr.2 t.tolerance)
  · apply MeasurableSet.iUnion
    intro u
    have hu := t.angular_valid u.val u.property
    exact measurableSet_taggedEvent _
      (fun g => measurableSet_angularException hp k g hu.1 hu.2 t.tolerance)

/-- All requested original density exceptions cost power-small mass. -/
theorem bad_powerSmall (t : DensityTests p) (hp : Exact p) :
    IsPowerSmall (N p) (fun k => worldMixture p k (t.bad k)) := by
  have hpure : IsPowerSmall (N p) (fun k => worldMixture p k (t.pureBad k)) := by
    have hsmall (r : t.pure) : IsPowerSmall (N p) (fun k => worldMixture p k
        (taggedEvent (fun g => pureException p k g r.val t.tolerance))) :=
      pureException_powerSmall hp (t.pure_valid r.val r.property).1
        (t.pure_valid r.val r.property).2 t.tolerance_pos
    simpa only [pureBad, Finset.mem_univ, iUnion_true] using
      powerSmall_finite_union (N p) hp.1.2.1 (worldMixture p) _ hsmall Finset.univ
  have hang : IsPowerSmall (N p) (fun k => worldMixture p k (t.angularBad k)) := by
    have hsmall (u : t.angular) : IsPowerSmall (N p) (fun k => worldMixture p k
        (taggedEvent (fun g => angularException p k g u.val t.tolerance))) :=
      angularException_powerSmall hp (t.angular_valid u.val u.property).1
        (t.angular_valid u.val u.property).2 t.tolerance_pos
    simpa only [angularBad, Finset.mem_univ, iUnion_true] using
      powerSmall_finite_union (N p) hp.1.2.1 (worldMixture p) _ hsmall Finset.univ
  apply (hpure.add hp.1.2.1 hang).mono
  exact Eventually.of_forall fun k => measure_union_le _ _

theorem pure_subset_bad (t : DensityTests p) (k : ℕ) (r : ℝ) (hr : r ∈ t.pure) :
    taggedEvent (fun g => pureException p k g r t.tolerance) ⊆ t.bad k := by
  intro z hz
  exact Or.inl (mem_iUnion.mpr ⟨⟨r, hr⟩, hz⟩)

theorem angular_subset_bad (t : DensityTests p) (k : ℕ) (u : ℝ) (hu : u ∈ t.angular) :
    taggedEvent (fun g => angularException p k g u t.tolerance) ⊆ t.bad k := by
  intro z hz
  exact Or.inr (mem_iUnion.mpr ⟨⟨u, hu⟩, hz⟩)

end DensityTests

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures
