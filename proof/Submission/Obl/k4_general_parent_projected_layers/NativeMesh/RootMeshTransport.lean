/- Adapted from this LOT tree o222, session x0774, commit 109e510d,
   Submission/Obl/k4_projected_parent_contact_reduction/RootMeshTransport.lean.
   Existing source attributions are retained below. Accepted mesh-saturation
   results are imported from Submission.Lib.K4AffineMeshCaps.Saturation. -/
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.RootMeshControl

/-! Mesh laws are unchanged under measurable maps fixing the base point. -/

namespace Submission.Obl.k4_general_parent_projected_layers.NativeMesh

open Submission.Lib.K4AffineMeshCaps

open MeasureTheory Set
open Submission.Obl.k4_stable_native_signal_oscillation (erBase)

theorem measurable_rootBaseCoordinates : Measurable rootBaseCoordinates := by
  unfold rootBaseCoordinates erBase
  fun_prop

theorem rootBaseCoordinates_of_base_preserving (f : EuclideanSpace ℝ (Fin 4) →
    EuclideanSpace ℝ (Fin 4)) (hbase : ∀ p, erBase (f p) = erBase p) (p) :
    rootBaseCoordinates (f p) = rootBaseCoordinates p := by
  ext i
  change erBase (f p) i = erBase p i
  rw [hbase]

theorem RootBaseSmall.map {μ : Measure (EuclideanSpace ℝ (Fin 4))}
    (hsmall : RootBaseSmall μ) (f : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4))
    (hf : Measurable f) (hbase : ∀ p, erBase (f p) = erBase p) :
    RootBaseSmall (Measure.map f μ) := by
  apply (ae_map_iff hf.aemeasurable
    (measurableSet_Icc.preimage measurable_rootBaseCoordinates)).mpr
  filter_upwards [hsmall] with p hp
  simpa only [rootBaseCoordinates_of_base_preserving f hbase p] using hp

theorem RootMeshCap.map {μ : Measure (EuclideanSpace ℝ (Fin 4))} {K delta : ℝ}
    (hcap : RootMeshCap μ K delta)
    (f : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4))
    (hf : Measurable f) (hbase : ∀ p, erBase (f p) = erBase p) :
    RootMeshCap (Measure.map f μ) K delta := by
  intro q
  have hm : Measurable (fun p => baseMesh delta (rootBaseCoordinates p)) :=
    (measurable_baseMesh delta).comp measurable_rootBaseCoordinates
  have hs : MeasurableSet {p | baseMesh delta (rootBaseCoordinates p) = q} :=
    measurableSet_eq_fun hm measurable_const
  rw [Measure.map_apply hf hs]
  change μ {p | baseMesh delta (rootBaseCoordinates (f p)) = q} ≤ _
  simpa only [rootBaseCoordinates_of_base_preserving f hbase] using hcap q

end Submission.Obl.k4_general_parent_projected_layers.NativeMesh
