/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/TruePathSupport.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.TrueGridPath
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.TrueAtlasSupport

/-! All full source TRUE pieces hold on a common measurable set of full
final-mixture measure, using the identical retained path witnesses. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.TrueGridPath

open MeasureTheory Set Filter PathMeasures
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

variable {ctx : CriticalContext} {source : MaximizingFamily ctx}
  {start : ℝ} {targets : List ℝ}

def measuredChain {ctx : CriticalContext} {source : MaximizingFamily ctx}
    {start : ℝ} {targets : List ℝ} (path : TrueGridPath ctx source start targets)
    (i : ℕ) (certs : path.Certificates i) :
    RefinementChain (source.problem i) (path.forget.finalFamily.problem i) :=
  path.forget.toMeasuredChain i (path.toLayerWitnesses i certs)

/-- The full ambient true pieces at every actual local parent, tested
on the same final coordinates and composed pullback maps. -/
def ambientPathSet {ctx : CriticalContext} {source : MaximizingFamily ctx}
    {start : ℝ} {targets : List ℝ} (path : TrueGridPath ctx source start targets)
    (i : ℕ) : path.Certificates i → (k : ℕ) →
      Set (Fin (W (path.forget.finalFamily.problem i) k) × State) :=
  match path with
  | .nil _ _ => fun _ _ => univ
  | .cons _ _ _ _ _ tail => fun certs k =>
      tail.ambientPathSet i certs.2 k ∩
        (tail.measuredChain i certs.2).pullback k ⁻¹'
          certs.1.ambientPreimage ((tail.measuredChain i certs.2).sample k)

theorem measurableSet_ambientPathSet (path : TrueGridPath ctx source start targets)
    (i : ℕ) (certs : path.Certificates i) (k : ℕ) :
    MeasurableSet (path.ambientPathSet i certs k) := by
  induction path with
  | nil => exact MeasurableSet.univ
  | cons r rs hstart hr node tail ih =>
    exact (ih certs.2).inter ((certs.1.measurableSet_ambientPreimage _).preimage
      ((tail.measuredChain i certs.2).measurable_pullback k))

/-- The existing selected path core is contained in every full true
source piece; every later mask of that core inherits the same support. -/
theorem pathSet_subset_ambient (path : TrueGridPath ctx source start targets)
    (i : ℕ) (certs : path.Certificates i) (k : ℕ) :
    (path.measuredChain i certs).pathSet k ⊆ path.ambientPathSet i certs k := by
  induction path with
  | nil => exact Subset.rfl
  | cons r rs hstart hr node tail ih =>
    intro z hz
    exact ⟨ih certs.2 hz.1, certs.1.selected_subset_ambient _ _ hz.2⟩

/-- All unchanged true source pieces simultaneously hold almost
everywhere for the final original weighted mixture. -/
theorem ambientPathSet_ae (path : TrueGridPath ctx source start targets)
    (i : ℕ) (certs : path.Certificates i) (k : ℕ) :
    ∀ᵐ z ∂worldMixture (path.forget.finalFamily.problem i) k,
      z ∈ path.ambientPathSet i certs k :=
  ((path.measuredChain i certs).pathSet_ae k).mono
    (fun _ hz => path.pathSet_subset_ambient i certs k hz)

/-- The SAME normalized probability used for every view is supported in
all the unchanged true source pieces. -/
theorem ambientPathSet_ae_normalized (path : TrueGridPath ctx source start targets)
    (i : ℕ) (certs : path.Certificates i) (k : ℕ) :
    ∀ᵐ z ∂normalizedWorldMixture (path.forget.finalFamily.problem i) k,
      z ∈ path.ambientPathSet i certs k :=
  Measure.smul_absolutelyContinuous.ae_le (path.ambientPathSet_ae i certs k)

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.TrueGridPath
