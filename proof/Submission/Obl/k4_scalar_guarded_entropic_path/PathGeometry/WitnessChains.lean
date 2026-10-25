/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/WitnessChains.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.OriginalFrame
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.FinitePaths

/-!
Choose literal witnesses for every finite path layer and compose their
sample maps, full-prior assignments, selected laws and original weights.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.GridPath

open Filter
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

/-- The data of every literal normalization, retained at every layer. -/
def LayerWitnesses {ctx : CriticalContext} {source : MaximizingFamily ctx} {start : ℝ}
    {targets : List ℝ} (path : GridPath ctx source start targets) (i : ℕ) : Type :=
  match path with
  | .nil _ _ => PUnit
  | .cons _ _ _ _ node tail =>
      RefinementWitness (source.problem i) (node.remaining.problem i)
        (node.depth i) (node.depth i) (node.cost i) × tail.LayerWitnesses i

variable {ctx : CriticalContext} {source : MaximizingFamily ctx}
  {start : ℝ} {targets : List ℝ}

/-- The finite eventual layer laws contain all the actual data needed for
simultaneous original-law provenance. -/
theorem nonempty_layerWitnesses (path : GridPath ctx source start targets)
    (i : ℕ) (hi : path.AllLayers i) : Nonempty (path.LayerWitnesses i) := by
  induction path with
  | nil => exact ⟨PUnit.unit⟩
  | cons r rs hstart hr node tail ih =>
    obtain ⟨w⟩ := refinement_iff_nonempty_witness.1 hi.1.refinement
    obtain ⟨rest⟩ := ih hi.2
    exact ⟨w, rest⟩

/-- A concrete finite chain composes to one original-law frame. Its prior
is normalized by the original full assignment, with the selected masks
appearing only in the separately transported incidence law. -/
noncomputable def toOriginalFrame {ctx : CriticalContext} {source : MaximizingFamily ctx}
    {start : ℝ} {targets : List ℝ} (path : GridPath ctx source start targets) (i : ℕ) :
    path.LayerWitnesses i → OriginalFrame (source.problem i) (path.finalFamily.problem i) :=
  match path with
  | .nil source _ => fun _ => OriginalFrame.refl (source.problem i) (source.angular i).1
  | .cons _ _ _ _ node tail => fun w =>
      (OriginalFrame.ofRefinement w.1 (source.angular i).1).comp (tail.toOriginalFrame i w.2)

/-- One actual original-world frame exists on the common eventual tail
of all the finite layers. -/
theorem eventually_originalFrames (path : GridPath ctx source start targets) :
    ∀ᶠ i in atTop,
      Nonempty (OriginalFrame (source.problem i) (path.finalFamily.problem i)) := by
  filter_upwards [path.eventually_allLayers] with i hi
  obtain ⟨w⟩ := path.nonempty_layerWitnesses i hi
  exact ⟨path.toOriginalFrame i w⟩

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.GridPath
