/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/MeasuredWitnesses.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ChainFrames
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.WitnessChains

/-! Choose the literal witnesses once. Both the composed original frame
and every common measured-path law then use precisely those witnesses. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.GridPath

open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open PathMeasures

noncomputable section

def toMeasuredChain {ctx : CriticalContext} {source : MaximizingFamily ctx}
    {start : ℝ} {targets : List ℝ} (path : GridPath ctx source start targets) (i : ℕ) :
    path.LayerWitnesses i → RefinementChain (source.problem i) (path.finalFamily.problem i) :=
  match path with
  | .nil source _ => fun _ => .nil (source.problem i)
  | .cons _ _ _ _ node tail => fun w =>
      .cons w.1 (source.angular i).1 (tail.toMeasuredChain i w.2)

theorem measuredChain_frame {ctx : CriticalContext} {source : MaximizingFamily ctx}
    {start : ℝ} {targets : List ℝ} (path : GridPath ctx source start targets)
    (i : ℕ) (w : path.LayerWitnesses i) :
    (path.toMeasuredChain i w).toOriginalFrame (path.finalFamily.angular i).1 =
      path.toOriginalFrame i w := by
  induction path with
  | nil => rfl
  | cons r rs hstart hr node tail ih =>
    change (OriginalFrame.ofRefinement w.1 _).comp
      ((tail.toMeasuredChain i w.2).toOriginalFrame (tail.finalFamily.angular i).1) = _
    rw [ih w.2]
    rfl

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.GridPath
