/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/ChainFrames.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.OriginalFrame
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.MeasuredPaths
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ChainBudgets

/-! The actual witnesses used by the measured path also supply its full
original assignment frame. The common measure and the geometric provenance
therefore use the same sample maps and the same actual budget product. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures.RefinementChain

open MeasureTheory
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

def toOriginalFrame {p z : Code} (chain : RefinementChain p z) (hz : Exact z) :
    OriginalFrame p z :=
  match chain with
  | .nil p => OriginalFrame.refl p hz
  | .cons w hp tail => (OriginalFrame.ofRefinement w hp).comp (tail.toOriginalFrame hz)

theorem frame_sample {p z : Code} (chain : RefinementChain p z) (hz : Exact z) :
    (chain.toOriginalFrame hz).sample = chain.sample := by
  induction chain with
  | nil => rfl
  | cons w hp tail ih =>
    change w.sample ∘ (tail.toOriginalFrame hz).sample = w.sample ∘ tail.sample
    rw [ih hz]

theorem frame_normalizer {p z : Code} (chain : RefinementChain p z) (hz : Exact z) (k : ℕ) :
    (chain.toOriginalFrame hz).normalizer k = chain.budget k := by
  induction chain with
  | nil => rfl
  | cons w hp tail ih =>
    change normalizer w ((tail.toOriginalFrame hz).sample k) *
      (tail.toOriginalFrame hz).normalizer k = normalizer w (tail.sample k) * tail.budget k
    rw [tail.frame_sample hz, ih hz]

/-- The measured product budget is exactly the sum of the composed
ORIGINAL full-prior assignment budgets, with actual duration products. -/
theorem original_assignmentBudget_eq {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (k : ℕ) :
    (∑ i, ω p ((chain.toOriginalFrame hz).sample k) ((chain.toOriginalFrame hz).world k i) *
      (chain.toOriginalFrame hz).duration k *
        (ν p ((chain.toOriginalFrame hz).sample k) ((chain.toOriginalFrame hz).world k i)
          ((chain.toOriginalFrame hz).assignment k i)).toReal) = chain.budget k :=
  ((chain.toOriginalFrame hz).normalizer_eq_original_budget hz k).symm.trans
    (chain.frame_normalizer hz k)

theorem original_assignmentBudget_floor {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (k : ℕ) :
    N z k ^ (-chain.loss k) ≤
      ∑ i, ω p ((chain.toOriginalFrame hz).sample k) ((chain.toOriginalFrame hz).world k i) *
        (chain.toOriginalFrame hz).duration k *
          (ν p ((chain.toOriginalFrame hz).sample k) ((chain.toOriginalFrame hz).world k i)
            ((chain.toOriginalFrame hz).assignment k i)).toReal := by
  rw [chain.original_assignmentBudget_eq hz k]
  exact chain.budget_floor hz k

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures.RefinementChain
