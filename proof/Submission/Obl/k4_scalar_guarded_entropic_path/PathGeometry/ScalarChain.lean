import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ChainCuts
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ScalarFrames

/-! Every literal cut of a chosen true path retains its composed scalar
coordinate change and its full original-prior frame. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.TrueLiftChains.Chain

open MeasureTheory
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open PathMeasures

noncomputable section

/-- Compose the actual scalar normalizations, retaining the exact
cumulative depth and the full original assignments. -/
def scalarFrame {p z : Code} (chain : Chain p z) : ScalarFrame p z chain.depth :=
  match chain with
  | .nil p hp => ScalarFrame.refl p hp
  | .cons a _ _ _ _ tail =>
      (ScalarFrame.ofRefinement a.witness a.parent_exact).comp tail.scalarFrame a.parent_exact

variable {p z : Code}

theorem scalarFrame_frame (chain : Chain p z) :
    chain.scalarFrame.frame = chain.toRefinementChain.toOriginalFrame chain.final_exact := by
  induction chain with
  | nil => rfl
  | cons a hL hr hh hrelative tail ih =>
    change (OriginalFrame.ofRefinement a.witness a.parent_exact).comp
      tail.scalarFrame.frame =
        (OriginalFrame.ofRefinement a.witness a.parent_exact).comp
          (tail.toRefinementChain.toOriginalFrame tail.final_exact)
    rw [ih]

theorem scalarFrame_sample (chain : Chain p z) :
    chain.scalarFrame.frame.sample = chain.sample := by
  rw [scalarFrame_frame]
  exact chain.toRefinementChain.frame_sample chain.final_exact

/-- The original sample of every potential normalized window parent is
the same final-inner original sample of the full chosen path. -/
theorem cut_scalarFrame_sample (chain : Chain p z) (n k : ℕ) :
    (chain.initialPart n).scalarFrame.frame.sample ((chain.suffix n).sample k) =
      chain.sample k := by
  rw [scalarFrame_sample]
  exact (chain.cut_sample n k).symm

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.TrueLiftChains.Chain
