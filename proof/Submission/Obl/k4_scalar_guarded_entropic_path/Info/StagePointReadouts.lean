import Submission.Obl.k4_scalar_guarded_entropic_path.Info.PointLayoutGaps
import Submission.Obl.k4_scalar_guarded_entropic_path.Info.FiniteRecordRanges
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.OuterStage

/-! Literal candidate indices and future-world conditioning for the
actual common stage menu. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path

open MeasureTheory
open PathGeometry PathGeometry.PathMeasures PathGeometry.PathNodes TrueLiftChains
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

namespace StageLayout

variable {stage : ℕ} {R δ κ η : ℝ}

def candidateIndex (q : StageLayout stage R δ κ η) (a : Fin q.L) :
    Fin (q.targets.length + 1) :=
  ⟨a.val + 1, by rw [q.targets_length]; have := q.coarse_lt; omega⟩

end StageLayout

namespace PathGeometry.PathNodes.TrueGridPath

variable {ctx : CriticalContext} {source : MaximizingFamily ctx}
  {start : ℝ} {targets : List ℝ}

def stageViewsReadouts (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (hl : path.forget.AllLayers i)
    (a : Fin (targets.length + 1)) : (path.stageViews i certs hl a).Readouts :=
  path.viewAtReadouts i certs hl (.nil _ (source.angular i).1) a.val

theorem stage_candidate_count {stage : ℕ} {R δ : ℝ}
    (q : StageLayout stage R δ ctx.κ ctx.η) (path : TrueGridPath ctx source 0 q.targets)
    (i : ℕ) (certs : path.Certificates i) (hl : path.forget.AllLayers i) (a : Fin q.L) :
    q.C ≤ (path.stageViews i certs hl (q.candidateIndex a)).count := by
  change q.C ≤ (path.viewAt i certs hl (.nil _ (source.angular i).1) (a.val + 1)).count
  rw [path.viewAt_count, q.targets_length]
  omega

end PathGeometry.PathNodes.TrueGridPath

namespace Info

/-- The complete candidate history range becomes the exact future
original-world range used by exists_window_info.hs. -/
theorem stage_point_range_given_future
    {ctx : CriticalContext} {source : MaximizingFamily ctx}
    {stage : ℕ} {R δ : ℝ} (q : StageLayout stage R δ ctx.κ ctx.η)
    (path : TrueGridPath ctx source 0 q.targets) (i : ℕ)
    (certs : path.Certificates i) (hl : path.forget.AllLayers i) (a : Fin q.L) (k : ℕ)
    (P : Measure (Fin (W (path.forget.finalFamily.problem i) k) × State))
    (record : (Fin (W (path.forget.finalFamily.problem i) k) × State) → ℕ) (budget : ℕ)
    (h : FiniteRangeGiven P record
      (fun z => (path.stageViews i certs hl (q.candidateIndex a)).suffixChain.history k q.C z.1)
      budget) :
    FiniteRangeGiven P record
      (fun z => (path.viewAt i certs hl (.nil _ (source.angular i).1)
        (a.val + 1 + q.C)).suffixChain.world k z.1) budget :=
  finiteRangeGiven_viewAt_future path i certs hl (.nil _ (source.angular i).1)
    (a.val + 1) k q.C P record budget h

end Info

end

end Submission.Obl.k4_scalar_guarded_entropic_path
