import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.TruePathSupport
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.RootTrueCharts

/-! The numerical true grid and its backward lifting chain use the same
chosen normalizations, sample maps, and common measured law. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.TrueGridPath

open MeasureTheory Filter
open scoped Topology
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open TrueLiftChains PathMeasures

noncomputable section

/-- Retain the true normalization, its absolute units, and its relative
profile law at every step of the original finite grid. -/
def trueChain {ctx : CriticalContext} {source : MaximizingFamily ctx}
    {start : ℝ} {targets : List ℝ} (path : TrueGridPath ctx source start targets)
    (i : ℕ) : path.Certificates i → path.forget.AllLayers i →
      Chain (source.problem i) (path.forget.finalFamily.problem i) :=
  match path with
  | .nil source _ => fun _ _ => .nil (source.problem i) (source.angular i).1
  | .cons _ _ _ _ _ tail => fun certs laws =>
      .cons certs.1 laws.1.remaining_length laws.1.depth_nonneg laws.1.known.1
        (fun s hs hsL => laws.1.remaining_profile s ⟨hs, hsL⟩)
        (tail.trueChain i certs.2 laws.2)

variable {ctx : CriticalContext} {source : MaximizingFamily ctx}
  {start : ℝ} {targets : List ℝ}

theorem trueChain_toRefinementChain (path : TrueGridPath ctx source start targets)
    (i : ℕ) (certs : path.Certificates i) (laws : path.forget.AllLayers i) :
    (path.trueChain i certs laws).toRefinementChain = path.measuredChain i certs := by
  induction path with
  | nil => rfl
  | cons r rs hstart hr node tail ih =>
    change RefinementChain.cons certs.1.witness _
      (tail.trueChain i certs.2 laws.2).toRefinementChain =
        RefinementChain.cons certs.1.witness _ (tail.measuredChain i certs.2)
    rw [ih certs.2 laws.2]

theorem trueChain_depth (path : TrueGridPath ctx source start targets)
    (i : ℕ) (certs : path.Certificates i) (laws : path.forget.AllLayers i) :
    (path.trueChain i certs laws).depth = path.forget.totalDepth i := by
  induction path with
  | nil => rfl
  | cons r rs hstart hr node tail ih =>
    change node.depth i + (tail.trueChain i certs.2 laws.2).depth =
      node.depth i + tail.forget.totalDepth i
    rw [ih certs.2 laws.2]

theorem trueChain_cost (path : TrueGridPath ctx source start targets)
    (i : ℕ) (certs : path.Certificates i) (laws : path.forget.AllLayers i) :
    (path.trueChain i certs laws).cost = path.forget.totalCost i := by
  induction path with
  | nil => rfl
  | cons r rs hstart hr node tail ih =>
    change node.cost i + (tail.trueChain i certs.2 laws.2).cost =
      node.cost i + tail.forget.totalCost i
    rw [ih certs.2 laws.2]

/-- Both the original numerical laws and the identical measured true
chain are available on one outer tail. -/
theorem eventually_trueChain (path : TrueGridPath ctx source start targets) :
    ∀ᶠ i in atTop,
      ∃ certs : path.Certificates i, ∃ laws : path.forget.AllLayers i,
        (path.trueChain i certs laws).toRefinementChain = path.measuredChain i certs ∧
        (path.trueChain i certs laws).depth = path.forget.totalDepth i ∧
        (path.trueChain i certs laws).cost = path.forget.totalCost i := by
  filter_upwards [path.eventually_certificates, path.forget.eventually_allLayers]
    with i hc hl
  obtain ⟨certs⟩ := hc
  exact ⟨certs, hl, path.trueChain_toRefinementChain i certs hl,
    path.trueChain_depth i certs hl, path.trueChain_cost i certs hl⟩

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.TrueGridPath
