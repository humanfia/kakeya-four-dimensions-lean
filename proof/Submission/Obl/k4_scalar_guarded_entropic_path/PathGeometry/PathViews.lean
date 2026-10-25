import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.UniformRootCharts
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ScalarChain

/-! A finite chosen true path supplies all candidate normalized parent
views on one final probability, with their actual original scalar frames. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry

open MeasureTheory Set Filter
open scoped ENNReal Topology
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_scalar_true_terminal_lifting (ChartW)
open TrueLiftChains PathMeasures IntermediateLiftSupport

noncomputable section

/-- One actual potential parent, with its original prefix frame and the
same final-law suffix as every other candidate in the finite path. -/
structure OriginalView (root final : Code) (D S η : ℝ) where
  parent : Code
  prefixChain : Chain root parent
  suffixChain : RefinementChain parent final
  cap_le : d parent ≤ D
  angular : Submission.Obl.k4_scalar_linear_critical_extremizers.Split.S parent = S
  range : U parent = η * L parent
  count : ℕ
  depth : Fin count → ℝ
  time : Fin count → ℝ
  complexity : ℕ
  complexity_pos : 1 ≤ complexity
  geometry : (k : ℕ) → Fin count → ChartGeometry.Geometry parent (suffixChain.sample k)
  depth_bounds : ∀ j, 0 ≤ depth j ∧ depth j < L parent
  time_nonneg : ∀ j, 0 ≤ time j
  layers : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ j : Fin count,
    ∃ P : ChartW parent complexity (depth j) (L parent) (time j + ε) ε true
        (suffixChain.sample k),
      ChartGeometry.ofChart P = geometry k j ∧
      ∀ ρ : Measure (Fin (W final k) × State), ρ ≪ worldMixture final k →
        ∀ᵐ u ∂ρ.map (suffixChain.pullback k), u ∈ chartRegion P

namespace OriginalView

variable {root final : Code} {D S η : ℝ}

def rootSample (a : OriginalView root final D S η) (k : ℕ) : ℕ :=
  a.prefixChain.sample (a.suffixChain.sample k)

def originalFrame (a : OriginalView root final D S η) :
    OriginalFrame root a.parent := a.prefixChain.scalarFrame.frame

theorem originalFrame_sample (a : OriginalView root final D S η) (k : ℕ) :
    a.originalFrame.sample (a.suffixChain.sample k) = a.rootSample k := by
  rw [originalFrame, Chain.scalarFrame_sample]
  rfl

theorem parent_exact (a : OriginalView root final D S η) : Exact a.parent :=
  a.prefixChain.final_exact

end OriginalView

namespace PathNodes.TrueGridPath

variable {ctx : CriticalContext} {source : MaximizingFamily ctx}
  {start : ℝ} {targets : List ℝ} {root : Code}

/-- Freeze one actual parent view after the outer index and chosen true
certificates have been fixed, before any inner tolerance or sample. -/
def originalView (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (hl : path.forget.AllLayers i)
    (before : Chain root (source.problem i)) :
    OriginalView root (path.forget.finalFamily.problem i) (ctx.D i) ctx.S₀ ctx.η where
  parent := source.problem i
  prefixChain := before
  suffixChain := path.measuredChain i certs
  cap_le := source.cap i
  angular := (source.angular i).2.1
  range := (source.angular i).2.2
  count := targets.length
  depth := path.prefixDepth i
  time := path.prefixCost i
  complexity := path.uniformPrefixBudget i certs
  complexity_pos := path.uniformPrefixBudget_one i certs
  geometry := path.rootGeometry i certs
  depth_bounds := path.prefixDepth_bounds i hl
  time_nonneg := path.prefixCost_nonneg i hl
  layers := by
    intro ε hε
    exact path.eventually_uniform_root_terminal_charts i certs hl ε hε

theorem originalView_rootSample (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (hl : path.forget.AllLayers i)
    (before : Chain root (source.problem i)) (k : ℕ) :
    (path.originalView i certs hl before).rootSample k =
      before.sample ((path.measuredChain i certs).sample k) := by
  rfl

/-- Retain every actual suffix parent and its ORIGINAL prefix frame. -/
def originalViews {ctx : CriticalContext} {source : MaximizingFamily ctx}
    {start : ℝ} {targets : List ℝ} {root : Code}
    (path : TrueGridPath ctx source start targets) (i : ℕ) :
    (certs : path.Certificates i) → (hl : path.forget.AllLayers i) →
    Chain root (source.problem i) →
      List (OriginalView root (path.forget.finalFamily.problem i) (ctx.D i) ctx.S₀ ctx.η) :=
  match path with
  | .nil _ _ => fun certs hl before => [originalView (.nil _ _) i certs hl before]
  | .cons r rs hstart hr node tail => fun certs hl before =>
      originalView (.cons r rs hstart hr node tail) i certs hl before ::
        tail.originalViews i certs.2 hl.2
          (before.append (.cons certs.1 hl.1.remaining_length hl.1.depth_nonneg hl.1.known.1
            (fun s hs hsL => hl.1.remaining_profile s ⟨hs, hsL⟩)
            (.nil _ (tail.trueChain i certs.2 hl.2).source_exact)))

theorem originalViews_length (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (hl : path.forget.AllLayers i)
    (before : Chain root (source.problem i)) :
    (path.originalViews i certs hl before).length = targets.length + 1 := by
  induction path with
  | nil => rfl
  | cons r rs hstart hr node tail ih =>
    change (tail.originalViews i certs.2 hl.2 _).length + 1 = rs.length + 1 + 1
    exact congrArg (fun n : ℕ => n + 1) (ih certs.2 hl.2 _)

/-- All candidate prefix frames refer to exactly the same ORIGINAL
sample, although their normalized parent sample indices differ. -/
theorem originalViews_rootSample (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (hl : path.forget.AllLayers i)
    (before : Chain root (source.problem i)) (k : ℕ)
    (a : OriginalView root (path.forget.finalFamily.problem i) (ctx.D i) ctx.S₀ ctx.η)
    (ha : a ∈ path.originalViews i certs hl before) :
    a.rootSample k = before.sample ((path.measuredChain i certs).sample k) := by
  induction path with
  | nil =>
    simp only [originalViews, List.mem_singleton] at ha
    subst a
    exact originalView_rootSample _ _ _ _ _ _
  | cons r rs hstart hr node tail ih =>
    rcases List.mem_cons.mp ha with hhead | htail
    · subst a
      exact originalView_rootSample _ _ _ _ _ _
    · have hv := ih certs.2 hl.2 _ a htail
      rw [Chain.append_sample] at hv
      exact hv

end PathNodes.TrueGridPath

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry
