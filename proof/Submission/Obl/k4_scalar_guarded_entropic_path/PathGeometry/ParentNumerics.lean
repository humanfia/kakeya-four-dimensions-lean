import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathViews
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ChainNumerics
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.KnownExclusion

/-! One outer tail controls every genuine candidate parent before any
inner sample, common residual or entropy-window choice. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry

open Set Filter
open scoped Topology
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open TrueLiftChains PathMeasures

noncomputable section

namespace PathNodes

/-- Uniform finite-stage estimates in the actual original units of one
candidate parent. The tolerance has been fixed before its guard complexity. -/
structure ParentControl (ctx : CriticalContext) (ε gain : ℝ) (p : Code) : Prop where
  profile : ∀ s : ℝ, 0 ≤ s → s ≤ L p → |f p s - f p 0 - ctx.dstar * s| ≤ ε
  known_lower : ∀ r h : ℝ, 0 ≤ r → r < L p → Known p r (L p) h →
    ctx.κ * r - gain / 4 < h

namespace MaximizingFamily

theorem eventually_parentControl {ctx : CriticalContext} (source : MaximizingFamily ctx)
    (hcalc : Calculus) (ε gain : ℝ) (hε : 0 < ε) (hgain : 0 < gain) :
    ∀ᶠ i in atTop, ParentControl ctx ε gain (source.problem i) := by
  have he := (exclusionError_tendsto ctx source).eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < gain / 4))
  filter_upwards [source.profile_buffer ε hε, he] with i hp hi
  refine ⟨?_, ?_⟩
  · intro s hs hsL
    apply (hp s ⟨hs, hsL⟩).trans
    have hbuffer : ctx.D i - ctx.dstar ≤ 1 := by
      linarith [(ctx.cap_bounds i).2, ctx.star_nonneg]
    nlinarith only [hε, hbuffer]
  · intro r h hr hrL hk
    have hg := known_gain_le_error hcalc ctx source i r (L (source.problem i)) h
      hr hrL hrL.le le_rfl hk
    linarith only [hg, hi]

end MaximizingFamily

namespace TrueGridPath

variable {ctx : CriticalContext} {source : MaximizingFamily ctx}
  {start : ℝ} {targets : List ℝ}

/-- All original parent controls hold simultaneously, uniformly in the
chosen literal certificates and original prefix frame. -/
theorem eventually_originalViews_parentControl (path : TrueGridPath ctx source start targets)
    (hcalc : Calculus) (ε gain : ℝ) (hε : 0 < ε) (hgain : 0 < gain) :
    ∀ᶠ i in atTop, ∀ (certs : path.Certificates i) (hl : path.forget.AllLayers i)
      (root : Code) (before : Chain root (source.problem i))
      (a : OriginalView root (path.forget.finalFamily.problem i) (ctx.D i) ctx.S₀ ctx.η),
      a ∈ path.originalViews i certs hl before → ParentControl ctx ε gain a.parent := by
  induction path with
  | nil source start =>
    filter_upwards [source.eventually_parentControl hcalc ε gain hε hgain] with i hi
    intro certs hl root before a ha
    simp only [originalViews, List.mem_singleton] at ha
    subst a
    exact hi
  | @cons source start r rs hstart hr node tail ih =>
    filter_upwards [source.eventually_parentControl hcalc ε gain hε hgain, ih] with i hi ht
    intro certs hl root before a ha
    rcases List.mem_cons.mp ha with hhead | htail
    · subst a
      exact hi
    · exact ht certs.2 hl.2 root _ a htail

end TrueGridPath

end PathNodes

namespace OriginalView

variable {root final : Code} {D S η : ℝ}

/-- Only genuine positive prefix normalizations are used as windows. -/
theorem profile_zero (a : OriginalView root final D S η)
    (hpositive : 0 < a.prefixChain.length) : f a.parent 0 = 0 :=
  a.prefixChain.final_profile_zero hpositive

/-- The original relative bound is absolute in every normalized window. -/
theorem absolute_profile_bound {ctx : PathNodes.CriticalContext} {ε gain : ℝ}
    (a : OriginalView root final D S η) (hcontrol : PathNodes.ParentControl ctx ε gain a.parent)
    (hpositive : 0 < a.prefixChain.length) :
    ∀ s : ℝ, 0 ≤ s → s ≤ L a.parent → |f a.parent s - ctx.dstar * s| ≤ ε := by
  intro s hs hsL
  simpa only [a.profile_zero hpositive, sub_zero] using hcontrol.profile s hs hsL

end OriginalView

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry
