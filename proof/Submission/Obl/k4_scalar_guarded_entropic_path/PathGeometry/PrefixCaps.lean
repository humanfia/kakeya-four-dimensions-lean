/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/PrefixCaps.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathPrefixes

/-! Actual endpoint secant caps at all cumulative original critical depths. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes

open Set Filter
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

/-- The actual coarsened exact problem certifies a cap on the original
profile at its own actual depth. -/
theorem LayerAt.endpoint_cap {p outer remaining : Code} {depth cost δ : ℝ}
    (h : LayerAt p outer remaining depth cost δ) (s : ℝ) (hs : s ∈ Icc 0 depth) :
    f p depth - f p s ≤ δ * (depth - s) := by
  have hc := exact_terminal_cap h.outer_exact s hs.1
    (by rw [h.outer_length]; exact hs.2)
  rw [h.outer_length, h.outer_cap] at hc
  have h₀ := h.outer_profile depth ⟨h.depth_nonneg, le_rfl⟩
  have h₁ := h.outer_profile s hs
  linarith

namespace GridPath

variable {ctx : CriticalContext} {source : MaximizingFamily ctx}
  {start : ℝ} {targets : List ℝ}

/-- Endpoint caps compose at the actual cumulative depth. The entire
finite path uses the same strict buffer below the original cap D_i. -/
theorem cumulative_endpoint_cap (path : GridPath ctx source start targets) :
    ∀ᶠ i in atTop, ∀ s ∈ Icc 0 (path.totalDepth i),
      f (source.problem i) (path.totalDepth i) - f (source.problem i) s ≤
        (ctx.dstar + (ctx.D i - ctx.dstar) / 2) * (path.totalDepth i - s) := by
  induction path with
  | nil =>
    refine Eventually.of_forall fun i s hs => ?_
    change 0 ≤ s ∧ s ≤ 0 at hs
    have hs₀ : s = 0 := le_antisymm hs.2 hs.1
    simp only [totalDepth, hs₀, sub_self, mul_zero, le_refl]
  | @cons source start r rs hstart hr node tail ih =>
    filter_upwards [node.layers, ih, tail.path_law] with i hn htail hlaw s hs
    change s ∈ Icc 0 (node.depth i + tail.totalDepth i) at hs
    change f (source.problem i) (node.depth i + tail.totalDepth i) -
      f (source.problem i) s ≤ _ * (node.depth i + tail.totalDepth i - s)
    have hz : tail.totalDepth i ∈ Icc 0 (L (node.remaining.problem i)) :=
      ⟨hlaw.depth_nonneg, hlaw.depth_lt.le⟩
    have hpz := hn.remaining_profile _ hz
    by_cases hsd : s ≤ node.depth i
    · have hfirst := hn.endpoint_cap s ⟨hs.1, hsd⟩
      have hrest := htail 0 ⟨le_rfl, hlaw.depth_nonneg⟩
      nlinarith
    · have hv : s - node.depth i ∈ Icc 0 (tail.totalDepth i) :=
        ⟨sub_nonneg.mpr (le_of_not_ge hsd), by linarith [hs.2]⟩
      have hrest := htail _ hv
      have hpv := hn.remaining_profile (s - node.depth i) ⟨hv.1, hv.2.trans hz.2⟩
      rw [show node.depth i + (s - node.depth i) = s by ring] at hpv
      nlinarith

/-- All finite prefixes have the same original buffered endpoint cap on
one common eventual outer tail, before choosing any inner exact sample. -/
theorem eventually_all_prefix_caps (path : GridPath ctx source start targets) :
    ∀ᶠ i in atTop, ∀ n : Fin (targets.length + 1),
      ∀ s ∈ Icc 0 ((path.take n).totalDepth i),
        f (source.problem i) ((path.take n).totalDepth i) - f (source.problem i) s ≤
          (ctx.dstar + (ctx.D i - ctx.dstar) / 2) * ((path.take n).totalDepth i - s) := by
  apply Filter.eventually_all.2
  intro n
  exact (path.take n).cumulative_endpoint_cap

end GridPath

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes
