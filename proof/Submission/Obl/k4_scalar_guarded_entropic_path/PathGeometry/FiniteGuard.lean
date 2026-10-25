/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/FiniteGuard.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.KnownLimits
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.KnownExclusion

/-!
The fixed-complexity finite-sample horizon exclusion. Thickness and
observation exponents may vary with the original exact sample. Compactness
and actual power-grid list transport turn any infinitely recurring output
into a genuine known atlas at the limiting exponents.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes

open Set Filter
open scoped Topology
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

/-- Excluding genuine known improvements gives an eventual exclusion of
all fixed-complexity charts with vanishing losses, uniformly in their
actual thickness, knowledge depth, horizon and smaller loss budgets. -/
theorem uniform_finiteSampleGuard (p : Code) (hp : Exact p) (B : ℕ) (hB : 1 ≤ B)
    (κ gain margin : ℝ) (hgain : 0 < gain) (hmargin : 0 < margin)
    (loss : ℕ → ℝ) (hloss : Tendsto loss atTop (𝓝 0))
    (hexclude : ∀ r b h : ℝ, 0 ≤ r → r < L p → r ≤ b → b ≤ L p →
      h ≤ κ * r - gain / 2 → ¬ Known p r b h) :
    ∀ᶠ k in atTop, ∀ r b h ε : ℝ, 0 ≤ r → r ≤ L p - margin →
      r ≤ b → b ≤ L p → h ≤ κ * r - gain → ε ≤ loss k →
      ¬ Chart p B r b h ε false k := by
  exact Submission.Lib.K4ScalarFiniteGuard.uniform_finiteSampleGuard (guardModel p)
    (guardModel_sampling p hp) B hB κ gain margin hgain hmargin loss hloss hexclude

/-- The order of the finite guard's quantifiers: first take a sufficiently
late outer exact problem for the positive gain, then fix any complexity
and vanishing path-loss sequence, and only then take its original sample.
The guard is uniform over all output thicknesses away from the endpoint. -/
theorem eventually_finiteSampleGuards (hcalc : Calculus)
    (ctx : CriticalContext) (source : MaximizingFamily ctx)
    (gain margin : ℝ) (hgain : 0 < gain) (hmargin : 0 < margin) :
    ∀ᶠ i in atTop, ∀ B : ℕ, 1 ≤ B → ∀ loss : ℕ → ℝ, Tendsto loss atTop (𝓝 0) →
      ∀ᶠ k in atTop, ∀ r b h ε : ℝ,
        0 ≤ r → r ≤ L (source.problem i) - margin →
        r ≤ b → b ≤ L (source.problem i) → h ≤ ctx.κ * r - gain → ε ≤ loss k →
        ¬ Chart (source.problem i) B r b h ε false k := by
  filter_upwards [eventually_no_known_gain hcalc ctx source (gain / 2) (by positivity)]
    with i hi B hB loss hloss
  exact uniform_finiteSampleGuard (source.problem i) (source.angular i).1 B hB
    ctx.κ gain margin hgain hmargin loss hloss hi

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes
