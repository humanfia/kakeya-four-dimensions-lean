/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/ChartTransport.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.GridLists
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ChartMonotonicity

/-!
Transport actual scalar atlases between nearby thickness and observation
exponents. Selected incidences and full assignments remain unchanged.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes

open MeasureTheory
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

/-- Transfer observation knowledge by compatible power-grid lists. This
retains the full atlas and selected original incidences. -/
theorem chart_changeKnowledge (p : Code) (B k : ℕ) (r b b' h ε ε' : ℝ) (isTrue : Bool)
    (hN : 1 ≤ N p k) (hε : ε ≤ ε')
    (hbudget : 4 * N p k ^ (ε + |b - b'|) ≤ N p k ^ ε')
    (hc : Chart p B r b h ε isTrue k) : Chart p B r b' h ε' isTrue k := by
  exact Submission.Lib.K4ScalarFiniteGuard.chart_changeKnowledge (guardModel p) B k r b b' h ε ε' isTrue
    hN hε hbudget hc

/-- A known atlas can be moved to a nearby thickness by its actual power
loss. No true-floor condition is asserted in this transport. -/
theorem chart_changeThickness (p : Code) (B k : ℕ) (r r' b h ε ε' : ℝ)
    (hN : 1 ≤ N p k) (hε : ε ≤ ε') (hdepth : ε - r ≤ ε' - r')
    (hc : Chart p B r b h ε false k) : Chart p B r' b h ε' false k := by
  exact Submission.Lib.K4ScalarFiniteGuard.chart_changeThickness (guardModel p) B k r r' b h ε ε'
    hN hε hdepth hc

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes
