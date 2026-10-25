/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/KnownLimits.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ChartTransport

/-!
Limits of the thickness and knowledge exponents of actual chart outputs.
Finite compatibility lists absorb their power-grid mismatch into a
vanishing original-resolution loss.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes

open Filter
open scoped Topology
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

/-- Every actual chart has a nonnegative horizon budget at a resolution
strictly greater than one. -/
theorem chart_horizon_nonneg (p : Code) (B k : ℕ) (r b h ε : ℝ) (isTrue : Bool)
    (hN : 1 < N p k) (hc : Chart p B r b h ε isTrue k) : 0 ≤ h := by
  exact Submission.Lib.K4ScalarFiniteGuard.chart_horizon_nonneg (guardModel p) B k r b h ε isTrue hN hc

/-- On any actual sample subsequence, convergent exponents and vanishing
losses can be replaced by their limits at any prescribed positive loss. -/
theorem eventually_transport_chart_exponents (p : Code) (hp : Exact p) (B : ℕ)
    (sample : ℕ → ℕ) (hsample : Tendsto sample atTop atTop)
    (r b : ℝ) (rseq bseq horizon loss : ℕ → ℝ)
    (hr : Tendsto rseq atTop (𝓝 r)) (hb : Tendsto bseq atTop (𝓝 b))
    (hloss : Tendsto loss atTop (𝓝 0)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop,
      Chart p B (rseq k) (bseq k) (horizon k) (loss k) false (sample k) →
      Chart p B r b (horizon k) ε false (sample k) := by
  exact Submission.Lib.K4ScalarFiniteGuard.eventually_transport_chart_exponents (guardModel p)
    (guardModel_sampling p hp) B sample hsample r b rseq bseq horizon loss hr hb hloss ε hε

/-- Infinitely many actual uniformly tempered charts with converging
thickness/knowledge exponents produce a genuine known atlas at the
limiting exponents. The horizon needs only an eventual upper envelope. -/
theorem known_of_varying_charts (p : Code) (hp : Exact p) (B : ℕ) (hB : 1 ≤ B)
    (sample : ℕ → ℕ) (hsample : Tendsto sample atTop atTop)
    (r b h : ℝ) (hh : 0 ≤ h) (rseq bseq horizon loss : ℕ → ℝ)
    (hr : Tendsto rseq atTop (𝓝 r)) (hb : Tendsto bseq atTop (𝓝 b))
    (hloss : Tendsto loss atTop (𝓝 0))
    (hhorizon : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, horizon k ≤ h + ε)
    (hcharts : ∃ᶠ k in atTop,
      Chart p B (rseq k) (bseq k) (horizon k) (loss k) false (sample k)) :
    Known p r b h := by
  exact Submission.Lib.K4ScalarFiniteGuard.known_of_varying_charts (guardModel p)
    (guardModel_sampling p hp) B hB sample hsample r b h hh rseq bseq horizon loss
    hr hb hloss hhorizon hcharts

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes
