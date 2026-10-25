/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/CriticalPaths.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.OuterDiagonal
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.FiniteGuard
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.OriginalSamples

/-!
The accepted critical certificate supplies finite ordered paths with
actual original-law refinement witnesses at every layer.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes

open Set Filter
open scoped Topology
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

/-- Read the literal critical certificate as one maximizing family with
the fixed envelopes required by finite iteration. -/
theorem critical_has_maximizingFamily (hcritical : Critical) :
    ∃ (ctx : CriticalContext) (source : MaximizingFamily ctx),
      0 < ctx.S₀ ∧ 0 < ctx.η ∧ 0 < ctx.κ ∧ ctx.κ ≤ 1 ∧
      source.length = 1 ∧ (∀ i, L (source.problem i) = 1) ∧
      Tendsto ctx.D atTop (𝓝 ctx.dstar) := by
  rcases hcritical with ⟨S₀, η, dstar, κ, p, D, B,
    hS, hη, hstar₀, hstar₁, hκ, hκ₁, hp, hdlim, hDlim, hBlim, hHlim, hcompare, hscaled⟩
  have hclass (i : ℕ) : AngularClass S₀ η (p i) := by
    rcases hp i with ⟨he, hL, hS, hU, hrest⟩
    exact ⟨he, hS, by simpa only [hL, mul_one] using hU⟩
  have hcap (i : ℕ) : d (p i) ≤ D i := by
    rcases hp i with ⟨_, _, _, _, hd, _⟩
    exact hd
  have hbuffer (i : ℕ) : dstar < D i ∧ D i < 1 := by
    rcases hp i with ⟨_, _, _, _, _, hlo, hhi, _⟩
    exact ⟨hlo, hhi⟩
  have hL (i : ℕ) : L (p i) = 1 := (hp i).2.1
  let ctx : CriticalContext :=
    ⟨S₀, η, dstar, κ, D, B, hstar₀, hstar₁, hbuffer, hBlim,
      fun i q hq hd => hcompare i q hq.1 hd hq.2.1 hq.2.2⟩
  have hlength : Tendsto (fun i => L (p i)) atTop (𝓝 (1 : ℝ)) :=
    tendsto_const_nhds.congr' (Eventually.of_forall fun i => (hL i).symm)
  have hprofile : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ s ∈ Icc (0 : ℝ) (L (p i)),
      |f (p i) s - f (p i) 0 - dstar * s| ≤ ε * (D i - dstar) := by
    intro ε hε
    filter_upwards [hscaled ε hε] with i hi s hs
    exact hi s hs.1 (by simpa only [hL i] using hs.2)
  let source : MaximizingFamily ctx :=
    ⟨p, 1, by norm_num, hclass, hcap, hlength,
      by simpa only [mul_one] using hHlim, hprofile⟩
  exact ⟨ctx, source, hS, hη, hκ, hκ₁, rfl, hL, hDlim⟩

/-- A critical certificate produces paths on every prescribed finite
ordered interior grid. All layer laws hold on one eventual outer tail,
and actual final true costs complete the path to depth one. -/
theorem critical_has_finite_paths (hinit : Initial) (hcalc : Calculus)
    (hcritical : Critical) :
    ∃ (ctx : CriticalContext) (source : MaximizingFamily ctx),
      0 < ctx.S₀ ∧ 0 < ctx.η ∧ 0 < ctx.κ ∧ ctx.κ ≤ 1 ∧
      source.length = 1 ∧ (∀ i, L (source.problem i) = 1) ∧
      Tendsto ctx.D atTop (𝓝 ctx.dstar) ∧
      ∀ targets : List ℝ, targets.Pairwise (· < ·) →
        (∀ r ∈ targets, r ∈ Ioo (0 : ℝ) 1) →
        Nonempty (GridPath ctx source 0 targets) := by
  obtain ⟨ctx, source, hS, hη, hκ, hκ₁, hlength, hL, hD⟩ :=
    critical_has_maximizingFamily hcritical
  refine ⟨ctx, source, hS, hη, hκ, hκ₁, hlength, hL, hD, ?_⟩
  intro targets hordered htargets
  exact nonempty_gridPath hinit hcalc ctx source 0 targets (by norm_num) hordered htargets

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes
