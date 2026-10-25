/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/KnownExclusion.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.MovingNode
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ChartMonotonicity

/-!
Uniform original-unit exclusions of genuine known atlases on maximizing
families. Observation knowledge may be at any finer allowed depth.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes

open Set Filter
open scoped Topology
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

/-- The cost lower bound is valid for knowledge at a finer depth `b` as
well as for the equality case `b = r`. -/
theorem known_cost_lower_bound_finer (hcalc : WeakCalculus)
    (S₀ η D B : ℝ) (p : Code) (hp : AngularClass S₀ η p)
    (hD₀ : 0 ≤ D) (hD₁ : D < 1) (hpd : d p ≤ D)
    (hrate : ∀ q, AngularClass S₀ η q → d q ≤ D → Horizon q ≤ B * L q)
    (r b h : ℝ) (hr₀ : 0 ≤ r) (hrL : r < L p) (hrb : r ≤ b) (hbL : b ≤ L p)
    (hKnown : Known p r b h) : Horizon p - B * (L p - r) ≤ h := by
  obtain ⟨q, hq, hqL, hqd, hqS, hqU, hH, hprof, heq⟩ :=
    hcalc.2.2 p r b h D hp.1 hr₀ hrL hrb hbL hD₀ hD₁
      (fun s hrs hsL => (exact_terminal_cap hp.1 s (hr₀.trans hrs) hsL).trans
        (mul_le_mul_of_nonneg_right hpd (sub_nonneg.mpr hsL))) hKnown
  have hqclass : AngularClass S₀ η q := by
    refine ⟨hq, hqS.trans hp.2.1, ?_⟩
    rw [hqU, hp.2.2, hqL]
    field_simp [(exact_length_pos hp.1).ne']
  have htail := hrate q hqclass hqd.le
  rw [hqL] at htail
  linarith

/-- An explicit vanishing error bounds every possible known-atlas gain
uniformly over depths in one exact problem. -/
noncomputable def exclusionError (ctx : CriticalContext) (source : MaximizingFamily ctx)
    (i : ℕ) : ℝ :=
  |Horizon (source.problem i) - ctx.B i * L (source.problem i)| +
    |ctx.B i - ctx.κ| * L (source.problem i)

theorem exclusionError_tendsto (ctx : CriticalContext) (source : MaximizingFamily ctx) :
    Tendsto (exclusionError ctx source) atTop (𝓝 0) := by
  have hfirst : Tendsto
      (fun i => Horizon (source.problem i) - ctx.B i * L (source.problem i))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self] using source.horizon_limit.sub
      (ctx.rate_limit.mul source.length_limit)
  have hsecond : Tendsto (fun i => ctx.B i - ctx.κ) atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self] using ctx.rate_limit.sub (tendsto_const_nhds (x := ctx.κ))
  have ht := hfirst.abs.add (hsecond.abs.mul source.length_limit)
  change Tendsto (fun i => |Horizon (source.problem i) - ctx.B i * L (source.problem i)| +
    |ctx.B i - ctx.κ| * L (source.problem i)) atTop (𝓝 0)
  simpa only [abs_zero, zero_mul, add_zero] using ht

/-- A genuine known atlas cannot improve the critical horizon by more
than the explicit envelope error, regardless of its finer knowledge depth. -/
theorem known_gain_le_error (hcalc : Calculus)
    (ctx : CriticalContext) (source : MaximizingFamily ctx) (i : ℕ)
    (r b h : ℝ) (hr₀ : 0 ≤ r) (hrL : r < L (source.problem i))
    (hrb : r ≤ b) (hbL : b ≤ L (source.problem i))
    (hKnown : Known (source.problem i) r b h) :
    ctx.κ * r - h ≤ exclusionError ctx source i := by
  have hlo := known_cost_lower_bound_finer (weakCalculus_of_calculus hcalc)
    ctx.S₀ ctx.η (ctx.D i) (ctx.B i) (source.problem i) (source.angular i)
    (ctx.star_nonneg.trans (ctx.cap_bounds i).1.le) (ctx.cap_bounds i).2
    (source.cap i) (ctx.compare i) r b h hr₀ hrL hrb hbL hKnown
  have hprod : (ctx.κ - ctx.B i) * r ≤
      |ctx.B i - ctx.κ| * L (source.problem i) := by
    calc
      _ ≤ |ctx.κ - ctx.B i| * r :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hr₀
      _ = |ctx.B i - ctx.κ| * r := by rw [abs_sub_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left hrL.le (abs_nonneg _)
  have herror := neg_le_abs (Horizon (source.problem i) - ctx.B i * L (source.problem i))
  dsimp only [exclusionError]
  nlinarith

/-- Any fixed positive gain is eventually excluded simultaneously for
all actual depths and all finer knowledge depths. -/
theorem eventually_no_known_gain (hcalc : Calculus)
    (ctx : CriticalContext) (source : MaximizingFamily ctx) (gain : ℝ) (hgain : 0 < gain) :
    ∀ᶠ i in atTop, ∀ r b h : ℝ, 0 ≤ r → r < L (source.problem i) →
      r ≤ b → b ≤ L (source.problem i) → h ≤ ctx.κ * r - gain →
      ¬ Known (source.problem i) r b h := by
  have hsmall : ∀ᶠ i in atTop, exclusionError ctx source i < gain :=
    (exclusionError_tendsto ctx source).eventually_lt tendsto_const_nhds hgain
  filter_upwards [hsmall] with i hi r b h hr₀ hrL hrb hbL hh hk
  have hbound := known_gain_le_error hcalc ctx source i r b h hr₀ hrL hrb hbL hk
  linarith

/-- A nonnegative excluded known cost has, at every fixed complexity, a
positive loss tolerance at which actual sample charts are eventually absent.
This is the direct quantifier form of the fixed-depth exclusion. -/
theorem eventually_no_chart_of_not_known (p : Code) (r b h : ℝ) (hh : 0 ≤ h)
    (hnot : ¬ Known p r b h) (B : ℕ) (hB : 1 ≤ B) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ k in atTop, ¬ Chart p B r b (h + ε) ε false k := by
  by_contra hnone
  apply hnot
  refine ⟨hh, B, hB, ?_⟩
  intro ε hε
  by_contra hfreq
  exact hnone ⟨ε, hε, Filter.not_frequently.1 hfreq⟩

/-- A fixed excluded cost forbids outputs with any vanishing loss sequence
and any smaller horizon budgets at the same fixed complexity. -/
theorem eventually_no_chart_vanishing_loss (p : Code) (hp : Exact p)
    (r b h : ℝ) (hh : 0 ≤ h) (hnot : ¬ Known p r b h) (B : ℕ) (hB : 1 ≤ B)
    (horizon loss : ℕ → ℝ) (hloss : Tendsto loss atTop (𝓝 0))
    (hhorizon : ∀ᶠ k in atTop, horizon k ≤ h + loss k) :
    ∀ᶠ k in atTop, ¬ Chart p B r b (horizon k) (loss k) false k := by
  obtain ⟨ε, hε, hexcluded⟩ := eventually_no_chart_of_not_known p r b h hh hnot B hB
  have hsmall : ∀ᶠ k in atTop, loss k < ε :=
    hloss.eventually_lt tendsto_const_nhds hε
  filter_upwards [hexcluded, hsmall, hhorizon] with k hk hs hh hc
  apply hk
  exact chart_mono p B k r b (horizon k) (h + ε) (loss k) ε false
    ((by norm_num : (1 : ℝ) ≤ 2).trans (hp.1.1 k))
    (by linarith) hs.le hc

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes
