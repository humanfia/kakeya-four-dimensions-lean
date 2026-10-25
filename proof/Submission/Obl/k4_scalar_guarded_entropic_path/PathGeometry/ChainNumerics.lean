import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ChainCuts
import Submission.Obl.k4_scalar_guarded_entropic_path.Accepted

/-! Relative profiles and horizon deficits telescope along the same
literal true normalizations used for the common path measure. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.TrueLiftChains.Chain

open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_scalar_guarded_entropic_path

noncomputable section

variable {p z : Code}

/-- The remaining absolute length uses the accumulated original depths. -/
theorem depth_lt_length (chain : Chain p z) : chain.depth < L p := by
  have hz := exact_length_pos chain.final_exact
  change 0 < L z at hz
  linarith [chain.remaining_length]

/-- Every suffix profile is a single original increment; its error does
not multiply with the number of normalizations. -/
theorem profile_eq (chain : Chain p z) (s : ℝ) (hs : 0 ≤ s) (hsL : s ≤ L z) :
    f z s - f z 0 = f p (chain.depth + s) - f p chain.depth := by
  induction chain with
  | nil => simp [depth]
  | @cons p q z r h a hL hr hh hrel tail ih =>
    have ht : 0 ≤ tail.depth := tail.depth_nonneg
    have htL : tail.depth ≤ L q := tail.depth_lt_length.le
    have htsL : tail.depth + s ≤ L q := by linarith [tail.remaining_length]
    have h₀ := hrel tail.depth ht htL
    have h₁ := hrel (tail.depth + s) (add_nonneg ht hs) htsL
    rw [depth, add_assoc]
    linarith only [ih hsL, h₀, h₁]

/-- A positive chosen true prefix has absolute profile zero at its
normalized origin, by the actual inherited full-prior saturation. -/
theorem final_profile_zero (chain : Chain p z) (hpos : 0 < chain.length) : f z 0 = 0 := by
  induction chain with
  | nil => simp [length] at hpos
  | cons a hL hr hh hrel tail ih =>
    cases tail with
    | nil q hq => exact a.profile_zero hq hL hr
    | cons b hL' hr' hh' hrel' tail' => exact ih (by simp [length])

/-- Uniform original profile errors telescope with a factor two. -/
theorem relative_profile_error (chain : Chain p z) {d₀ e : ℝ}
    (herror : ∀ s : ℝ, 0 ≤ s → s ≤ L p → |f p s - f p 0 - d₀ * s| ≤ e)
    (s : ℝ) (hs : 0 ≤ s) (hsL : s ≤ L z) :
    |f z s - f z 0 - d₀ * s| ≤ 2 * e := by
  have hdepth : 0 ≤ chain.depth := chain.depth_nonneg
  have hs' : chain.depth + s ≤ L p := by linarith [chain.remaining_length]
  have h₀ := herror chain.depth hdepth chain.depth_lt_length.le
  have h₁ := herror (chain.depth + s) (add_nonneg hdepth hs) hs'
  rw [chain.profile_eq s hs hsL]
  have heq : f p (chain.depth + s) - f p chain.depth - d₀ * s =
      (f p (chain.depth + s) - f p 0 - d₀ * (chain.depth + s)) -
        (f p chain.depth - f p 0 - d₀ * chain.depth) := by ring
  rw [heq]
  exact (abs_sub _ _).trans (by linarith only [h₀, h₁])

/-- Actual horizon charging composes through the same true chain. -/
theorem horizon_le (chain : Chain p z) : Horizon p ≤ chain.cost + Horizon z := by
  induction chain with
  | nil => simp [cost]
  | @cons p q z r h a hL hr hh hrel tail ih =>
    have hrL : r < L p := by
      have hq := exact_length_pos tail.source_exact
      change 0 < L q at hq
      linarith
    have hfirst := horizon_le_add_of_refinement a.parent_exact tail.source_exact
      hr hrL le_rfl hrL.le hh hL (refinement_iff_nonempty_witness.mpr ⟨a.witness⟩)
    change Horizon p ≤ h + tail.cost + Horizon z
    linarith only [hfirst, ih]

/-- A candidate parent's horizon deficit is paid by the original deficit
and the accumulated error of the actual prefix cost. -/
theorem horizon_gap (chain : Chain p z) {κ ε₁ ε₂ : ℝ}
    (hp : κ * L p - ε₁ ≤ Horizon p)
    (hc : chain.cost ≤ κ * chain.depth + ε₂) :
    κ * L z - (ε₁ + ε₂) ≤ Horizon z := by
  rw [chain.remaining_length]
  nlinarith [chain.horizon_le]

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.TrueLiftChains.Chain
