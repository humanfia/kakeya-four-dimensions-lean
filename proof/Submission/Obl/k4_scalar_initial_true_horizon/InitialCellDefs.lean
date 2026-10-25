import Mathlib
import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.MassBounds

/-!
# Dyadic line-space cells of the initial atlas

In the time block `[t₀, t₀ + q]`, a bounded trajectory `l` is a line with intercept
`spatial l t₀` and slope `l.2 1`.  A group fixes the hidden bin of `hidden l t₀` (width
`aL = N^-L`); inside a group, the level-`k` cell fixes the intercept to width `q / 2^k` and
the slope to width `1 / 2^k`.  Cells are nested.  The chart of a cell uses the line through
the cell's lower corner, width `J = q / 2^k`, and the constant test at the group's bin centre.
-/

namespace Submission.Obl.k4_scalar_initial_true_horizon

open MeasureTheory Set
open Submission.Obl.k4_scalar_terminal_chart_packet_extraction (Coeff spatial hidden)

/-- Bounded trajectories: index at most `Nb`, coefficients at most `Kb`. -/
def bddTraj (Nb Kb : ℝ) (l : Coeff) : Prop := (l.1 : ℝ) ≤ Nb ∧ ∀ e, |l.2 e| ≤ Kb

/-- The hidden bin at the block start. -/
noncomputable def xBin (aL t₀ : ℝ) (l : Coeff) : ℤ := ⌊hidden l t₀ / aL⌋

/-- The level-`k` line-space cell index: intercept to width `q / 2^k`, slope to `1 / 2^k`. -/
noncomputable def cellIdx (q t₀ : ℝ) (k : ℕ) (l : Coeff) : ℤ × ℤ :=
  (⌊spatial l t₀ / (q / 2 ^ k)⌋, ⌊l.2 1 * 2 ^ k⌋)

/-- The trajectory set of the cell `(m, k, c)` of the block starting at `t₀`. -/
def cellSet (Nb Kb aL q t₀ : ℝ) (m : ℤ) (k : ℕ) (c : ℤ × ℤ) : Set Coeff :=
  {l | bddTraj Nb Kb l ∧ xBin aL t₀ l = m ∧ cellIdx q t₀ k l = c}

/-- Chart width of a level-`k` cell. -/
noncomputable def cellJ (q : ℝ) (k : ℕ) : ℝ := q / 2 ^ k

/-- Slope of the chart line of a cell (the cell's lower slope corner). -/
noncomputable def cellV (k : ℕ) (c : ℤ × ℤ) : ℝ := c.2 / 2 ^ k

/-- Offset of the chart line: `u + t v = c.1 J + (t - t₀) v`. -/
noncomputable def cellU (q t₀ : ℝ) (k : ℕ) (c : ℤ × ℤ) : ℝ :=
  c.1 * cellJ q k - t₀ * cellV k c

/-- The constant hidden test at the group's bin centre. -/
noncomputable def cellP (aL : ℝ) (m : ℤ) : MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.C (((m : ℝ) + 1 / 2) * aL)

end Submission.Obl.k4_scalar_initial_true_horizon
