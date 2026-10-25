import Submission.Obl.k4_quadratic_atlas_normalization.LowSample

/-!
# The low-curvature step

`low_sample_normalization` (x0398) normalizes one late low-curvature sample under explicit
large-scale caps. Here the caps are met: the number of power bins `m` is fixed by the output
slack (`exists_fine_power_bins`), the input slack is `min (a/4) (ε/4)`, and the late samples are
those with `4 ≤ N^(a/2)` and `64 m ≤ N^(ε/2)`.
-/

set_option linter.unusedVariables false

namespace Submission.Obl.k4_quadratic_atlas_normalization

open Filter

/-- The low-curvature step. -/
theorem lowStep (L a h : ℝ) (M D Mb : ℕ) (hL : 0 < L) (ha : 0 < a) (h20 : 20 * a < L) :
    LowStep L a h M D Mb := by
  refine ⟨lowOutputExponent M a, max D 2, fun ε hε => ?_⟩
  obtain ⟨m, hm, -, hstep⟩ := exists_fine_power_bins a (ε / 4) ha (by positivity)
  refine ⟨min (a / 4) (ε / 4), lt_min (by positivity) (by positivity), ?_⟩
  have hev : ∀ᶠ N : ℝ in atTop, 4 ≤ N ^ (a / 2) ∧ 64 * (m : ℝ) ≤ N ^ (ε / 2) :=
    ((tendsto_rpow_atTop (by positivity)).eventually_ge_atTop 4).and
      ((tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hev
  refine ⟨N₀, fun Nk Wk ωk νk Ek Bk hNk hN2 hω0 hω1 hν hB hR => ?_⟩
  obtain ⟨hNa, hmN⟩ := hN₀ Nk hNk
  exact low_sample_normalization L a h (min (a / 4) (ε / 4)) ε M D m ha hε hm
    (min_le_left _ _) (min_le_right _ _) hstep Nk Wk ωk νk Ek Bk hN2 hNa hmN hω0 hω1 hν
    (fun g => (hB g).1) hR

end Submission.Obl.k4_quadratic_atlas_normalization
