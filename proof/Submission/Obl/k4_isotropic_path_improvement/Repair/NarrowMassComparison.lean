-- Part of an offer for o106 assembled by x0678 (o064). Adapted from this LOT tree, o064's
-- repository, origin/x0447 at f61522e4 (x0447's file Submission/Obl/k4_terminal_charts_from_scalar_mesh_row_fit/NarrowMassComparison.lean);
-- only the namespace changed. See that file for the sources it in turn adapts.
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Submission.Obl.k4_isotropic_path_improvement.Repair.NarrowMassComparison

/-- The mass of one selected heavy strip pays the requested power threshold.
The required lower bound on the sample size is independent of the path factor. -/
theorem kappa_power_mass_le_fraction {N κ α fraction : ℝ}
    (hκ : 0 ≤ κ) (hfraction : 0 < fraction) (hlarge : 8 / fraction ≤ N ^ α) :
    (κ * N ^ α)⁻¹ / 8 ≤ κ⁻¹ * fraction / 64 := by
  have hpower : 0 < N ^ α := (div_pos (by norm_num) hfraction).trans_le hlarge
  have hsmall : (1 : ℝ) / (8 * N ^ α) ≤ fraction / 64 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    have hprod := (div_le_iff₀ hfraction).mp hlarge
    nlinarith
  calc
    (κ * N ^ α)⁻¹ / 8 = κ⁻¹ * (1 / (8 * N ^ α)) := by
      simp only [mul_inv_rev, div_eq_mul_inv, one_mul]
      ring
    _ ≤ κ⁻¹ * (fraction / 64) :=
      mul_le_mul_of_nonneg_left hsmall (inv_nonneg.mpr hκ)
    _ = κ⁻¹ * fraction / 64 := by ring

/-- A fixed positive strip fraction pays the weaker narrow mass requirement
eventually, uniformly over every nonnegative path factor. -/
theorem eventually_kappa_power_mass_le_fraction {N : ℕ → ℝ} {α fraction : ℝ}
    (hN : Filter.Tendsto N Filter.atTop Filter.atTop)
    (hα : 0 < α) (hfraction : 0 < fraction) :
    ∀ᶠ k in Filter.atTop, ∀ κ : ℝ, 0 ≤ κ →
      (κ * N k ^ α)⁻¹ / 8 ≤ κ⁻¹ * fraction / 64 := by
  have hlarge : ∀ᶠ k in Filter.atTop, 8 / fraction ≤ N k ^ α :=
    ((tendsto_rpow_atTop hα).comp hN).eventually
      (Filter.eventually_ge_atTop (8 / fraction))
  filter_upwards [hlarge] with k hk
  intro κ hκ
  exact kappa_power_mass_le_fraction hκ hfraction hk

end Submission.Obl.k4_isotropic_path_improvement.Repair.NarrowMassComparison
