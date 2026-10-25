import Submission.Obl.k4_raw_critical_segment_forests.PreparedInterface

namespace Submission.Obl.k4_raw_critical_segment_forests

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- The true incidence floor and the full time block cancel the time factor:
every prepared chart's full prior is saturated at its own depth. -/
theorem PreparedParent.prior_saturation {p : Data} (hp : Valid p) {k M D : ℕ}
    {r ε κ : ℝ} {a : Atlas p k} (ha : PreparedParent p M D r ε κ a) (b : Fin a.C) :
    0 < (p.ν k (a.γ b) (a.A b)).toReal ∧
      p.N k ^ (-p.f r) * |Matrix.det (a.Q b)| / κ ≤ (p.ν k (a.γ b) (a.A b)).toReal ∧
      (p.ν k (a.γ b) (a.A b)).toReal ≤ κ * p.N k ^ (-p.f r) * |Matrix.det (a.Q b)| := by
  obtain ⟨Mp, Dp, hfmt⟩ := hp.2.2.2.2.2.2.2.2.1
  letI : IsProbabilityMeasure (p.ν k (a.γ b)) := ((hfmt k).2.2.2.1 (a.γ b)).1
  have hκ : 0 < κ := lt_of_lt_of_le zero_lt_one ha.1
  have hN := hp.scale_pos k
  have hT : (0 : ℝ) < (2 : ℝ) ^ a.T := by positivity
  have hc := ha.2.2.2.2.1.2.2.1 b
  rcases hc with ⟨hdet, hc, hQ, hsum, hdeg, hcoeff, hA, hF, hfmt', hline,
    hpoint, hfloor, hupper, hlist⟩
  have hdetpos : 0 < |Matrix.det (a.Q b)| := abs_pos.mpr hdet
  have hfin : p.ν k (a.γ b) (a.A b) ≠ ⊤ := measure_ne_top _ _
  have hmass : priorMass p k (a.γ b) (a.F b) ≤
      ENNReal.ofReal ((p.ν k (a.γ b) (a.A b)).toReal / (2 : ℝ) ^ a.T) := by
    calc
      _ ≤ (p.ν k (a.γ b)).prod volume
          (a.A b ×ˢ Set.Icc ((a.j b : ℝ) / (2 : ℝ) ^ a.T)
            (((a.j b : ℝ) + 1) / (2 : ℝ) ^ a.T)) := by
        apply measure_mono
        intro z hz
        exact ⟨(hpoint z hz).2.1, (hpoint z hz).2.2.1⟩
      _ = _ := by
        rw [Measure.prod_prod, Real.volume_Icc]
        have heq : ((a.j b : ℝ) + 1) / (2 : ℝ) ^ a.T -
            (a.j b : ℝ) / (2 : ℝ) ^ a.T = 1 / (2 : ℝ) ^ a.T := by ring
        rw [heq]
        calc
          _ = ENNReal.ofReal (p.ν k (a.γ b) (a.A b)).toReal *
              ENNReal.ofReal (1 / (2 : ℝ) ^ a.T) := by rw [ENNReal.ofReal_toReal hfin]
          _ = _ := by
            rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
            congr 1
            ring
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity :
      0 ≤ (p.ν k (a.γ b) (a.A b)).toReal / (2 : ℝ) ^ a.T)).mp (hfloor.trans hmass)
  have heq : p.N k ^ (-p.f r) * |Matrix.det (a.Q b)| / ((2 : ℝ) ^ a.T * κ) =
      (p.N k ^ (-p.f r) * |Matrix.det (a.Q b)| / κ) / (2 : ℝ) ^ a.T := by ring
  rw [heq] at hreal
  have hlower := (div_le_div_iff_of_pos_right hT).mp hreal
  have hupreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hupper
  rw [ENNReal.toReal_ofReal (by positivity)] at hupreal
  exact ⟨(by positivity : 0 < p.N k ^ (-p.f r) * |Matrix.det (a.Q b)| / κ).trans_le hlower,
    hlower, hupreal⟩

/-- The shifted original profile gives terminal calibration through each
prepared parent, with no selected-incidence renormalization. -/
theorem PreparedParent.terminal_calibration {p : Data} (hp : Valid p) {k M D : ℕ}
    {r ε κ : ℝ} {a : Atlas p k} (ha : PreparedParent p M D r ε κ a) (b : Fin a.C) :
    p.N k ^ (-p.f p.L) * |Matrix.det (a.Q b)| ≤
      κ * (p.ν k (a.γ b) (a.A b)).toReal * p.N k ^ (-(p.f p.L - p.f r)) := by
  have hκ : 0 < κ := lt_of_lt_of_le zero_lt_one ha.1
  have hprior := (ha.prior_saturation hp b).2.1
  have hprior' := (div_le_iff₀ hκ).mp hprior
  have hm := mul_le_mul_of_nonneg_right hprior'
    (Real.rpow_nonneg (hp.scale_pos k).le (-(p.f p.L - p.f r)))
  have heq : p.N k ^ (-p.f r) * |Matrix.det (a.Q b)| * p.N k ^ (-(p.f p.L - p.f r)) =
      p.N k ^ (-p.f p.L) * |Matrix.det (a.Q b)| := by
    rw [mul_right_comm, ← Real.rpow_add (hp.scale_pos k)]
    congr 2
    ring
  rw [heq] at hm
  simpa only [mul_comm (p.ν k (a.γ b) (a.A b)).toReal κ] using hm

end
end Submission.Obl.k4_raw_critical_segment_forests
