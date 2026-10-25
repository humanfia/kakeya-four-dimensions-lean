import Submission.Obl.k4_discrete_of_terminal_charts.Exclusion

namespace Submission.Obl.k4_discrete_of_terminal_charts

open Filter MeasureTheory

noncomputable section

/-- The comparison half of the model reduction, at the construction interface. -/
theorem comparison_of_slope_volume (hvol : SlopeVolumeEstimate) : ComparisonStatement := by
  change ∃ C : ℝ, 0 < C ∧ SlopeVolumeBound C at hvol
  obtain ⟨C, hC, hvol⟩ := hvol
  intro N K L d S η W ω ν E P B f g G hyp hdom
  let data : ProfileInput N K := {
    L := L
    d := d
    S := S
    η := η
    L_pos := hyp.L_pos
    d_pos := hyp.d_pos
    d_lt_one := hyp.d_lt_one
    S_pos := hyp.S_pos
    eta_pos := hyp.η_pos
    W := W
    ω := ω
    ν := ν
    E := E
    P := P
    B := B
    f := f
    g := g
    G := G
    tempered := hyp.tempered
    pure_density := hyp.pureDensity
    angular_density := hyp.angularDensity
    lipschitz_profile := hyp.profile
    homogeneous := hyp.pureHomogeneous
    pure_cap := hyp.endpointCap
    angular_cap := hyp.angularCap }
  obtain ⟨hB, Λ, gain, hgain, hcap, hΛ⟩ := hdom
  have hpower : data.SlopeCap (gain / 2) := by
    filter_upwards [hΛ (gain / 2) (by positivity)] with k hk
    intro γ U
    calc
      ν k γ (trajectorySlope ⁻¹' U) ≤ ENNReal.ofReal (Λ k) * volume U := hcap k γ U
      _ ≤ ENNReal.ofReal (K k * N k ^ (L - f L - gain / 2)) * volume U := by
        gcongr
        calc
          Λ k ≤ N k ^ (L - f L - gain + gain / 2) := hk
          _ = N k ^ (L - f L - gain / 2) := by congr 1; ring
          _ ≤ K k * N k ^ (L - f L - gain / 2) := by
            have hp : 0 < N k ^ (L - f L - gain / 2) :=
              Real.rpow_pos_of_pos (by linarith [hyp.two_le_N k]) _
            nlinarith [hyp.subpower_K.1 k]
  refine ⟨gain / 12, by positivity, ?_⟩
  intro hcharts
  have hh := data.horizon_lower_bound hC hvol hyp.two_le_N hyp.tendsto_N
    hyp.subpower_K hB hpower (show data.HasCharts (gain / 12) from hcharts)
  linarith

end

end Submission.Obl.k4_discrete_of_terminal_charts
