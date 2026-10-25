import Submission.Obl.k4_horizon_chart_assembly.ProbPreparation
import Submission.Obl.k4_horizon_chart_assembly.BudgetNumerics
import Submission.Obl.k4_horizon_chart_assembly.AsymptoticEstimates
import Submission.Obl.k4_horizon_chart_assembly.FinalConversion

namespace Submission.Obl.k4_horizon_chart_assembly

open MeasureTheory Set Filter
open scoped ENNReal BigOperators

noncomputable section

/-- The numerical finite atlas implies the frozen horizon statement, with the
complexity exponent chosen before every tolerance exponent. -/
theorem finite_weighted_atlas_to_horizon
    (hatlas : FiniteWeightedAtlas) (hlight : LightCells) : HorizonStatement := by
  classical
  intro N K L d S η W ω ν E P B f g G hprob h hh
  obtain ⟨m₀, D₀, hprepared⟩ := prepared_samples N K L d S η W ω ν E P B f g G hprob
  obtain ⟨H₀, hlight⟩ := hlight N K L d S η W ω ν E P B f g G hprob
  obtain ⟨A₀, C₀, hA₀, hC₀, hatlas⟩ := hatlas
  have hN : ∀ k, 2 ≤ N k := hprob.1
  have hN₁ : ∀ k, 1 ≤ N k := fun k => by linarith [hN k]
  have hNt : Tendsto N atTop atTop := hprob.2.1
  have hK : ∀ k, 1 ≤ K k := hprob.2.2.1.1
  have hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε := hprob.2.2.1.2
  have hL : 0 < L := hprob.2.2.2.1
  let m := m₀ + 1
  obtain ⟨J, hJ⟩ := exists_nat_ge (max (1 : ℝ) (max H₀ ((m * A₀ : ℕ) : ℝ)))
  have hJ₁ : 1 ≤ J := by exact_mod_cast (le_max_left _ _).trans hJ
  have hJH : H₀ ≤ (J : ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans hJ)
  have hJA : m * A₀ ≤ J := by
    exact_mod_cast (le_max_right _ _).trans ((le_max_right _ _).trans hJ)
  obtain ⟨M, hbudget⟩ := uniform_atlas_power_budget m J C₀ L (f L)
  refine ⟨M, max D₀ 4, ?_⟩
  intro ε hε
  let ε₀ := min ε 1
  have hε₀ : 0 < ε₀ := lt_min hε (by norm_num)
  have hε₀ε : ε₀ ≤ ε := min_le_left _ _
  have hε₀₁ : ε₀ ≤ 1 := min_le_right _ _
  have hJpos : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
  obtain ⟨ζ, hζ, hζupper, hchoose⟩ := atlas_plank_loss_choice hε₀ hJpos
    (show (0 : ℝ) < (J + 1 : ℕ) by positivity)
  obtain ⟨η₁, Cg, hη₁, hCg, hfinite⟩ := hatlas ζ hζ
  obtain ⟨σ, hσ, hση, hσε, hgap⟩ := hchoose η₁ hη₁
  obtain ⟨c₀, hc₀, hlight_eventually⟩ := hlight σ hσ
  have hslack := eventually_atlas_slack hN₁ hNt hK hsub hε₀
  have hscalar := eventually_atlas_scalar_error hN₁ hNt hK hsub hσ
  have hbad := eventually_atlas_scalar_error hN₁ hNt hK hsub hc₀
  have hresidual := eventually_atlas_residual_error hN₁ hNt hK hsub hε₀ hCg.le
  have htime := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt hNt hh 8
  have hKscale := hsub 1 (by norm_num)
  apply Filter.Eventually.frequently
  filter_upwards [hslack, hscalar, hbad, hresidual, htime, hKscale, hlight_eventually]
    with k hslack hscalar hbad hresidual htime hKscale hlightk
  have hNk : 0 < N k := by linarith [hN k]
  have hKk : 0 < K k := by linarith [hK k]
  have hNm : N k ≤ N k ^ m := by
    simpa only [pow_one] using pow_le_pow_right₀ (hN₁ k) (show 1 ≤ m by dsimp [m]; omega)
  have hKN : K k ≤ N k := by simpa using hKscale
  have hKH : K k ≤ N k ^ m := hKN.trans hNm
  have hH : 2 ≤ N k ^ m := (hN k).trans hNm
  have hdata := (hprepared k).mono (pow_le_pow_right₀ (hN₁ k) (show m₀ ≤ m by dsimp [m]; omega))
  change SampleData (N k ^ m) (K k) (W k) D₀ (ω k) (ν k) (E k) (P k) (B k) at hdata
  obtain ⟨hW, hω₀, hω₁, hworld, hupper, hlower, hmass₀⟩ := hdata
  obtain ⟨T, hTmin, hTmax, hscale, ha₁⟩ := initial_dyadic_partition (hN₁ k) hL.le
  let q : ℝ := ((2 : ℝ) ^ T)⁻¹
  have hq : 0 < q := by dsimp [q]; positivity
  have hq₁ : q ≤ 1 := by
    dsimp [q]
    exact (inv_le_one₀ (by positivity)).mpr (by linarith)
  have ha : 0 < dl (N k) L := by rw [hscale]; positivity
  have hqlower : N k ^ (-L) / 8 ≤ q := dyadic_block_length_lower hNk hscale
  let Dmesh := meshIndex (N k) J
  obtain ⟨hD₂, hDlow, hDupper⟩ := meshIndex_bounds (hN k) hJ₁
  change 2 ≤ Dmesh at hD₂
  change N k ^ J ≤ (Dmesh : ℝ) at hDlow
  change (Dmesh : ℝ) ≤ N k ^ (J + 1) at hDupper
  have hD₀ : (0 : ℝ) < Dmesh := by exact_mod_cast (by omega : 0 < Dmesh)
  have hmesh : (N k ^ m) ^ A₀ ≤ (Dmesh : ℝ) := by
    rw [← pow_mul]
    exact (pow_le_pow_right₀ (hN₁ k) hJA).trans hDlow
  let κ := N k ^ ε₀
  let s := N k ^ (-σ)
  let n₀ := N k ^ (-f L)
  let θ := n₀ * s
  let τ₀ := 4 * n₀ * ((2 * K k + 2) * q) ^ 2 / κ
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hκN : κ ≤ N k := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (hN₁ k) hε₀₁
  have hκK : K k ≤ κ := by dsimp [κ]; linarith
  have hκ₂K : 2 * K k ≤ κ := by dsimp [κ]; linarith
  have hs : 0 < s := by dsimp [s]; positivity
  have hn₀ : 0 < n₀ := by dsimp [n₀]; positivity
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hτ₀ : 0 < τ₀ := by dsimp [τ₀]; positivity
  have hduration : (Dmesh : ℝ) ^ (-η₁) ≤ s := by
    apply mesh_duration_power_le (hN₁ k) _ hη₁ hση
    simpa only [Real.rpow_natCast] using hDlow
  have htrue : 4 * n₀ * ((2 * K k + 2) * q) ^ 2 ≤ τ₀ * κ := by
    dsimp [τ₀]
    exact le_of_eq (by field_simp)
  obtain ⟨C', γ, j, cv, uv, Q, R, A', F, hcount, hdisj, hchart, hmass⟩ :=
    hfinite (N k ^ m) (K k) hH (hK k) hKH (W k) D₀ (ω k) (ν k) (E k) (P k) (B k)
      hW hω₀ hω₁ hworld hupper hlower (dl (N k) L) T ha ha₁ hscale.symm.le
      Dmesh hD₂ hmesh s τ₀ θ n₀ κ hs hτ₀ hθ hn₀ hslack hduration htrue
  have hV := hbudget (N k) (K k) (hN k) (hK k) hKH Dmesh T hDupper hTmax
    q κ hqlower hκ hκN
  have hρ : 0 < q / (Dmesh : ℝ) := div_pos hq hD₀
  have hρbound : q / (Dmesh : ℝ) ≤ N k ^ (-H₀) :=
    fine_mesh_scale_le (hN₁ k) hq₁ hDlow hJH
  have hθeq : θ = N k ^ (-f L - σ) := by
    dsimp [θ, n₀, s]
    rw [← Real.rpow_add hNk]
    congr 1
  have hthreshold : θ * (q / (Dmesh : ℝ)) ^ 3 =
      N k ^ (-f L - σ) * (q / (Dmesh : ℝ)) * (q / (Dmesh : ℝ)) ^ 2 := by
    rw [hθeq]
    ring
  have hlightmass : lightMass (W k) (ω k) (ν k) (E k) (B k)
      (dl (N k) L) (q / (Dmesh : ℝ)) θ ≤ ENNReal.ofReal (N k ^ (-c₀)) := by
    simpa only [lightMass, hthreshold] using
      hlightk (q / (Dmesh : ℝ)) (q / (Dmesh : ℝ)) hρ hρbound hρ hρbound
  have hcoefficient : Cg * K k ^ 3 * τ₀ * (Dmesh : ℝ) ^ ζ / (s * θ * q ^ 2) ≤ 1 / 4 := by
    have hgap' : 2 * σ + ((J + 1 : ℕ) : ℝ) * ζ ≤ ε₀ / 2 := by linarith
    have hbound := atlas_residual_coefficient_le (hN₁ k) (hK k) hD₀.le hCg.le hζ.le hq hn₀
      (by simpa only [Real.rpow_natCast] using hDupper) hgap'
    exact hbound.trans hresidual
  have hmassfin := original_weighted_mass_ne_top (ω k) (ν k) (E k)
    (fun γ => (hworld γ).1) (fun γ => (hworld γ).2.2.2.2.2.2.2.1)
  have hmassfloor := retained_weighted_mass hKk hκ₂K hmassfin hmass₀ hmass
    (hlightmass.trans (ENNReal.ofReal_le_ofReal hbad))
    (ENNReal.ofReal_le_ofReal hscalar) (ENNReal.ofReal_le_ofReal hcoefficient)
  refine ⟨κ, (hK k).trans hκK, hκK,
    Real.rpow_le_rpow_of_exponent_le (hN₁ k) hε₀ε, T, C', γ, j, cv, uv, Q, R, A', F,
    hTmax.trans htime.le, hcount.trans hV, hdisj, ?_, hmassfloor⟩
  intro b
  apply budgetChart_as_chart hV (hchart b)
  intro hb
  simpa only [n₀, q, physical_floor_eq] using hb

end
end Submission.Obl.k4_horizon_chart_assembly
