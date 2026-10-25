import Submission.Obl.k4_discrete_of_terminal_charts.Horizon
import Submission.Obl.k4_discrete_of_terminal_charts.CoefficientGeometry
import Submission.Obl.k4_discrete_of_terminal_charts.TerminalInterface

namespace Submission.Obl.k4_discrete_of_terminal_charts

open Set MeasureTheory Filter
open scoped ENNReal

noncomputable section

/-- The quantitative datum retained from the finite-configuration construction. -/
def ProfileInput.SlopeCap {N K : ℕ → ℝ} (data : ProfileInput N K) (gain : ℝ) : Prop :=
  ∀ᶠ k in atTop, ∀ γ (U : Set E3),
    data.ν k γ (trajectorySlope ⁻¹' U) ≤
      ENNReal.ofReal (K k * N k ^ (data.L - data.f data.L - gain)) * volume U

/-- A true terminal chart obeys the scalar density comparison. -/
theorem ProfileInput.chart_density_comparison {N K : ℕ → ℝ}
    (data : ProfileInput N K) {C gain h : ℝ} (hC : 0 < C)
    (hvol : SlopeVolumeBound C) (hN : ∀ k, 2 ≤ N k) (hK : ∀ k, 1 ≤ K k)
    (hB : ∀ k γ, data.B k γ = 1) (hcap : data.SlopeCap gain)
    (hcharts : data.HasCharts h) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ K' : ℕ → ℝ,
      ((∀ k, 1 ≤ K' k) ∧ SubpowerBound (N ∘ ψ) K') ∧
      ∃ T : ℕ → ℕ, ∀ᶠ k in atTop,
        (2 : ℝ) ^ T k ≤ N (ψ k) ^ h ∧
        N (ψ k) ^ (-data.f data.L) ≤
          (K (ψ k) * N (ψ k) ^ (data.L - data.f data.L - gain)) *
            C * K' k ^ 5 * gridWidth (N (ψ k)) data.L / (((2 : ℝ) ^ T k)⁻¹) ^ 3 := by
  rcases hcharts with ⟨ψ, hψ, M, D, K', hK', hKK', T, C', γ, j, c, u, Q, R, A, F, hx⟩
  refine ⟨ψ, hψ, K', hK', T, ?_⟩
  filter_upwards [hψ.tendsto_atTop.eventually hcap] with k hkcap
  rcases hx k with ⟨hT, hcount, hdisj, hlocal, htotal⟩
  have hne : Nonempty (Fin (C' k)) :=
    nonempty_of_terminal_mass (fun b => ENNReal.ofReal (data.ω (ψ k) (γ k b)))
      (fun b => ((data.ν (ψ k) (γ k b)).prod volume) (F k b))
      (lt_of_lt_of_le zero_lt_one (hK'.1 k)) htotal
  let b : Fin (C' k) := Classical.choice hne
  rcases hlocal b with
    ⟨hQ, hcenter, hmatrix, hmatrixsmall, hR, hcoeff, hA, hF,
      hformat, hassign, hselected, hfloor⟩
  have hNk : 0 < N (ψ k) := by linarith [hN (ψ k)]
  let q : ℝ := ((2 : ℝ) ^ T k)⁻¹
  let t₀ : ℝ := ((j k b : ℕ) : ℝ) / (2 : ℝ) ^ T k
  have hq : 0 < q := by dsimp [q]; positivity
  have hI : Icc t₀ (t₀ + q) =
      Icc (((j k b : ℕ) : ℝ) / (2 : ℝ) ^ T k)
        ((((j k b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T k) := by
    congr 1
    dsimp [t₀, q]
    rw [add_div, one_div]
  have hradius : 1 ≤ 3 * N (ψ k) ^ M := by
    have : 1 ≤ N (ψ k) ^ M := one_le_pow₀ (by linarith [hN (ψ k)])
    linarith
  have hgeom : ∀ p ∈ F k b,
      trajectorySlope p.1 ∈ eligibleSlopes (R k b) (Q k b) (c k b) (u k b)
        t₀ q (gridWidth (N (ψ k)) data.L) (K' k) (3 * N (ψ k) ^ M) ∧
        p.2 ∈ Icc t₀ (t₀ + q) := by
    intro p hp
    rcases hselected p hp with ⟨hpE, hpA, hpt, hpreg⟩
    have hbounds := (hassign p.1 hpA).2.1
    have hpos : 0 ≤ N (ψ k) ^ M := by positivity
    refine ⟨⟨trajectorySlope_norm_le hpos p.1 hbounds, trajectoryIntercept p.1,
      trajectoryIntercept_norm_le hpos p.1 hbounds, ?_, ?_⟩, by rwa [hI]⟩
    · intro t ht
      have hh := (hassign p.1 hpA).2.2 t (by rwa [← hI])
      constructor
      · rw [trajectory_planar_delta]
        exact hh.1
      · rw [trajectory_point]
        exact hh.2.1
    · refine ⟨p.2, by rwa [hI], ?_⟩
      rw [trajectory_point]
      simpa only [hB, one_div] using hpreg
  have hfloor' : ENNReal.ofReal
      (N (ψ k) ^ (-data.f data.L) * |Matrix.det (Q k b)| * q / K' k) ≤
        ((data.ν (ψ k) (γ k b)).prod volume) (F k b) := by
    convert hfloor using 1
    congr 1
    simp only [q, div_eq_mul_inv, mul_inv_rev]
    ring
  refine ⟨hT, ?_⟩
  exact density_le_of_chart_mass_bounds
    (mul_nonneg (by linarith [hK (ψ k)]) (Real.rpow_pos_of_pos hNk _).le)
    hC.le (lt_of_lt_of_le zero_lt_one (hK'.1 k)) (gridWidth_pos _ _).le
    (abs_pos.mpr hQ) hq hfloor'
    (chart_incidence_mass_le hC.le
      (mul_nonneg (by linarith [hK (ψ k)]) (Real.rpow_pos_of_pos hNk _).le)
      hvol (data.ν (ψ k) (γ k b)) trajectorySlope (hkcap (γ k b))
      (R k b) (Q k b) (c k b) (u k b) hR hQ hq
      (gridWidth_pos _ _) (hK'.1 k) hradius (F k b) hgeom)

theorem profile_density_upper_bound {N K C K' L f gain q n : ℝ}
    (hN : 0 < N) (hK : 0 ≤ K) (hC : 0 ≤ C) (hK' : 0 ≤ K')
    (hn : n ≤ (K * N ^ (L - f - gain)) * C * K' ^ 5 * gridWidth N L / q ^ 3)
    (hq : 0 < q) :
    n ≤ (2 * C * K * K' ^ 5) * N ^ (-f - gain) / q ^ 3 := by
  have hpow : N ^ (L - f - gain) * N ^ (-L) = N ^ (-f - gain) := by
    rw [← Real.rpow_add hN]
    congr 1
    ring
  calc
    n ≤ (K * N ^ (L - f - gain)) * C * K' ^ 5 * gridWidth N L / q ^ 3 := hn
    _ ≤ (K * N ^ (L - f - gain)) * C * K' ^ 5 * (2 * N ^ (-L)) / q ^ 3 := by
      gcongr
      exact gridWidth_le hN
    _ = (2 * C * K * K' ^ 5) * (N ^ (L - f - gain) * N ^ (-L)) / q ^ 3 := by ring
    _ = (2 * C * K * K' ^ 5) * N ^ (-f - gain) / q ^ 3 := by rw [hpow]

/-- The full-slope cap forces the claimed positive horizon on every subsequence. -/
theorem ProfileInput.horizon_lower_bound {N K : ℕ → ℝ}
    (data : ProfileInput N K) {C gain h : ℝ} (hC : 0 < C)
    (hvol : SlopeVolumeBound C) (hN : ∀ k, 2 ≤ N k)
    (hNt : Tendsto N atTop atTop)
    (hK : (∀ k, 1 ≤ K k) ∧ SubpowerBound N K)
    (hB : ∀ k γ, data.B k γ = 1) (hcap : data.SlopeCap gain)
    (hcharts : data.HasCharts h) : gain ≤ 3 * h := by
  rcases data.chart_density_comparison hC hvol hN hK.1 hB hcap hcharts with
    ⟨ψ, hψ, K', hK', T, hx⟩
  have hN₁ : ∀ k, 1 ≤ (N ∘ ψ) k := fun k => le_trans one_le_two (hN (ψ k))
  have hN₀ : ∀ k, 0 < (N ∘ ψ) k := fun k => lt_of_lt_of_le zero_lt_one (hN₁ k)
  have hKt : ∀ k, 0 ≤ K (ψ k) := fun k => le_trans zero_le_one (hK.1 (ψ k))
  have hK't : ∀ k, 0 ≤ K' k := fun k => le_trans zero_le_one (hK'.1 k)
  have hNt' := hNt.comp hψ.tendsto_atTop
  have hloss : SubpowerBound (N ∘ ψ) (fun k => 2 * C * K (ψ k) * K' k ^ 5) :=
    subpower_mul hN₀ (fun k => mul_nonneg (by positivity) (hKt k))
      (fun k => pow_nonneg (hK't k) _)
      (subpower_mul hN₀ (fun _ => by positivity) hKt
        (subpower_const hNt' (2 * C)) (subpower_subsequence hK.2 hψ))
      (subpower_pow hN₁ hK't hK'.2 5)
  apply horizon_exponent_lower_bound hN₁ hNt'
    (fun k => mul_nonneg (mul_nonneg (by positivity) (hKt k))
      (pow_nonneg (hK't k) _)) hloss
    (fun k => Real.rpow_pos_of_pos (hN₀ k) (-data.f data.L - gain))
    (fun k => by positivity)
    (n := fun k => N (ψ k) ^ (-data.f data.L))
    (q := fun k => ((2 : ℝ) ^ T k)⁻¹)
  · filter_upwards [] with k
    dsimp
    rw [← Real.rpow_add (show 0 < N (ψ k) from hN₀ k)]
    have : -data.f data.L - gain + gain = -data.f data.L := by ring
    rw [this]
  · filter_upwards [hx] with k hk
    exact profile_density_upper_bound (hN₀ k) (hKt k) hC.le (hK't k) hk.2
      (by positivity)
  · filter_upwards [hx] with k hk
    exact dyadic_time_lower_bound (hN₀ k) hk.1

/-- The terminal assertion excludes the slope-dominated profile produced by a counterexample. -/
theorem ProfileInput.exclude {N K : ℕ → ℝ}
    (data : ProfileInput N K) {C gain : ℝ} (hC : 0 < C)
    (hvol : SlopeVolumeBound C) (hterm : TerminalChartAssertion)
    (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : (∀ k, 1 ≤ K k) ∧ SubpowerBound N K)
    (hB : ∀ k γ, data.B k γ = 1) (hgain : 0 < gain)
    (hcap : data.SlopeCap gain) : False := by
  have hcharts := data.hasCharts hterm hN hNt hK (h := gain / 6) (by positivity)
  have hh := data.horizon_lower_bound hC hvol hN hNt hK hB hcap hcharts
  linarith

end

end Submission.Obl.k4_discrete_of_terminal_charts
