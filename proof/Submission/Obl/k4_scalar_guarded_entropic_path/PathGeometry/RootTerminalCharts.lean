/-
Adapted from this LOT tree, obligation o093, session x0535, commit 62576536,
Submission/Obl/k4_scalar_critical_path_terminal/RootTerminalCharts.lean. Original attribution is retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.RootPrefixCharts
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.FinerKnowledge

/-! Upgrade all common root TRUE prefix charts to the original terminal
observation, keeping their full assignments, geometry and selected events. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.TrueGridPath

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_scalar_true_terminal_lifting (ChartW chartData_mono)
open PathMeasures IntermediateLiftSupport

noncomputable section

variable {ctx : CriticalContext} {source : MaximizingFamily ctx}
  {start : ℝ} {targets : List ℝ}

abbrev RootTerminalChart (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (ε : ℝ) (k : ℕ) (j : Fin targets.length) :=
  ChartW (source.problem i) (path.prefixBudget i certs j)
    (path.prefixDepth i j) (L (source.problem i)) (path.prefixCost i j + ε) ε true
      ((path.measuredChain i certs).sample k)

/-- On one common final-inner tail, EVERY actual original prefix has a
TRUE chart with original TERMINAL lists and the same common-law coverage. -/
theorem eventually_root_terminal_charts_with_geometry (path : TrueGridPath ctx source start targets)
    (i : ℕ) (certs : path.Certificates i) (hl : path.forget.AllLayers i)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ j : Fin targets.length,
      ∃ P : path.RootTerminalChart i certs ε k j,
        ChartGeometry.ofChart P = path.rootGeometry i certs k j ∧
        ∀ ρ : Measure (Fin (W (path.forget.finalFamily.problem i) k) × PathMeasures.State),
          ρ ≪ worldMixture (path.forget.finalFamily.problem i) k →
          ∀ᵐ u ∂ρ.map ((path.measuredChain i certs).pullback k), u ∈ chartRegion P := by
  have hε4 : 0 < ε / 4 := by positivity
  have hcharts := path.eventually_root_charts_with_geometry i certs hl (ε / 4) hε4
  have hN4 : ∀ᶠ k in atTop,
      4 ≤ N (source.problem i) ((path.measuredChain i certs).sample k) ^ (ε / 2) :=
    ((tendsto_rpow_atTop (show 0 < ε / 2 by positivity)).comp
      ((source.angular i).1.1.2.1.comp
        (path.measuredChain i certs).sample_strictMono.tendsto_atTop)).eventually_ge_atTop 4
  filter_upwards [hcharts, hN4] with k hk h4
  intro j
  obtain ⟨Q, hgeometry, hcover⟩ := hk j
  have hN : 0 < N (source.problem i) ((path.measuredChain i certs).sample k) := by
    linarith [(source.angular i).1.1.1 ((path.measuredChain i certs).sample k)]
  have hN₁ : 1 ≤ N (source.problem i) ((path.measuredChain i certs).sample k) := by
    linarith [(source.angular i).1.1.1 ((path.measuredChain i certs).sample k)]
  have hfactor : 4 * N (source.problem i) ((path.measuredChain i certs).sample k) ^ (ε / 4) ≤
      N (source.problem i) ((path.measuredChain i certs).sample k) ^ ε := by
    calc
      _ ≤ N (source.problem i) ((path.measuredChain i certs).sample k) ^ (ε / 2) *
          N (source.problem i) ((path.measuredChain i certs).sample k) ^ (ε / 2) :=
        mul_le_mul h4 (Real.rpow_le_rpow_of_exponent_le hN₁ (by linarith))
          (Real.rpow_nonneg hN.le _) (Real.rpow_nonneg hN.le _)
      _ = _ := by rw [← Real.rpow_add hN]; congr 1; ring
  obtain ⟨Λ, hc⟩ := chartData_finerKnowledge hN₁
    (path.prefixDepth_bounds i hl j).2.le (show ε / 4 ≤ ε by linarith) hfactor Q.hcd
  let P : path.RootTerminalChart i certs ε k j :=
    ⟨Q.T, Q.n, Q.γ, Q.j, Q.A, Q.C, Q.u, Q.v, Q.J, Q.P, Λ,
      Submission.Obl.k4_scalar_true_terminal_lifting.chartData_mono hc hN₁ le_rfl (show path.prefixCost i j + ε / 4 ≤ path.prefixCost i j + ε by linarith)
        le_rfl⟩
  exact ⟨P, hgeometry, hcover⟩

/-- The common original-terminal TRUE charts, retaining the prior public
coverage API while the stronger theorem also exposes all field identities. -/
theorem eventually_root_terminal_charts (path : TrueGridPath ctx source start targets)
    (i : ℕ) (certs : path.Certificates i) (hl : path.forget.AllLayers i)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ j : Fin targets.length,
      ∃ P : path.RootTerminalChart i certs ε k j,
        ∀ ρ : Measure (Fin (W (path.forget.finalFamily.problem i) k) × PathMeasures.State),
          ρ ≪ worldMixture (path.forget.finalFamily.problem i) k →
          ∀ᵐ u ∂ρ.map ((path.measuredChain i certs).pullback k), u ∈ chartRegion P := by
  filter_upwards [path.eventually_root_terminal_charts_with_geometry i certs hl ε hε] with k hk
  intro j
  obtain ⟨P, _, hcover⟩ := hk j
  exact ⟨P, hcover⟩

/-- Actual certificates and simultaneous layer laws occur on one outer
tail. Every complexity is fixed before the declared inner tolerance. -/
theorem eventually_certified_root_terminal_charts (path : TrueGridPath ctx source start targets) :
    ∀ᶠ i in atTop, ∃ certs : path.Certificates i,
      ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ j : Fin targets.length,
        ∃ P : path.RootTerminalChart i certs ε k j,
          ∀ ρ : Measure (Fin (W (path.forget.finalFamily.problem i) k) × PathMeasures.State),
            ρ ≪ worldMixture (path.forget.finalFamily.problem i) k →
            ∀ᵐ u ∂ρ.map ((path.measuredChain i certs).pullback k), u ∈ chartRegion P := by
  filter_upwards [path.eventually_certificates, path.forget.eventually_allLayers] with i hc hl
  obtain ⟨certs⟩ := hc
  exact ⟨certs, fun ε hε => path.eventually_root_terminal_charts i certs hl ε hε⟩

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.TrueGridPath
