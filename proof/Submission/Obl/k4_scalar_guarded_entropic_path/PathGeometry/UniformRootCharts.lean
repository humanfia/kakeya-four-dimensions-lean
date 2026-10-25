/-
Adapted from this LOT tree, obligation o093, session x0535, commit 62576536,
Submission/Obl/k4_scalar_critical_path_terminal/UniformRootCharts.lean. Original attribution is retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.RootTerminalCharts

/-! Declare a SINGLE original integer complexity for all root TRUE prefixes
before any inner tolerance, sample, residual or candidate is chosen. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.TrueGridPath

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_scalar_true_terminal_lifting (ChartW)
open PathMeasures IntermediateLiftSupport TrueLiftChains

noncomputable section

variable {ctx : CriticalContext} {source : MaximizingFamily ctx}
  {start : ℝ} {targets : List ℝ}

def uniformPrefixBudget (path : TrueGridPath ctx source start targets)
    (i : ℕ) (certs : path.Certificates i) : ℕ :=
  max 1 (Finset.univ.sup (path.prefixBudget i certs))

theorem uniformPrefixBudget_one (path : TrueGridPath ctx source start targets)
    (i : ℕ) (certs : path.Certificates i) : 1 ≤ path.uniformPrefixBudget i certs :=
  le_max_left _ _

theorem prefixBudget_le_uniform (path : TrueGridPath ctx source start targets)
    (i : ℕ) (certs : path.Certificates i) (j : Fin targets.length) :
    path.prefixBudget i certs j ≤ path.uniformPrefixBudget i certs :=
  (Finset.le_sup (Finset.mem_univ j)).trans (le_max_right _ _)

abbrev UniformRootTerminalChart (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (ε : ℝ) (k : ℕ) (j : Fin targets.length) :=
  ChartW (source.problem i) (path.uniformPrefixBudget i certs)
    (path.prefixDepth i j) (L (source.problem i)) (path.prefixCost i j + ε) ε true
      ((path.measuredChain i certs).sample k)

/-- One fixed original complexity serves all prefixes; every actual field
matches the deterministic path geometry and all later AC residuals stay covered. -/
theorem eventually_uniform_root_terminal_charts (path : TrueGridPath ctx source start targets)
    (i : ℕ) (certs : path.Certificates i) (hl : path.forget.AllLayers i)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ j : Fin targets.length,
      ∃ P : path.UniformRootTerminalChart i certs ε k j,
        ChartGeometry.ofChart P = path.rootGeometry i certs k j ∧
        ∀ ρ : Measure (Fin (W (path.forget.finalFamily.problem i) k) × PathMeasures.State),
          ρ ≪ worldMixture (path.forget.finalFamily.problem i) k →
          ∀ᵐ u ∂ρ.map ((path.measuredChain i certs).pullback k), u ∈ chartRegion P := by
  filter_upwards [path.eventually_root_terminal_charts_with_geometry i certs hl ε hε] with k hk
  intro j
  obtain ⟨Q, hgeometry, hcover⟩ := hk j
  have hN : 1 ≤ N (source.problem i) ((path.measuredChain i certs).sample k) :=
    (by norm_num : (1 : ℝ) ≤ 2).trans ((source.angular i).1.1.1 _)
  exact ⟨relaxChart Q hN (path.prefixBudget_le_uniform i certs j) le_rfl le_rfl,
    hgeometry, hcover⟩

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.TrueGridPath
