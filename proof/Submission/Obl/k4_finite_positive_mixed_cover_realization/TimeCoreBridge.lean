import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCore
import Submission.Obl.k4_finite_positive_mixed_cover_realization.Path
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.SampleInput
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.Kernels
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.FinalCore
import Submission.Obl.k4_local_algebraic_graph_matching
import Submission.Obl.k4_stable_quadratic_hidden_sheets
import Submission.Obl.k4_algebraic_sheet_remez

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

open MeasureTheory

/-- The graph-atlas analysis needs no numerical value for cumulative
narrowness. Every original positive path supplies its weaker path interface. -/
lemma PathData.Valid.analytic_path
    {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {s : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ) :
    TimeCoreBridge.path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ
      p.r p.T p.nw p.κ p.C p.lev p.par p.world p.bin p.center p.velocity p.frame
        p.test p.assigned p.counted p.lists := by
  refine ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, ?_, hp.2.2.2.2.2.1,
    hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2⟩
  intro i hi
  obtain ⟨h1, h2, h3, h4, -, h6⟩ := hp.level_bounds i hi
  exact ⟨h1, h2, h3, h4, trivial, h6⟩

/-- The weaker finite analytic construction gives exactly the positive-path
time core; all actual arrays, measures and frame determinants are preserved. -/
theorem timeCore_of_finiteAnalyticConstruction
    (hfc : TimeCoreBridge.FiniteConstruction) : TimeCore := by
  intro hMatch ℓ d₁ κ₁ hd₁ hd₁1 hκ₁ hκ₁1
  have hgraph : TimeCoreBridge.localGraph := Submission.k4_local_algebraic_graph_matching hMatch
  have hsheets : TimeCoreBridge.stableSheets := Submission.k4_stable_quadratic_hidden_sheets
  have hremez : TimeCoreBridge.algebraicRemez := Submission.k4_algebraic_sheet_remez
  obtain ⟨θ, ρ, hθ, hθ4, hρ, hρ4, hdρ, hrest⟩ :=
    hfc hgraph hsheets hremez d₁ κ₁ hd₁ hd₁1 hκ₁ hκ₁1
  refine ⟨θ, ρ, hθ, hθ4, hρ, hρ4, hdρ, ?_⟩
  intro L m s gain δ₀ hL hgrid hgain hgain1 hδ₀ hδρ Mp Dp Mg Dg Mpr Dpr
  obtain ⟨M, D, hMD⟩ := hrest L m s gain δ₀ hL hgrid hgain hgain1 hδ₀ hδρ
    Mp Dp Mg Dg Mpr Dpr
  refine ⟨M, D, ?_⟩
  intro β hβ hβ1
  obtain ⟨τ, ε₀, σ₀, hτ, hε₀, hε₀1, hσ₀, hσ₀1, N₀, hN₀, hsample⟩ := hMD β hβ hβ1
  refine ⟨τ, ε₀, σ₀, hτ, hε₀, hε₀1, hσ₀, hσ₀1, N₀, hN₀, ?_⟩
  intro Nk hNk W ω ν E B f hscalar hlin ε σ hε hεε₀ hεβ hσ hσσ₀
    r T nw κ C lev par γ j c u Q R A F lst hpath hclean
  let p : PathData W := ⟨r, T, nw, κ, C, lev, par, γ, j, c, u, Q, R, A, F, lst⟩
  have hp : p.Valid ℓ Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ := hpath
  exact hsample Nk hNk W ω ν E B f hscalar hlin ε σ hε hεε₀ hεβ hσ hσσ₀
    r T nw κ C lev par γ j c u Q R A F lst hp.analytic_path hclean

/-- The reusable single-sample analytic statement is the remaining input
to the time branch. All finite assembly and outer numerical choices are done. -/
theorem timeCore_of_preparedSampleCore (hsc : TimeCoreBridge.PreparedSampleCore) : TimeCore :=
  timeCore_of_finiteAnalyticConstruction (TimeCoreBridge.finiteConstruction_of_preparedSampleCore hsc)

/-- The graph-atlas core for the original positive-narrowness path. -/
theorem timeCore : TimeCore := timeCore_of_preparedSampleCore TimeCoreBridge.preparedSampleCore

end Submission.Obl.k4_finite_positive_mixed_cover_realization
