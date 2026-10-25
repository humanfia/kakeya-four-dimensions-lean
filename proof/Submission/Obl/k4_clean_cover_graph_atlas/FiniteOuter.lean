import Submission.Obl.k4_clean_cover_graph_atlas.SampleCore
import Submission.Obl.k4_clean_cover_graph_atlas.Prepare

namespace Submission.Obl.k4_clean_cover_graph_atlas

/-- Choose the uniform input tolerances after the analytic slack ratio, then
re-export the cleaned witness data around the per-sample label construction. -/
theorem finiteCore_of_sampleCore (hsc : SampleCore) : FiniteCore := by
  intro hgraph hsheets hremez d₁ κ₁ hd₁ hd₁1 hκ₁ hκ₁1
  obtain ⟨θ, ϖ, hθ, hθ4, hϖ, hrest⟩ := hsc hgraph hsheets hremez d₁ κ₁ hd₁ hd₁1 hκ₁ hκ₁1
  let ρ := min ϖ (min (1 / 4) ((1 - d₁) / 2))
  have hρ : 0 < ρ := lt_min hϖ (lt_min (by norm_num) (by linarith))
  have hρϖ : ρ ≤ ϖ := min_le_left _ _
  have hρ4 : ρ ≤ 1 / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hρd : ρ ≤ (1 - d₁) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hdρ : d₁ + ρ < 1 := by linarith
  refine ⟨θ, ρ, hθ, hθ4, hρ, hρ4, hdρ, ?_⟩
  intro L m s gain δ₀ hL hgrid hgain hgain1 hδ₀ hδρ Mp Dp Mg Dg Mpr Dpr
  obtain ⟨Mc, hMc⟩ := hrest ρ hρ hρϖ hdρ L m s gain δ₀ hL hgrid hgain hgain1 hδ₀ hδρ
    Mp Dp Mg Dg Mpr Dpr
  refine ⟨Mc, ?_⟩
  intro β hβ hβ1
  let τ := ϖ * gain * L / 4
  let ε₀ := min 1 (min (β / 2) τ)
  let σ₀ := min 1 (min (β / 8) τ)
  have hτ : 0 < τ := by dsimp only [τ]; positivity
  have hε₀ : 0 < ε₀ := lt_min (by norm_num) (lt_min (by positivity) hτ)
  have hσ₀ : 0 < σ₀ := lt_min (by norm_num) (lt_min (by positivity) hτ)
  have hε₀1 : ε₀ ≤ 1 := min_le_left _ _
  have hσ₀1 : σ₀ ≤ 1 := min_le_left _ _
  have hε₀β : ε₀ ≤ β / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hσ₀β : σ₀ ≤ β / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have hε₀τ : ε₀ ≤ τ := (min_le_right _ _).trans (min_le_right _ _)
  have hσ₀τ : σ₀ ≤ τ := (min_le_right _ _).trans (min_le_right _ _)
  have hsum : ε₀ + σ₀ + τ ≤ ϖ * gain * L := by dsimp only [τ] at *; linarith
  obtain ⟨N₀, hN₀2, hN₀⟩ := hMc β τ ε₀ σ₀ hβ hβ1 hτ hε₀ hε₀β hσ₀ hσ₀β hsum
  refine ⟨τ, ε₀, σ₀, hτ, hε₀, hε₀1, hσ₀, hσ₀1, by linarith, N₀, hN₀2, ?_⟩
  intro Nk hNk W ω ν E B f hdata hlin ε σ hε hεbound hεβ hσ hσbound
    r T nw κ C lev par γ j c u Q R A F lst hpath hcover
  obtain ⟨i, h, n, old, R', A', V, U, hbody⟩ := hcover
  obtain ⟨s₀, K', htime, hs₀, hK', hout⟩ := hN₀ Nk hNk W ω ν E B f hdata hlin ε σ
    hε hεbound hσ hσbound r T nw κ C lev par γ j c u Q R A F lst hpath
    i h n old R' A' V U hbody
  obtain ⟨hi, hgh, hh, -, hmargin, hn, hentry, -, hdisj, -, -, -⟩ := hbody
  refine ⟨i, h, n, old, R', A', s₀, K', hi, hgh, hh, hmargin, hn, ?_, hdisj, htime, hs₀, hK', hout⟩
  intro a
  obtain ⟨hlev, -, hdegree, -, -, hsub, hfmt, -⟩ := hentry a
  exact ⟨hlev, hdegree, hsub, hfmt⟩

/-- The numerical outer layer and checked geometric assembly leave only the
single-sample analytic construction. -/
theorem finiteConstruction_of_sampleCore (hsc : SampleCore) : FiniteConstruction :=
  finiteConstruction_of_core (finiteCore_of_sampleCore hsc)

end Submission.Obl.k4_clean_cover_graph_atlas
