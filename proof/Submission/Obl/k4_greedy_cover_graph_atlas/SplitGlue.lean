import Submission.Obl.k4_greedy_cover_graph_atlas.SplitInterfaces

namespace Submission.Obl.k4_greedy_cover_graph_atlas

theorem preparation_of_density_and_finite
    (hdensity : DensityPreparation) (hfinite : FiniteConstruction) : Preparation := by
  intro hgraph hsheets hremez d₁ κ₁ hd₁ hd₁1 hκ₁ hκ₁1
  obtain ⟨θ, ρ, hθ, hθ1, hρ, hρ1, hdρ, hconstruct⟩ :=
    hfinite hgraph hsheets hremez d₁ κ₁ hd₁ hd₁1 hκ₁ hκ₁1
  refine ⟨θ, ρ, hθ, hθ1, hρ, hdρ, ?_⟩
  intro S η hS hη m s gain δ₀ hgrid hgain hgain1 hδ₀ hδρ
    N K L d W ω ν E P B f g G hprob hlin Mp Dp Mg Dg
  have hL : 0 < L := hprob.2.2.2.1
  obtain ⟨Mpr, Dpr, hpr⟩ := hprob.2.2.2.2.2.2.2.2.1
  have hscalar : ∀ k, ScalarData (N k) Mpr Dpr (W k) (ω k) (ν k) (E k) (B k) := by
    intro k
    obtain ⟨hW, hω, hsum, hw, _⟩ := hpr k
    refine ⟨hW, hω, hsum, ?_⟩
    intro w
    obtain ⟨hν, hB0, hB1, hB2, _, _, _, hE, _, _, hfmt, _, _⟩ := hw w
    exact ⟨hν, hB0, hB1, hB2, hE, hfmt⟩
  obtain ⟨M, D, hMD⟩ := hconstruct L m s gain δ₀ hL hgrid hgain hgain1 hδ₀ hδρ
    Mp Dp Mg Dg Mpr Dpr
  refine ⟨M, D, ?_⟩
  intro β hβ hβ1
  obtain ⟨τ, εf, σf, hτ, hεf, hεf1, hσf, hσf1, N₀, hN₀, hfin⟩ := hMD β hβ hβ1
  obtain ⟨εd, σd, hεd, hεd1, hσd, hσd1, k₀, hclean⟩ :=
    hdensity d₁ κ₁ S η ρ hd₁ hd₁1 hκ₁ hκ₁1 hS hη hρ hρ1 hdρ
      m s gain δ₀ hgrid hgain hgain1 hδ₀ hδρ
      N K L d W ω ν E P B f g G hprob Mp Dp Mg Dg τ hτ
  let ε : ℝ := min β (min εf εd)
  let σ : ℝ := min σf σd
  have hε : 0 < ε := lt_min hβ (lt_min hεf hεd)
  have hεβ : ε ≤ β := min_le_left _ _
  have hεf' : ε ≤ εf := (min_le_right _ _).trans (min_le_left _ _)
  have hεd' : ε ≤ εd := (min_le_right _ _).trans (min_le_right _ _)
  have hσ : 0 < σ := lt_min hσf hσd
  have hσf' : σ ≤ σf := min_le_left _ _
  have hσd' : σ ≤ σd := min_le_right _ _
  have hlate : ∀ᶠ k in Filter.atTop, N₀ ≤ N k := hprob.2.1.eventually_ge_atTop N₀
  obtain ⟨k₁, hk₁⟩ := Filter.eventually_atTop.mp hlate
  refine ⟨ε, σ, hε, hεf'.trans hεf1, hεβ, hσ, max k₀ k₁, ?_⟩
  intro k hk r T nw κ C lev par γ j c u Q R A F lst hpath hcover
  have hcleaned := hclean k ((le_max_left _ _).trans hk) ε σ hε hεd' hσ hσd'
    r T nw κ C lev par γ j c u Q R A F lst hpath hcover
  exact hfin (N k) (hk₁ k ((le_max_right _ _).trans hk))
    (W k) (ω k) (ν k) (E k) (B k) f (hscalar k) hlin ε σ hε hεf' hεβ hσ hσf'
    r T nw κ C lev par γ j c u Q R A F lst hpath hcleaned

end Submission.Obl.k4_greedy_cover_graph_atlas
