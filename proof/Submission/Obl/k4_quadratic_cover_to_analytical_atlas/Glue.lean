import Submission.Obl.k4_quadratic_cover_to_analytical_atlas.Certificates
import Submission.Obl.k4_quadratic_cover_to_analytical_atlas.ObservationImages

namespace Submission.Obl.k4_quadratic_cover_to_analytical_atlas

/-- Only the original quantifier order, late-sample bounds and old-level alternative
remain after the two certificates have been constructed. -/
theorem statement_of_certificates (prepare : Preparation) (realize : Realization) : Statement := by
  intro hgraph hjets hsheets hremez d₁ κ₁ hd₁ hd₁1 hκ₁ hκ₁1
  obtain ⟨θ, ρ, hθ, hθ1, hρ, hdρ, hprepare⟩ :=
    prepare hgraph hsheets hremez d₁ κ₁ hd₁ hd₁1 hκ₁ hκ₁1
  refine ⟨θ / 4, ρ, by positivity, by linarith, hρ, hdρ, ?_⟩
  intro S η hS hη m s gain δ₀ hgrid hgain hgain1 hδ₀ hδρ
    N K L d W ω ν E P B f g G hprob hlinear Mp Dp Mg Dg
  obtain ⟨M, D, hM⟩ := hprepare S η hS hη m s gain δ₀ hgrid hgain hgain1 hδ₀ hδρ
    N K L d W ω ν E P B f g G hprob hlinear Mp Dp Mg Dg
  obtain ⟨M', hMM', hrealize⟩ := realize M
  refine ⟨M', D, ?_⟩
  intro ζ hζ hζ1
  have hβ : 0 < ζ / 4 := by positivity
  have hβ1 : ζ / 4 ≤ 1 := by linarith
  obtain ⟨ε, σ, hε, hε1, hεβ, hσ, k₀, hk₀⟩ := hM (ζ / 4) hβ hβ1
  have hL : 0 < L := hprob.2.2.2.1
  obtain ⟨N₀, hN₀, hlarge⟩ := hrealize L θ gain ζ hL hθ hθ1 hgain hgain1 hζ hζ1
  have hev : ∀ᶠ k in Filter.atTop, N₀ ≤ N k :=
    Filter.tendsto_atTop.mp hprob.2.1 N₀
  obtain ⟨k₁, hk₁⟩ := Filter.eventually_atTop.mp hev
  refine ⟨ε, σ, hε, hε1, by linarith, hσ, max k₀ k₁, ?_⟩
  intro k hk r T nw κ C lev par γ j c u Q R A F lst hpath hcover
  obtain ⟨i, h, T₂, C₂, γ₂, j₂, c₂, u₂, Q₂, P₂, scale, A₂, F₂, lst₂,
      hi, hgh, hh, hmargin, htime, hcert⟩ :=
    hk₀ k ((le_max_left _ _).trans hk) r T nw κ C lev par γ j c u Q R A F lst hpath hcover
  have hr : 0 ≤ r i := ((hpath.2.2.2.2.1 i hi).2.1).le
  obtain ⟨r₃, C₃, γ₃, j₃, c₃, u₃, Q₃, R₃, A₃, F₃, lst₃,
      hdepth, hend, hfinal⟩ :=
    hlarge (N k) (hk₁ k ((le_max_right _ _).trans hk))
      (W k) (ω k) (ν k) (E k) (B k) (r i) h (ζ / 4) D T₂ C₂
      γ₂ j₂ c₂ u₂ Q₂ P₂ scale A₂ F₂ lst₂ hr hgh hh hmargin hβ le_rfl hcert
  rcases hfinal with ⟨hcount, hdisjoint, hlists, hmeas, hcharts, hmass⟩
  refine ⟨r₃, T₂, C₃, γ₃, j₃, c₃, u₃, Q₃, R₃, A₃, F₃, lst₃,
    hend, Or.inr ⟨i, hi, hdepth, htime⟩,
    hcount, hdisjoint, hlists, hmeas, hcharts, hmass⟩

end Submission.Obl.k4_quadratic_cover_to_analytical_atlas
