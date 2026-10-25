import Submission.Obl.k4_finite_width_output_exclusion.Exclusions
import Submission.Obl.k4_finite_width_output_exclusion.Compactness

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Submission.Obl.k4_finite_width_output_exclusion

open MeasureTheory Filter

noncomputable section

lemma prove_statement : Statement := by
  unfold Statement
  intro hcRaw hiRaw ds kr ell S η hS hη hesRaw hell hunifRaw
    zeta a Δ e0 hzeta hΔ ha he0 m s hgrid
  have hc : Composition := by
    intro p hp r h w hr hrL hk
    have hcomp := hcRaw p.N p.K p.L p.d p.S p.η p.W p.ω p.ν p.E p.P p.B p.f p.g p.G
      hp r h w hr hrL
    obtain ⟨N', K', W', ω', ν', E', P', B', f', g', G', hv, ht, hn⟩ := hcomp (by
      obtain ⟨M, D, hk⟩ := hk
      refine ⟨M, D, fun ε hε => (hk ε hε).mono ?_⟩
      rintro k ⟨κ, hκ, hκε, a, hT, hw, ⟨hC, hd, hchart, hmass⟩, hlst⟩
      exact ⟨κ, hκ, hκε, a.T, a.C, a.γ, a.j, a.c, a.u, a.Q, a.R, a.A, a.F, a.lst,
        hT, hw, hC, hd, hlst, hchart, hmass⟩)
    exact ⟨⟨N', K', p.L - r, p.d, p.S, p.η, W', ω', ν', E', P', B', f', g', G'⟩,
      hv, rfl, rfl, rfl, rfl, ht, hn⟩
  have hi : Initial := by
    intro p hp h hh
    exact hiRaw p.N p.K p.L p.d p.S p.η p.W p.ω p.ν p.E p.P p.B p.f p.g p.G hp h hh
  have hes : Extremal ds kr S η := by
    rcases hesRaw with ⟨hds, hds1, hkr, hkr1, hex, hupper, hlinear⟩
    refine ⟨hds, hds1, hkr, hkr1, ?_, ?_, ?_⟩
    · intro t ht
      obtain ⟨N, K, d, W, ω, ν, E, P, B, f, g, G, hp, hd, hH⟩ := hex t ht
      exact ⟨⟨N, K, 1, d, S, η, W, ω, ν, E, P, B, f, g, G⟩,
        hp, rfl, rfl, rfl, hd, hH⟩
    · intro t ht
      obtain ⟨b, hb, hh⟩ := hupper t ht
      refine ⟨b, hb, ?_⟩
      intro p hp hpS hpη hd
      exact hh p.N p.K p.L p.d p.W p.ω p.ν p.E p.P p.B p.f p.g p.G
        (by simpa only [Valid, hpS, hpη] using hp) hd
    · intro t ht
      obtain ⟨b, hb, hh⟩ := hlinear t ht
      refine ⟨b, hb, ?_⟩
      intro p hp hpS hpη hd hH
      exact hh p.N p.K p.L p.d p.W p.ω p.ν p.E p.P p.B p.f p.g p.G
        (by simpa only [Valid, hpS, hpη] using hp) hd hH
  have hunif : ∀ z : ℝ, 0 < z → UniformWidth ds kr S η (max 0 (ell - z)) := by
    intro z hz a ha
    obtain ⟨t, ht, hh⟩ := hunifRaw z hz a ha
    refine ⟨t, ht, ?_⟩
    intro p hp hpL hpS hpη hd hH
    have hh' := hh p.N p.K p.d p.W p.ω p.ν p.E p.P p.B p.f p.g p.G
      (by simpa only [Valid, hpL, hpS, hpη] using hp) hd
      (by simpa only [Horizon, hpL] using hH)
    simpa only [Narrow, hpL] using hh'
  obtain ⟨e, t, he, hee0, ht, hno⟩ :=
    choose_no_improvement hc hi hes hell hunif hzeta hΔ ha he0
  refine ⟨e, t, he, hee0, ht, ?_⟩
  intro N K d W ω ν E P B f g G hp hd hH hbad M D
  let p : Data := ⟨N, K, 1, d, S, η, W, ω, ν, E, P, B, f, g, G⟩
  have hpV : Valid p := hp
  have hkr : 0 ≤ kr := hes.2.2.1.le
  have hΔpos : 0 < Δ := by linarith
  have hno' : ∀ φ : ℕ → ℕ, Tendsto φ atTop atTop →
      NoImprovement (p.reindex φ) kr ell Δ zeta e := by
    intro φ hφ
    apply hno (p.reindex φ) (valid_reindex hpV hφ) rfl rfl rfl hd
    · exact hH.trans_le (horizon_reindex_le hi hpV hφ)
    · intro hn
      exact hbad (narrow_of_reindex hφ hn)
  obtain ⟨τ, hτ, hlate⟩ := eventual_improved_exclusion hpV rfl s hkr hΔpos he.le hno' M D
  refine ⟨τ, hτ, hlate.mono ?_⟩
  intro k hk r T nw hpath hout
  apply hk r T nw hpath
  rcases hout with ⟨r₂, T₂, C₂, γ₂, j₂, c₂, u₂, Q₂, R₂, A₂, F₂, lst₂,
    hrΔ, hcases, hC, hdisj, hlst, hcharts, hmass⟩
  refine ⟨r₂, ⟨T₂, C₂, γ₂, j₂, c₂, u₂, Q₂, R₂, A₂, F₂, lst₂⟩,
    hrΔ, hcases, ⟨hC, hdisj, hcharts, ?_⟩, hlst⟩
  have hpower : N k ^ (-τ) = (N k ^ τ)⁻¹ := Real.rpow_neg (hpV.scale_pos k).le τ
  rw [hpower] at hmass
  exact hmass

end
end Submission.Obl.k4_finite_width_output_exclusion
