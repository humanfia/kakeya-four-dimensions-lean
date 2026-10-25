import Submission.Obl.k4_raw_critical_segment_forests.Statement
import Submission.Obl.k4_raw_critical_segment_forests.PrefixInterface

set_option maxRecDepth 4096

namespace Submission.Obl.k4_raw_critical_segment_forests

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

lemma grid_monotone {m : ℕ} {s : ℕ → ℝ}
    (hstep : ∀ i, i + 1 < m → s i < s (i + 1)) :
    ∀ i j, i ≤ j → j < m → s i ≤ s j := by
  intro i j
  induction j with
  | zero =>
      intro hij hj
      have hi : i = 0 := by omega
      subst i
      exact le_rfl
  | succ j ih =>
      intro hij hj
      by_cases hi : i ≤ j
      · exact (ih hi (by omega)).trans (hstep j hj).le
      · have hi' : i = j + 1 := by omega
        subst i
        exact le_rfl

/-- The named forest predicates elaborate to the frozen lambda-expanded
statement. All concrete problem data are retained in both directions. -/
theorem statement_of_prefix (hprefix : PrefixConstruction) : Statement := by
  unfold Statement
  intro hprepRaw hcRaw hiRaw ds kr S η w hS hη hesRaw hw hunifRaw
    m s hgrid ε q hε hε1 hq
  change es ds kr S η at hesRaw
  change unif ds kr S η w at hunifRaw
  have hprep : Preparation := by
    intro p hp m r hm hr M D
    obtain ⟨M', D', hM, hD, hpre⟩ := hprepRaw p.N p.K p.L p.d p.S p.η
      p.W p.ω p.ν p.E p.P p.B p.f p.g p.G hp m r hm hr M D
    refine ⟨M', D', hM, hD, ?_⟩
    intro σ hσ
    obtain ⟨ρ, hρ, hρσ, hlate⟩ := hpre σ hσ
    refine ⟨ρ, hρ, hρσ, hlate.mono ?_⟩
    intro k hk a hκ hT hcore
    have hcore' := hcore
    unfold Forest.Core at hcore'
    rw [hκ] at hcore'
    obtain ⟨C', emb, par', F', lst, hC, hnew, hsub, hlist, hprior, hfinite, hbudget⟩ :=
      hk a.T a.C a.lev a.par a.γ a.j a.c a.u a.Q a.R a.A a.F hT hcore'
    exact ⟨⟨C', emb, par', F'⟩, lst, hC, hnew, hsub, hlist, hprior⟩
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
        (by change prob p.N p.K p.L p.d S η p.W p.ω p.ν p.E p.P p.B p.f p.g p.G; rw [← hpS, ← hpη]; exact hp) hd
    · intro t ht
      obtain ⟨b, hb, hh⟩ := hlinear t ht
      refine ⟨b, hb, ?_⟩
      intro p hp hpS hpη hd hH
      exact hh p.N p.K p.L p.d p.W p.ω p.ν p.E p.P p.B p.f p.g p.G
        (by change prob p.N p.K p.L p.d S η p.W p.ω p.ν p.E p.P p.B p.f p.g p.G; rw [← hpS, ← hpη]; exact hp) hd hH
  have hunif : UniformWidth ds kr S η w := by
    intro a ha
    obtain ⟨t, ht, hh⟩ := hunifRaw a ha
    refine ⟨t, ht, ?_⟩
    intro p hp hpL hpS hpη hd hH
    have hh' := hh p.N p.K p.d p.W p.ω p.ν p.E p.P p.B p.f p.g p.G
      (by change prob p.N p.K 1 p.d S η p.W p.ω p.ν p.E p.P p.B p.f p.g p.G; rw [← hpL, ← hpS, ← hpη]; exact hp) hd
      (by change kr - t < H p.N p.K 1 p.W p.ω p.ν p.E p.B p.f; rw [← hpL]; exact hH)
    change nt p.N p.K p.L p.W p.ω p.ν p.E p.B p.f (kr + a) w
    rw [hpL]
    exact hh'
  obtain ⟨hm, hs0, hstep, hsfinal⟩ := hgrid
  have hs : ∀ i, i < m → 0 < s i ∧ s i ≤ 1 := by
    intro i hi
    have h0i := grid_monotone hstep 0 i (Nat.zero_le i) hi
    have hi1 := grid_monotone hstep i (m - 1) (by omega) (by omega)
    exact ⟨hs0.trans_le h0i, hi1.trans_eq hsfinal⟩
  obtain ⟨t, ht, hforests⟩ := hprefix hprep hc hi ds kr S η w hes hw hunif
    m s hm hs hstep ε q hε hε1 hq
  refine ⟨t, ht, ?_⟩
  intro N K d W ω ν E P B f g G hp hd hH
  let p : Data := ⟨N, K, 1, d, S, η, W, ω, ν, E, P, B, f, g, G⟩
  obtain ⟨r, M, D, hr, hfrequent⟩ := hforests p hp rfl rfl rfl hd hH
  refine ⟨r, M, D, (hr (m - 1) (by omega)).2.2.2 hsfinal, ?_, ?_⟩
  · intro i hi
    exact ⟨(hr i hi).1, (hr i hi).2.1, (hr i hi).2.2.1.trans (hs i hi).2⟩
  · intro σ hσ
    apply (hfrequent σ hσ).mono
    rintro k ⟨a, width, hκ, hcore, htime, hwidth⟩
    exact ⟨a.κ, a.T, a.C, a.lev, a.par, a.γ, a.j, a.c, a.u, a.Q, a.R, a.A, a.F,
      width, hκ, hcore, htime, hwidth⟩

end
end Submission.Obl.k4_raw_critical_segment_forests
