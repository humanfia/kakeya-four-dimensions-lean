import Submission.Obl.k4_finite_positive_prepared_models.FlatCut
import Submission.Obl.k4_finite_positive_prepared_models.InitialStages

namespace Submission.Obl.k4_finite_positive_prepared_models

noncomputable section

/-- Enlarging the original polynomial coefficient budget preserves either
kind of candidate; the mass and fitting allowances are unchanged. -/
theorem mixedCandidate_mono_budget
    {Nk L : ℝ} {W : ℕ} {ν : Fin W → MeasureTheory.Measure Trajectory}
    {B : Fin W → ℝ} {M M' : ℕ} {d₁ ρ gain ε : ℝ}
    {r : ℕ → ℝ} {T : ℕ → ℕ} {C : ℕ} {lev : Fin C → ℕ}
    {γ : Fin C → Fin W} {j : Fin C → ℕ}
    {u : Fin C → EuclideanSpace ℝ (Fin 2)} {Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ}
    {A : Fin C → Set Trajectory} {H : Fin W → Set Incidence}
    (hNk : 1 ≤ Nk) (hM : M ≤ M')
    (h : MixedCandidate Nk L W ν B M d₁ ρ gain ε r T C lev γ j u Q A H) :
    MixedCandidate Nk L W ν B M' d₁ ρ gain ε r T C lev γ j u Q A H := by
  obtain ⟨b, h, hg, hu, hr, hp, hc⟩ := h
  refine ⟨b, h, hg, hu, hr, hp, ?_⟩
  rcases hc with ⟨R, hd, hb, hm⟩ | ⟨a, z, ha, hz, hm⟩
  · exact Or.inl ⟨R, hd, fun e => (hb e).trans (pow_le_pow_right₀ hNk hM), hm⟩
  · exact Or.inr ⟨a, z, ha, hz.trans (pow_le_pow_right₀ hNk hM), hm⟩

/-- Repack the explicit fifteen-field synthetic model. -/
theorem synthetic_of_flat (h : FlatSynthetic) : SyntheticModels := by
  intro d₁ κ₁ ℓ S hd hd' hκ hκ' hℓ hS hS' n hn
  obtain ⟨sN, sK, sν, sμ, sρ, sπ, sb, sP, sT, sn, sj, sA, sB, sc, sF, hg⟩ :=
    h d₁ κ₁ ℓ S hd hd' hκ hκ' hℓ hS hS' n hn
  exact ⟨⟨sN, sK, sν, sμ, sρ, sπ, sb, sP, sT, sn, sj, sA, sB, sc, sF⟩, hg⟩

/-- Repack the actual path and native fields without changing any law. -/
theorem sourcePreparation_of_flat (h : FlatSourcePreparation) : SourcePreparation := by
  intro d₁ κ₁ ℓ S η ρ hd hd' hκ hκ' hℓ hS hS' hη hρ hρ' n hn
  obtain ⟨m, s, gain, δ₀, unit, hg, hgain, hgain', hδ, hδ', h⟩ :=
    h d₁ κ₁ ℓ S η ρ hd hd' hκ hκ' hℓ hS hS' hη hρ hρ' n hn
  refine ⟨m, s, gain, δ₀, unit, hg, hgain, hgain', hδ, hδ', ?_⟩
  intro N K L d W ω ν E P B f g G hprob hprof Mp Dp
  obtain ⟨M, h⟩ := h N K L d W ω ν E P B f g G hprob hprof Mp Dp
  refine ⟨M, fun ε hε => ?_⟩
  obtain ⟨σ, hσ, k₀, h⟩ := h ε hε
  refine ⟨σ, hσ, k₀, ?_⟩
  intro k hk p hp H hH hmass
  rcases h k hk p.r p.T p.nw p.κ p.C p.lev p.par p.world p.bin p.center p.velocity
      p.frame p.test p.assigned p.counted p.lists hp H hH hmass with hfound | hmodel
  · exact Or.inl hfound
  · obtain ⟨sN, sK, sν, sμ, sρ, sπ, sb, sP, sT, sn, sj, sA, sB, sc, sF, hg, hs⟩ := hmodel
    exact Or.inr ⟨⟨sN, sK, sν, sμ, sρ, sπ, sb, sP, sT, sn, sj, sA, sB, sc, sF⟩, hg, hs⟩

/-- Repack the universally quantified source without choosing it. -/
theorem sourceReturn_of_flat (h : FlatSourceReturn) : SourceReturn := by
  intro n M
  obtain ⟨Mc, h⟩ := h n M
  refine ⟨Mc, ?_⟩
  intro d₁ κ₁ ℓ ρ gain ε unit Nk L W ω ν E B f m s δ₀ Mp Dp σ p H st hp hH hs
  exact h d₁ κ₁ ℓ ρ gain ε unit Nk L W ω ν E B f m s δ₀ Mp Dp σ
    p.r p.T p.nw p.κ p.C p.lev p.par p.world p.bin p.center p.velocity p.frame p.test
    p.assigned p.counted p.lists H st.N st.K st.ν st.μ st.ρ st.π st.b st.P
    st.T st.nl st.j st.A st.B st.c st.F hp hH hs

/-- The source alternative and independent return give the finite models.
A found original candidate uses an independent synthetic model. -/
theorem stageModels_of_sources (hsyn : SyntheticModels) (hprep : SourcePreparation)
    (hreturn : SourceReturn) : StageModels := by
  intro d₁ κ₁ ℓ S η ρ hd hd' hκ hκ' hℓ hS hS' hη hρ hρ' n
  by_cases hn : n ≤ 1
  · exact stageReady_small d₁ κ₁ ℓ S η ρ hρ n hn
  have hn' : 2 ≤ n := by omega
  obtain ⟨m, s, gain, δ₀, unit, hg, hgain, hgain', hδ, hδ', hprep⟩ :=
    hprep d₁ κ₁ ℓ S η ρ hd hd' hκ hκ' hℓ hS hS' hη hρ hρ' n hn'
  refine ⟨m, s, gain, δ₀, hg, hgain, hgain', hδ, hδ', ?_⟩
  intro N K L d W ω ν E P B f g G hprob hprof Mp Dp
  obtain ⟨M, hprep⟩ := hprep N K L d W ω ν E P B f g G hprob hprof Mp Dp
  obtain ⟨Mc, hreturn⟩ := hreturn n M
  refine ⟨max M Mc, fun ε hε => ?_⟩
  obtain ⟨σ, hσ, k₀, hprep⟩ := hprep ε hε
  refine ⟨σ, hσ, k₀, ?_⟩
  intro k hk r T nw κ C lev par γ j c u Q R A F lst hp H hH hmass
  let p : PathData (W k) := ⟨r, T, nw, κ, C, lev, par, γ, j, c, u, Q, R, A, F, lst⟩
  have hp' : p.Valid ℓ (N k) L (ω k) (ν k) (E k) (B k) f κ₁ m s δ₀ Mp Dp σ := hp
  have hNk : 1 ≤ N k := le_trans (by norm_num) (hprob.1 k)
  rcases hprep k hk p hp' H hH hmass with hfound | ⟨st, hg, hs⟩
  · obtain ⟨st, hg⟩ := hsyn d₁ κ₁ ℓ S hd hd' hκ hκ' hℓ hS hS' n hn'
    refine ⟨st, hg, ?_⟩
    intro R hR hRn ε' hε' hε'' hcan
    exact mixedCandidate_mono_budget hNk (le_max_left M Mc) hfound
  · refine ⟨st, hg, ?_⟩
    intro R hR hRn ε' hε' hε'' hcan
    apply mixedCandidate_mono_budget hNk (le_max_right M Mc)
    exact hreturn d₁ κ₁ ℓ ρ gain ε unit (N k) L (W k) (ω k) (ν k) (E k) (B k) f
      m s δ₀ Mp Dp σ p H st hp' (fun w => (hH w).1) hs R hR hRn ε' hε' hε'' hcan

end
end Submission.Obl.k4_finite_positive_prepared_models
