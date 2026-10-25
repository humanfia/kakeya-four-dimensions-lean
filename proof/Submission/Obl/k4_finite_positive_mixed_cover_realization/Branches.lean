import Submission.Obl.k4_finite_positive_mixed_cover_realization.Cover

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

open MeasureTheory Submission.Lib.K4XInterface

/-- Each candidate type is realized uniformly over smaller positive geometric
losses. The final gain fraction is chosen before the common menu ratio. -/
def BranchStatement (time : Bool) : Prop :=
  Matching → ∀ d₁ κ₁ ℓ S η : ℝ,
    0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 → 0 < ℓ → 0 < S → S ≤ 1 → 0 < η →
  ∃ αmax : ℝ, 0 < αmax ∧ ∀ α : ℝ, 0 < α → α ≤ αmax →
  ∃ ρmax : ℝ, 0 < ρmax ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρmax → ρ ≤ 1 / 4 → d₁ + 8 * ρ < 1 →
  ∀ (m : ℕ) (s : ℕ → ℝ) (gain δ₀ : ℝ), FineGrid m s gain ρ →
    0 < gain → gain ≤ 1 / 8 → 0 < δ₀ → δ₀ ≤ ρ * gain →
  ∀ N K L d W ω ν E P B f g G, prob N K L d S η W ω ν E P B f g G →
    (∀ q : ℝ, 0 ≤ q → q ≤ L → |f q - f 0 - d₁ * q| ≤ δ₀ * L) →
  ∀ Mp Dp Mg Dg : ℕ, ∃ Mi Di : ℕ, ∀ τ : ℝ, 0 < τ →
  ∃ ε₀ σ₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ 0 < σ₀ ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
  ∀ ε σ : ℝ, 0 < ε → ε ≤ ε₀ → 0 < σ → σ ≤ σ₀ →
  ∀ p : PathData (W k),
    p.Valid ℓ (N k) L (ω k) (ν k) (E k) (B k) f κ₁ m s δ₀ Mp Dp σ →
  ∀ c : CoverData p, c.Valid (N k) L (ω k) (ν k) (B k) d₁ ρ gain m Mg Dg ε →
    c.time = time →
    Output (N k) L (W k) (ω k) (ν k) (E k) (B k) κ₁ (α * gain)
      m p.r p.T p.nw Mi Di τ

/-- Enlarging format budgets preserves an original-terminal-known output. -/
lemma output_format_mono {Nk L κ₁ Δ τ : ℝ} {W m M D M' D' : ℕ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory} {E : Fin W → Set Incidence}
    {B : Fin W → ℝ} {r nw : ℕ → ℝ} {T : ℕ → ℕ}
    (hNk : 1 ≤ Nk) (hB : ∀ w, 0 ≤ B w) (hM : M ≤ M') (hD : D ≤ D')
    (hout : Output Nk L W ω ν E B κ₁ Δ m r T nw M D τ) :
    Output Nk L W ω ν E B κ₁ Δ m r T nw M' D' τ := by
  obtain ⟨r₂, T₂, C₂, γ, j, c, u, Q, R, A, F, lst,
    hdepth, himp, hcount, hdisj, hlist, hchart, hmass⟩ := hout
  refine ⟨r₂, T₂, C₂, γ, j, c, u, Q, R, A, F, lst,
    hdepth, himp, hcount.trans (pow_le_pow_right₀ hNk hM), hdisj, hlist, ?_, hmass⟩
  intro b
  exact gchart_mono (hchart b) hNk hM hD
    (Real.rpow_pos_of_pos (zero_lt_one.trans_le hNk) τ) le_rfl (hB (γ b)) id

/-- The two uniform branch theorems give the exact frozen mixed realization.
All output budgets precede the requested slack, and both types use the same
final gain, menu ratio, original law and path. -/
theorem realization_of_branches (hTime : BranchStatement true)
    (hStrip : BranchStatement false) : RealizationStatement := by
  intro hMatch d₁ κ₁ ℓ S η hd₁ hd₁1 hκ₁ hκ₁1 hℓ hS hS1 hη
  obtain ⟨alphaT, hat, hTime⟩ := hTime hMatch d₁ κ₁ ℓ S η hd₁ hd₁1 hκ₁ hκ₁1 hℓ hS hS1 hη
  obtain ⟨alphaS, has, hStrip⟩ := hStrip hMatch d₁ κ₁ ℓ S η hd₁ hd₁1 hκ₁ hκ₁1 hℓ hS hS1 hη
  let α := min (1 / 4) (min alphaT alphaS)
  have hα : 0 < α := lt_min (by norm_num) (lt_min hat has)
  have hα4 : α ≤ 1 / 4 := min_le_left _ _
  have hαt : α ≤ alphaT := (min_le_right _ _).trans (min_le_left _ _)
  have hαs : α ≤ alphaS := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨rt, hrt, hTime⟩ := hTime α hα hαt
  obtain ⟨rs, hrs, hStrip⟩ := hStrip α hα hαs
  let ρ := min (1 / 4) (min rt (min rs ((1 - d₁) / 16)))
  have hρ : 0 < ρ := lt_min (by norm_num) (lt_min hrt (lt_min hrs (by linarith)))
  have hρ4 : ρ ≤ 1 / 4 := min_le_left _ _
  have hρt : ρ ≤ rt := (min_le_right _ _).trans (min_le_left _ _)
  have hρs : ρ ≤ rs := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hρd : ρ ≤ (1 - d₁) / 16 :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hdρ : d₁ + 8 * ρ < 1 := by linarith
  refine ⟨α, ρ, hα, hα4, hρ, hρ4, hdρ, ?_⟩
  intro m s gain δ₀ hs hgain hgain1 hδ₀ hδρ N K L d W ω ν E P B f g G hprob hlin Mp Dp Mg Dg
  obtain ⟨Mt, Dt, hTime⟩ := hTime ρ hρ hρt hρ4 hdρ m s gain δ₀ hs hgain hgain1 hδ₀ hδρ
    N K L d W ω ν E P B f g G hprob hlin Mp Dp Mg Dg
  obtain ⟨Ms, Ds, hStrip⟩ := hStrip ρ hρ hρs hρ4 hdρ m s gain δ₀ hs hgain hgain1 hδ₀ hδρ
    N K L d W ω ν E P B f g G hprob hlin Mp Dp Mg Dg
  refine ⟨max Mt Ms, max Dt Ds, ?_⟩
  intro τ hτ
  obtain ⟨et, st, het, het1, hst, kt, hTime⟩ := hTime τ hτ
  obtain ⟨es, ss, hes, hes1, hss, ks, hStrip⟩ := hStrip τ hτ
  let ε := min et es
  let σ := min st ss
  have hε : 0 < ε := lt_min het hes
  have hεt : ε ≤ et := min_le_left _ _
  have hεs : ε ≤ es := min_le_right _ _
  have hσ : 0 < σ := lt_min hst hss
  have hσt : σ ≤ st := min_le_left _ _
  have hσs : σ ≤ ss := min_le_right _ _
  refine ⟨ε, σ, hε, hεt.trans het1, hσ, max kt ks, ?_⟩
  intro k hk r T nw κ C lev par γ j c u Q R A F lst hp hcover
  let p : PathData (W k) := ⟨r, T, nw, κ, C, lev, par, γ, j, c, u, Q, R, A, F, lst⟩
  have hp' : p.Valid ℓ (N k) L (ω k) (ν k) (E k) (B k) f κ₁ m s δ₀ Mp Dp σ := hp
  obtain ⟨v, hv⟩ := (mixedCover_iff_data p (N k) L (ω k) (ν k) (B k)
    d₁ ρ gain m Mg Dg ε).mp hcover
  have hN : 1 ≤ N k := by linarith [hprob.1 k]
  have hB : ∀ w, 0 ≤ B k w := by
    obtain ⟨Mpr, Dpr, hdata⟩ := hprob.2.2.2.2.2.2.2.2.1
    intro w
    exact ((hdata k).2.2.2.1 w).2.1.le
  cases htime : v.time
  · exact output_format_mono hN hB (le_max_right _ _) (le_max_right _ _)
      (hStrip k ((le_max_right _ _).trans hk) ε σ hε hεs hσ hσs p hp' v hv htime)
  · exact output_format_mono hN hB (le_max_left _ _) (le_max_left _ _)
      (hTime k ((le_max_left _ _).trans hk) ε σ hε hεt hσ hσt p hp' v hv htime)

end Submission.Obl.k4_finite_positive_mixed_cover_realization
