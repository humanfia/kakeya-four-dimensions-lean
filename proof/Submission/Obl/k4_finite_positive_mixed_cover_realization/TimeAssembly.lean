import Submission.Obl.k4_finite_positive_mixed_cover_realization.Branches
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeClean
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeConvert
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeNumerics
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeSupport
import Submission.Obl.k4_finite_positive_mixed_cover_realization.FiniteGainMenu
import Submission.Obl.k4_graph_atlas_representative_realization
import Submission.Obl.k4_original_observation_atlas_encoding

/-!
# The time branch from its analytic core

`timeBranch_of_core : TimeCore → BranchStatement true`.

Constants: `θ, ρ₀` from the core; `αMax = θ/8`; `ρMax = min ρ₀ (κ₁ θ / 80)`.
A time cover at the requested gain `gain` and ratio `ρ ≤ ρ₀` is o209's greedy cover at the
requested gain `h` (its actual gain, which lies in the finite geometric menu) and ratio `ρ₀`.
Per sample: o209's cleaning (adapted, `sampleCleanPos`) gives `CleanCover`; the core gives a
graph atlas at the old depth with gain `h`; o195 normalizes it at depth `≥ r + (θ/4) h L`
with list allowance `N ^ ζ`; o174 recovers exact original lists at `N ^ τ`; the fine grid
supplies the reference level of the time alternative (`time_reference_shift`).
All budgets are maxima over the finite menu, chosen before `τ`.
-/

set_option linter.unusedVariables false

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

open MeasureTheory Filter Set
open Submission.Obl.k4_fixed_menu_density_pruning (upperTail menuDepth gcBody rpow_neg_le_div)

theorem timeBranch_of_core (hcore : TimeCore) : BranchStatement true := by
  classical
  intro hMatch d₁ κ₁ ℓ S η hd₁ hd₁1 hκ₁ hκ₁1 hℓ hS hS1 hη
  obtain ⟨θ, ρ₀, hθ, hθ4, hρ₀, hρ₀4, hdρ₀, hcore⟩ := hcore hMatch ℓ d₁ κ₁ hd₁ hd₁1 hκ₁ hκ₁1
  refine ⟨θ / 8, by positivity, ?_⟩
  intro α hα hαθ
  refine ⟨min ρ₀ (κ₁ * θ / 80), lt_min hρ₀ (by positivity), ?_⟩
  intro ρ hρ hρmax hρ4 hdρ m s gain δ₀ hgrid hgain hgain1 hδ₀ hδρ
    N K L d W ω ν E P B f g G hprob hlin Mp Dp Mg Dg
  have hρρ₀ : ρ ≤ ρ₀ := hρmax.trans (min_le_left _ _)
  have hρθ : ρ ≤ κ₁ * θ / 80 := hρmax.trans (min_le_right _ _)
  have hL : 0 < L := hprob.2.2.2.1
  have hN2 : ∀ k, 2 ≤ N k := hprob.1
  have hNt : Tendsto N atTop atTop := hprob.2.1
  have hglaw := hprob.2.2.2.2.2.2.2.2.2.1
  obtain ⟨Mpr, Dpr, hsd⟩ := prob_scalarData hprob
  -- the finite menu of actual gains
  let menu : Finset ℝ :=
    (geometricGainMenu gain ρ (1 / 8)).filter (fun h => gain ≤ h ∧ h ≤ 1 / 8)
  have hmemh : ∀ h : menu, gain ≤ (h : ℝ) ∧ (h : ℝ) ≤ 1 / 8 :=
    fun h => (Finset.mem_filter.mp h.2).2
  have hpos : ∀ h : menu, 0 < (h : ℝ) := fun h => hgain.trans_le (hmemh h).1
  have hδh : ∀ h : menu, δ₀ ≤ ρ₀ * (h : ℝ) := fun h =>
    hδρ.trans (mul_le_mul hρρ₀ (hmemh h).1 hgain.le hρ₀.le)
  have hbasic := hgrid.1
  -- the core at every menu gain
  have hcoreM := fun h : menu =>
    hcore L m s h δ₀ hL hbasic (hpos h) (hmemh h).2 hδ₀ (hδh h) Mp Dp Mg Dg Mpr Dpr
  choose Mh Dh hMD using hcoreM
  let Mstar : ℕ := Finset.univ.sup Mh
  let Dstar : ℕ := Finset.univ.sup Dh
  have hMh : ∀ h, Mh h ≤ Mstar := fun h => Finset.le_sup (Finset.mem_univ h)
  have hDh : ∀ h, Dh h ≤ Dstar := fun h => Finset.le_sup (Finset.mem_univ h)
  obtain ⟨M', hMM', h195⟩ :=
    Submission.Obl.k4_graph_atlas_representative_realization.realization Mstar
  obtain ⟨Mi, Di, hM'Mi, hDDi, h174⟩ :=
    Submission.Obl.k4_original_observation_atlas_encoding.encoding L hL Mpr Dpr M' Dstar
  refine ⟨Mi, Di, ?_⟩
  intro τ hτ
  set ζ : ℝ := min (τ / 4) (1 / 8) with hζdef
  have hζ : 0 < ζ := lt_min (by positivity) (by norm_num)
  have hζτ : ζ ≤ τ / 4 := min_le_left _ _
  have hζ8 : ζ ≤ 1 / 8 := min_le_right _ _
  have hζ1 : ζ ≤ 1 := hζ8.trans (by norm_num)
  set β : ℝ := ζ / 4 with hβdef
  have hβ : 0 < β := by positivity
  have hβ1 : β ≤ 1 := by linarith
  -- the core, o195 and o174 at this allowance
  have hcoreβ := fun h : menu => hMD h β hβ hβ1
  choose τc ε₀h σ₀h hτc hε₀h hε₀h1 hσ₀h hσ₀h1 N₀h hN₀h2 hcoreS using hcoreβ
  have h195' := fun h : menu => h195 L θ h ζ hL hθ hθ4 (hpos h) (hmemh h).2 hζ hζ1
  choose N195 hN1952 h195S using h195'
  obtain ⟨N174, hN1742, h174S⟩ := h174 τ hτ
  -- the finite menu of fixed depths and tolerances for the density cleaning
  let q : menu × (Fin m ⊕ (Fin m ⊕ Unit)) → ℝ := fun e =>
    match e.2 with
    | Sum.inl i => menuDepth L (s i) (e.1 : ℝ) δ₀
    | Sum.inr (Sum.inl i) => menuDepth L (s i) 0 δ₀
    | Sum.inr (Sum.inr _) => L
  have hq : ∀ e, q e ∈ Icc 0 L := by
    intro e
    rcases e with ⟨h, i | i | u⟩
    · exact Submission.Obl.k4_fixed_menu_density_pruning.menuDepth_mem hL.le
    · exact Submission.Obl.k4_fixed_menu_density_pruning.menuDepth_mem hL.le
    · exact ⟨hL.le, le_rfl⟩
  obtain ⟨c₀, hc₀, htails⟩ := prob_menu_upper_tails hprob q (fun e => τc e.1) hq
    (fun e => hτc e.1)
  -- the input tolerances
  obtain ⟨cε, hcε, hcε1, hcεh⟩ := finite_pos_lower ε₀h hε₀h
  obtain ⟨cσ, hcσ, hcσ1, hcσh⟩ := finite_pos_lower σ₀h hσ₀h
  let ε₀ : ℝ := min cε (min β (c₀ / 2))
  have hε₀ : 0 < ε₀ := lt_min hcε (lt_min hβ (by linarith))
  have hε₀c : ε₀ ≤ cε := min_le_left _ _
  have hε₀β : ε₀ ≤ β := (min_le_right _ _).trans (min_le_left _ _)
  have hε₀c₀ : ε₀ ≤ c₀ / 2 := (min_le_right _ _).trans (min_le_right _ _)
  -- the sample cutoff
  obtain ⟨Nmax, hNmax174, hNmax⟩ := finite_upper
    (fun h : menu => max (N₀h h) (N195 h)) N174
  have hev : ∀ᶠ k in atTop, (48 : ℝ) ≤ N k ^ (c₀ / 2) ∧ Nmax ≤ N k ∧ ∀ e,
      upperTail (N k) (W k) (ω k) (ν k) (E k) (B k) f (g k) (τc e.1) (q e) ≤
        ENNReal.ofReal (N k ^ (-c₀)) := by
    have h48 : ∀ᶠ k in atTop, (48 : ℝ) ≤ N k ^ (c₀ / 2) :=
      ((tendsto_rpow_atTop (by positivity)).comp hNt).eventually_ge_atTop 48
    exact h48.and ((hNt.eventually_ge_atTop Nmax).and htails)
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp hev
  refine ⟨ε₀, cσ, hε₀, hε₀c.trans hcε1, hcσ, k₀, ?_⟩
  intro k hk ε σ hε hεε₀ hσ hσσ₀ p hp c hc htime
  obtain ⟨h48, hNk, htk⟩ := hk₀ k hk
  have hNk1 : 1 ≤ N k := by linarith [hN2 k]
  obtain ⟨hsdk, htemp, hEsub⟩ := hsd k
  -- the cover's actual gain is a menu entry
  have hlevel : c.level < m := hc.1
  have hgg : gain ≤ c.gain := hc.2.1
  have hg8 : c.gain ≤ 1 / 8 := hc.2.2.1
  have hmenuE : ∃ e : ℕ, c.gain = gain * (1 + ρ) ^ e := hc.2.2.2.1
  have hmem : c.gain ∈ menu := Finset.mem_filter.mpr
    ⟨mem_geometricGainMenu hgain hρ hmenuE hg8, hgg, hg8⟩
  let hm : menu := ⟨c.gain, hmem⟩
  have hBpos : ∀ w, 0 < B k w := fun w => (hsdk.2.2.2 w).2.1
  have hgc := gcBody_of_timeCover (ρ₀ := ρ₀) c hNk1 hL hgain hBpos hρ.le hρρ₀ hc htime
  -- the density tails at this sample's menu entries
  have hsmall : ENNReal.ofReal (N k ^ (-c₀)) ≤ ENNReal.ofReal (N k ^ (-ε) / 48) :=
    ENNReal.ofReal_le_ofReal (rpow_neg_le_div hNk1 (hεε₀.trans hε₀c₀) (by norm_num) h48)
  have hcand := htk (hm, Sum.inl ⟨c.level, hlevel⟩)
  have hold := htk (hm, Sum.inr (Sum.inl ⟨c.level, hlevel⟩))
  have hterm := htk (hm, Sum.inr (Sum.inr ()))
  -- the cleaned cover
  have hclean := sampleCleanPos ℓ (N k) L (W k) (ω k) (ν k) (E k) (B k) f (g k) d₁ κ₁ ρ₀
    c.gain δ₀ (τc hm) ε σ m s Mp Dp Mg Dg p.r p.T p.nw p.κ p.C p.lev p.par p.world p.bin
    p.center p.velocity p.frame p.test p.assigned p.counted p.lists c.level c.gain c.n c.old
    c.test c.assigned c.counted (hN2 k) hL hd₁ hd₁1 hρ₀ hρ₀4 (hpos hm) (hmemh hm).2 hδ₀
    (hδh hm) (hτc hm) hε hsdk.2.1 hsdk.2.2.1
    (fun w => ⟨(hsdk.2.2.2 w).1, (hsdk.2.2.2 w).2.1, (hsdk.2.2.2 w).2.2.2.2.1, hEsub w⟩)
    (fun w q hq0 hqL => hglaw k w q hq0 hqL) hp hgc
    (hcand.trans hsmall) (hold.trans hsmall) (hterm.trans hsmall)
  -- the analytic core: a graph atlas over the old level
  obtain ⟨i', h', T₂, C₂, γ₂, j₂, c₂, u₂, Q₂, P₂, sc, A₂, F₂, lst₂,
      hi', hgh', hh'8, hroom', htime₂, hatlas⟩ :=
    hcoreS hm (N k) (((le_max_left _ _).trans (hNmax hm)).trans hNk) (W k) (ω k) (ν k) (E k)
      (B k) f hsdk hlin ε σ hε (hεε₀.trans (hε₀c.trans (hcεh hm))) (hεε₀.trans hε₀β) hσ
      (hσσ₀.trans (hcσh hm)) p.r p.T p.nw p.κ p.C p.lev p.par p.world p.bin p.center
      p.velocity p.frame p.test p.assigned p.counted p.lists hp hclean
  have hatlas' := graphAtlas_mono hNk1 (hMh hm) (hDh hm) hatlas
  -- o195: normalized representative charts at depth at least `r i' + (θ/4) h L`
  obtain ⟨r₂, C₃, γ₃, j₃, c₃, u₃, Q₃, R₃, A₃, F₃, lst₃, hr₂, hr₂L, hC₃, hdisj₃, hlst₃,
      hmeas₃, hchart₃, hmass₃⟩ :=
    h195S hm (N k) (((le_max_right _ _).trans (hNmax hm)).trans hNk) (W k) (ω k) (ν k) (E k)
      (B k) (p.r i') h' β Dstar T₂ C₂ γ₂ j₂ c₂ u₂ Q₂ P₂ sc A₂ F₂ lst₂
      (hp.level_bounds i' hi').2.1.le hgh' hh'8 hroom' hβ le_rfl hatlas'
  -- o174: exact original-observation lists at the requested slack
  obtain ⟨F', lst', hF'sub, hlst', hchart', hmass'⟩ :=
    h174S (N k) (hNmax174.trans hNk) (W k) (ω k) (ν k) (B k) (E k) htemp ζ r₂ T₂ C₃ γ₃ j₃
      c₃ u₃ Q₃ R₃ A₃ F₃ lst₃ hζ hζτ hζ8 hC₃ hlst₃ hmeas₃ hchart₃ hmass₃
  -- the reference level of the time alternative
  have hlevAll : ∀ i, i < m → |p.r i - s i * L| ≤ δ₀ * L ∧
      N k ^ ((κ₁ * s i - δ₀) * L) ≤ (2 : ℝ) ^ p.T i ∧
      (2 : ℝ) ^ p.T i ≤ N k ^ ((κ₁ * s i + δ₀) * L) := fun i hi =>
    ⟨(hp.level_bounds i hi).1, (hp.level_bounds i hi).2.2.1, (hp.level_bounds i hi).2.2.2.1⟩
  obtain ⟨i'', hi'', hr'', ht''⟩ := time_reference_shift hgrid hL hNk1 hgain hκ₁ hκ₁1 hθ hθ4
    hα hαθ hρ hρθ hδ₀.le hδρ hlevAll hi' hgg hgh' hroom' hr₂ htime₂
  refine ⟨r₂, T₂, C₃, γ₃, j₃, c₃, u₃, Q₃, R₃, A₃, F', lst', ?_,
    Or.inr ⟨i'', hi'', Or.inl ⟨hr'', ht''⟩⟩, hC₃.trans (pow_le_pow_right₀ hNk1 hM'Mi),
    hdisj₃, hlst', hchart', hmass'⟩
  have hαg : α * gain ≤ (θ / 4) * c.gain := by
    have h1 : α * gain ≤ (θ / 8) * gain := mul_le_mul_of_nonneg_right hαθ hgain.le
    have h2 : (θ / 8) * gain ≤ (θ / 4) * c.gain := by
      have := mul_le_mul_of_nonneg_left hgg (show (0:ℝ) ≤ θ / 4 by positivity)
      nlinarith
    linarith
  have := mul_le_mul_of_nonneg_right hαg hL.le
  linarith

end Submission.Obl.k4_finite_positive_mixed_cover_realization
