-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.SeparatedFromNonconc.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.RescaledNonconcentrated
import Submission.WZ.Obl.wz_separated_projection_dichotomy.LocalizedRegularity
import Submission.WZ.Obl.wz_separated_projection_dichotomy.TwoStripAlignment
import Submission.WZ.Obl.wz_separated_projection_dichotomy.StripSlices
import Submission.WZ.Obl.wz_separated_projection_dichotomy.StandardGeometry
import Submission.WZ.Obl.wz_separated_projection_dichotomy.FiniteReduction

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

theorem StandardTripleGeometry.cross_norm_bounds {F G U : Finset Plane}
    (h : StandardTripleGeometry F G U) :
    ∀ x ∈ G, ∀ b ∈ U, 1 / 2 ≤ ‖x - b‖ ∧ ‖x - b‖ ≤ 3 := by
  have hlow := h.separated_small_sets.2.2.2
  obtain ⟨a, c, ha, hc, hF, hG, hU⟩ := h
  intro x hx b hb
  refine ⟨by simpa only [dist_eq_norm] using hlow x hx b hb, ?_⟩
  have hxn : ‖x‖ ≤ 1 / 100 := by simpa only [dist_zero_right] using hG x hx
  have hbn : ‖b‖ ≤ 2 + 1 / 100 := by
    have ht := dist_triangle b c 0
    rw [dist_zero_right, dist_zero_right, hc] at ht
    linarith [hU b hb]
  exact (norm_sub_le _ _).trans (by linarith)

/-- The separated projection dichotomy follows from the nonconcentrated
projection principle. All localization, alignment and scale losses are
proved here, with the nonconcentrated input kept as an explicit premise. -/
theorem separated_dichotomy_of_nonconcentrated (hnc : NonconcentratedPrinciple)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ θ δ₀ : ℝ, 0 < θ ∧ 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → SeparatedDichotomyAt δ θ ε := by
  classical
  obtain ⟨ℓ, hℓ, hncℓ⟩ := hnc (ε / 2) (by positivity) (by linarith)
  let β := min (ε / 1000) (ε * ℓ / 1000)
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβε : β ≤ ε / 1000 := min_le_left _ _
  have hβℓ : β ≤ ε * ℓ / 1000 := min_le_right _ _
  have hβ1 : β ≤ 1 := by linarith
  obtain ⟨η, dA, hη, hdA, halign⟩ := two_strip_alignment hβ hβ1
  let ζ := min β η / 100
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  have hζβ : ζ ≤ β / 100 := by dsimp [ζ]; gcongr; exact min_le_left _ _
  have hζ1 : ζ ≤ 1 := by linarith
  obtain ⟨α, dNC, hα, hdNC, hncscale⟩ := hncℓ ζ hζ hζ1
  let t := ε / 10
  let θ := min ζ (min (t * α) (t * ℓ * ζ)) / 100
  have hp : ProjectionParameterBounds ε ℓ α β η ζ θ t :=
    projection_parameter_bounds hε hε1 hℓ hα hη hβ hβε hβℓ
  obtain ⟨dB, hdB, hbudget⟩ := exists_projection_scale_budget hp hdNC
  refine ⟨θ, min dA dB, hp.theta_pos, by positivity, ?_⟩
  intro δ hδ hsmall F G U hFn hGn hUn hFsep hGsep hUsep hF hG hU hgeom H hHne hH hden
  have hb := hbudget δ hδ (hsmall.trans (min_le_right _ _))
  have hδ1 := hb.scale_le_one
  have hdpos : 0 < δ ^ θ := by positivity
  have hd1 : δ ^ θ ≤ 1 := Real.rpow_le_one hδ.le hδ1 hp.theta_pos.le
  have hsm := hgeom.separated_small_sets
  obtain ⟨R⟩ := exists_localized_triple hdpos hd1 hδ hδ1 hζ.le hHne hH hden
    (fun x hx y hy => (hsm.2.1 x hx y hy).trans (by norm_num))
    (fun x hx y hy => (hsm.2.2.1 x hx y hy).trans (by norm_num))
  obtain ⟨hRF, hRG, hRU⟩ := R.frostman hδ hF hG hU
  have hCF : projectionFrostman δ θ ζ ≤ δ ^ (-η) := hb.alignment_frostman
  have huni : TripleUniform (δ ^ η) R.first R.second R.third R.edges :=
    R.uniform.mono_density (by linarith [hb.alignment_uniform])
  have hsep : ∀ x ∈ R.second, ∀ b ∈ R.third, 1 / 2 ≤ ‖x - b‖ ∧ ‖x - b‖ ≤ 3 :=
    fun x hx b hb' => hgeom.cross_norm_bounds x (R.second_subset hx) b (R.third_subset hb')
  have hnormF : ∀ a ∈ R.first, ‖a‖ ≤ 4 := fun a ha => hFn a (R.first_subset ha)
  have hnormG : ∀ x ∈ R.second, ‖x‖ ≤ 4 := fun x hx => hGn x (R.second_subset hx)
  have hnormU : ∀ b ∈ R.third, ‖b‖ ≤ 4 := fun b hb' => hUn b (R.third_subset hb')
  have hal := halign δ hδ (hsmall.trans (min_le_left _ _)) hδ1
    R.first R.second R.third R.edges R.nonempty R.contained hnormF hnormG hnormU
    (hRF.mono_constant hδ.le hCF) (hRG.mono_constant hδ.le hCF) (hRU.mono_constant hδ.le hCF)
    (fun x hx b hb' => by simpa only [norm_sub_rev] using (hsep x hx b hb').1)
    huni R.first_support R.second_support R.third_support R.normal_second R.normal_third
    R.center_second R.center_third R.width_second R.width_third R.unit_second R.unit_third
    R.width_second_lower R.width_third_lower (fun x hx => (R.strip_second x hx).le)
    (fun b hb' => (R.strip_third b hb').le)
  rcases hal with ⟨e, c, he, hFs, hGs, hUs⟩ | hgain
  swap
  · right
    exact ((hgain.mono_epsilon hδ hδ1 hη.le hp.beta_le_epsilon).mono_eta hδ hδ1 hp.theta_le_eta).mono_set R.edges_subset
  let w := min R.width_second R.width_third
  let W := δ ^ (-β) * w
  have hδw : δ ≤ w := le_min R.width_second_lower R.width_third_lower
  have hw : 0 < w := hδ.trans_le hδw
  have hW : 0 < W := by dsimp [W]; positivity
  have hδW : δ ≤ W := by
    have hpow : 1 ≤ δ ^ (-β) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
    dsimp [W]
    nlinarith
  have hFnz := R.nonempty_factors.1
  have hGnz := R.nonempty_factors.2.1
  by_cases hnarrow : W ≤ δ ^ (1 - t)
  · left
    have hcardF := hb.narrow_cardinal hδ hW hnarrow (hRF.nonempty_count hδ.le hFnz)
    have hcardG := hb.narrow_cardinal hδ hW hnarrow (hRG.nonempty_count hδ.le hGnz)
    have hline := line_conclusion_of_strip_cardinals hFnz hGnz hδ hδW he
      (fun x hx y hy hxy => hFsep x (R.first_subset hx) y (R.first_subset hy) hxy)
      (fun x hx y hy hxy => hGsep x (R.second_subset hx) y (R.second_subset hy) hxy)
      hFs hGs hcardF hcardG
    exact hline.mono_set R.first_subset R.second_subset
  right
  let h := min 1 W
  obtain ⟨hδh, hτbound, hhW⟩ := capped_width_bounds hδ hδ1 hβ.le hp.t_le_one hδw (lt_of_not_ge hnarrow)
  have hh : 0 < h := hδ.trans_le hδh
  have hh1 : h ≤ 1 := min_le_left _ _
  have hτ : 0 < δ / h := div_pos hδ hh
  obtain ⟨hfrB, hlineB, hdenB, hsmallB, hδq, hq, hlenB, hpowerB⟩ := hb.rescaled hp hδ hτ hτbound
  have hK : 1 ≤ projectionLine δ θ ζ β := projectionLine_ge_one hδ hδ1 hp.theta_pos.le hζ.le hβ.le
  have hC : 0 ≤ projectionFrostman δ θ ζ := by unfold projectionFrostman; positivity
  have hwidth : h ≤ δ ^ (-β) * w := min_le_right _ _
  have hGl := localized_line_rescaling hδ hζ.le hw hh hwidth
    (R.line_second.smaller_width hδ.le (by positivity) hζ.le hw (min_le_left _ _))
  have hUl := localized_line_rescaling hδ hζ.le hw hh hwidth
    (R.line_third.smaller_width hδ.le (by positivity) hζ.le hw (min_le_right _ _))
  have hFstrip : h < 1 → ∀ a ∈ R.first, |inner ℝ a e| ≤ h := by
    intro hlt a ha
    rw [show h = W from hhW hlt]
    exact hFs a ha
  have hGstrip : h < 1 → ∀ x ∈ R.second, |inner ℝ x (perp e) - c| ≤ h := by
    intro hlt x hx
    rw [show h = W from hhW hlt]
    exact hGs x hx
  have hUstrip : h < 1 → ∀ b ∈ R.third, |inner ℝ b (perp e) - c| ≤ h := by
    intro hlt b hb'
    rw [show h = W from hhW hlt]
    exact hUs b hb'
  have hnc' := hncscale (δ / h) hτ (hτbound.trans hb.input_scale)
  have hcount := anisotropic_nonconcentrated_count hδ hC hK hζ.le hδh hh1 hδq hq he hRF hRG hRU
    hGstrip hUstrip hGl hUl hsmallB hfrB hlineB hdenB hsep R.contained R.nonempty
    (R.uniform.density R.contained R.second_support) hnc'
  have hlength : δ ^ (-θ) * δ ≤ 2 * (25 * h) := by
    have hh' := mul_le_mul_of_nonneg_right hlenB hh.le
    have hid : (δ ^ (-θ) * (δ / h)) * h = δ ^ (-θ) * δ := by field_simp
    rw [hid] at hh'
    linarith
  have hpower : ((2 * (25 * h)) / δ) ^ (1 - ε) ≤ (δ / h) ^ (ε / 2 - 1) := by
    have hid : 2 * (25 * h) / δ = 50 / (δ / h) := by field_simp <;> ring
    rw [hid]
    exact hpowerB
  have hgain := projectionGain_of_bounded_subset le_rfl hlength hcount hpower (Set.Subset.rfl)
    (anisotropic_dot_bound he hh hh1 R.contained hnormF (fun x hx b hb' => (hsep x hx b hb').2)
      hFstrip hGstrip hUstrip)
  exact hgain.mono_set R.edges_subset

end WangZahlLot.Obl.wz_separated_projection_dichotomy
