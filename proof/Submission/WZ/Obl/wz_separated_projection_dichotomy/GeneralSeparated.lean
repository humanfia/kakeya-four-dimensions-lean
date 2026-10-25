-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.GeneralSeparated.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.SeparatedFromBounded
import Submission.WZ.Obl.wz_separated_projection_dichotomy.GeneralAnisotropicBound
import Submission.WZ.Obl.wz_separated_projection_dichotomy.GeneralProjectionPower
import Submission.WZ.Obl.wz_separated_projection_dichotomy.StripCountConclusion

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

/-- A finite separated projection dichotomy requiring only bounded factors,
bounded diameters of the two second factors, and their mutual separation. -/
def GeneralSeparatedDichotomyAt (δ θ ε : ℝ) : Prop :=
  ∀ F G U : Finset Plane,
    (∀ x ∈ F, ‖x‖ ≤ 4) → (∀ x ∈ G, ‖x‖ ≤ 4) → (∀ x ∈ U, ‖x‖ ≤ 4) →
    ClosedFiniteFrostman δ (δ ^ (-θ)) F →
    ClosedFiniteFrostman δ (δ ^ (-θ)) G →
    ClosedFiniteFrostman δ (δ ^ (-θ)) U →
    (∀ x ∈ G, ∀ y ∈ G, dist x y ≤ 1 / 2) →
    (∀ x ∈ U, ∀ y ∈ U, dist x y ≤ 1 / 2) →
    (∀ x ∈ G, ∀ y ∈ U, 1 / 2 ≤ ‖x - y‖) →
    ∀ H : Finset Triple, H.Nonempty → H ⊆ F ×ˢ (G ×ˢ U) →
      δ ^ θ * (F.card : ℝ) * (G.card : ℝ) * (U.card : ℝ) ≤ (H.card : ℝ) →
      StripCountConclusion δ ε (↑F : Set Plane) (↑G : Set Plane) ∨
        ProjectionGain δ θ ε (↑H : Set Triple)

/-- The separated projection dichotomy follows from the nonconcentrated
projection principle. All localization, alignment and scale losses are
proved here, with the nonconcentrated input kept as an explicit premise. -/
theorem general_separated_dichotomy_of_centered_nonconcentrated (hnc : CenteredNonconcentratedPrinciple)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ θ δ₀ : ℝ, 0 < θ ∧ 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → GeneralSeparatedDichotomyAt δ θ ε := by
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
  obtain ⟨dE, hdE, hdE1, hpowerBudget⟩ := exists_monomial_bound (100 : ℝ)
    (a := t * ε / 2) (b := 0) (by have := hp.t_pos; positivity)
  refine ⟨θ, min dA (min dB dE), hp.theta_pos, by positivity, ?_⟩
  intro δ hδ hsmall F G U hFn hGn hUn hF hG hU hGdiam hUdiam hcross H hHne hH hden
  have hsmallA := hsmall.trans (min_le_left _ _)
  have hsmallB := (hsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hsmallE := (hsmall.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hb := hbudget δ hδ hsmallB
  have hδ1 := hb.scale_le_one
  have hdpos : 0 < δ ^ θ := by positivity
  have hd1 : δ ^ θ ≤ 1 := Real.rpow_le_one hδ.le hδ1 hp.theta_pos.le
  obtain ⟨R⟩ := exists_localized_triple hdpos hd1 hδ hδ1 hζ.le hHne hH hden
    hGdiam hUdiam
  obtain ⟨hRF, hRG, hRU⟩ := R.frostman hδ hF hG hU
  have hCF : projectionFrostman δ θ ζ ≤ δ ^ (-η) := hb.alignment_frostman
  have huni : TripleUniform (δ ^ η) R.first R.second R.third R.edges :=
    R.uniform.mono_density (by linarith [hb.alignment_uniform])
  have hsep : ∀ x ∈ R.second, ∀ b ∈ R.third, 1 / 2 ≤ ‖x - b‖ :=
    fun x hx b hb' => hcross x (R.second_subset hx) b (R.third_subset hb')
  have hnormF : ∀ a ∈ R.first, ‖a‖ ≤ 4 := fun a ha => hFn a (R.first_subset ha)
  have hnormG : ∀ x ∈ R.second, ‖x‖ ≤ 4 := fun x hx => hGn x (R.second_subset hx)
  have hnormU : ∀ b ∈ R.third, ‖b‖ ≤ 4 := fun b hb' => hUn b (R.third_subset hb')
  have hal := halign δ hδ hsmallA hδ1
    R.first R.second R.third R.edges R.nonempty R.contained hnormF hnormG hnormU
    (hRF.mono_constant hδ.le hCF) (hRG.mono_constant hδ.le hCF) (hRU.mono_constant hδ.le hCF)
    (fun x hx b hb' => by simpa only [norm_sub_rev] using hsep x hx b hb')
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
    have hline := stripCountConclusion_of_containing_strips hFnz hGnz hδ hδW he
      hFs hGs hcardF hcardG
    exact hline.mono_set R.first_subset R.second_subset F.finite_toSet G.finite_toSet
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
  have hcount := anisotropic_centered_nonconcentrated_count hδ hC hK hζ.le hδh hh1 hδq hq he hRF hRG hRU
    hnormF hnormG hnormU hFstrip hGstrip hUstrip hGl hUl hsmallB hfrB hlineB hdenB hsep R.contained R.nonempty
    (R.uniform.density R.contained R.second_support) hnc'
  have hlength : δ ^ (-θ) * δ ≤ 2 * (50 * h) := by
    have hh' := mul_le_mul_of_nonneg_right hlenB hh.le
    have hid : (δ ^ (-θ) * (δ / h)) * h = δ ^ (-θ) * δ := by field_simp
    rw [hid] at hh'
    linarith
  have hpower : ((2 * (50 * h)) / δ) ^ (1 - ε) ≤ (δ / h) ^ (ε / 2 - 1) := by
    have hid : 2 * (50 * h) / δ = 100 / (δ / h) := by field_simp <;> ring
    rw [hid]
    apply projection_power_with_constant (by norm_num : (1 : ℝ) ≤ 100) hδ hτ hε hτbound
    simpa only [Real.rpow_zero] using hpowerBudget δ hδ hsmallE
  have hgain := projectionGain_of_bounded_subset le_rfl hlength hcount hpower (Set.Subset.rfl)
    (anisotropic_dot_bound_general he hh hh1 R.contained hnormF hnormG hnormU
      hFstrip hGstrip hUstrip)
  exact hgain.mono_set R.edges_subset

theorem general_separated_dichotomy_of_bounded_nonconcentrated
    (hnc : BoundedNonconcentratedPrinciple true)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ θ δ₀ : ℝ, 0 < θ ∧ 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → GeneralSeparatedDichotomyAt δ θ ε :=
  general_separated_dichotomy_of_centered_nonconcentrated
    (centered_nonconcentrated_of_bounded (bounded_nonconcentrated_remove_separation hnc)) hε hε1

end WangZahlLot.Obl.wz_separated_projection_dichotomy
