-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.NonconcRemoveSeparation.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.BoundedNonconcCore
import Submission.WZ.Obl.wz_separated_projection_dichotomy.PowerCoarseModel
import Submission.WZ.Obl.wz_separated_projection_dichotomy.CoarseProjection

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

/-- The separated, bounded counting statement implies its bounded version
without any separation hypothesis. Its Frostman parameter is chosen before
the line exponent, as required by the anisotropic application. -/
theorem bounded_nonconcentrated_remove_separation
    (hnc : BoundedNonconcentratedPrinciple true) : BoundedNonconcentratedPrinciple false := by
  intro ε hε hε1
  obtain ⟨ℓ, hℓ, hncℓ⟩ := hnc (ε / 2) (by positivity) (by linarith)
  refine ⟨ℓ / 4, by positivity, ?_⟩
  intro ζ hζ hζ1
  obtain ⟨a₀, d₀, ha₀, hd₀, hncscale⟩ := hncℓ ζ hζ hζ1
  let α := min 1 (min (a₀ / 3) (min (ℓ / 100) (ℓ * ζ / 100)))
  have hα : 0 < α := by dsimp [α]; positivity
  have hα1 : α ≤ 1 := min_le_left _ _
  have hαa : α ≤ a₀ / 3 := (min_le_right _ _).trans (min_le_left _ _)
  have hαℓ : α ≤ ℓ / 100 := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hαζ : α ≤ ℓ * ζ / 100 := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  obtain ⟨dC, hdC, hdC1, hcoarse⟩ := exists_power_coarse_model hℓ hα hα1 hζ
    (by norm_num : (0 : ℝ) ≤ 4) hαℓ hαζ
  obtain ⟨dE, hdE, hdE1, hbudget⟩ := exists_monomial_bound (51 : ℝ)
    (a := ε - 1) (b := ε / 2 - 1) (by linarith)
  refine ⟨α, min d₀ (min dC dE), hα, by positivity, ?_⟩
  intro δ hδ hsmall F G U H hFn hGn hUn hFsep hGsep hUsep hF hG hU hGl hUl hsep hH hHne hden
  have hs₀ := hsmall.trans (min_le_left _ _)
  have hsC := (hsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hsE := (hsmall.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hδ1 := hsC.trans hdC1
  obtain ⟨model⟩ := hcoarse δ hδ hsC F G U H hFn hGn hUn
    (by simpa only [neg_div] using hF) (by simpa only [neg_div] using hG)
    (by simpa only [neg_div] using hU) (by simpa only [neg_div] using hGl)
    (by simpa only [neg_div] using hUl) hH hHne hden
  have hdense : δ ^ a₀ * (model.first.card : ℝ) * (model.second.card : ℝ) * (model.third.card : ℝ) ≤
      (model.edges.card : ℝ) := by
    apply le_trans _ model.density
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hcount := hncscale δ hδ hs₀ model.first model.second model.third model.edges
    (fun x hx => hFn x (model.first_subset hx))
    (fun x hx => hGn x (model.second_subset hx))
    (fun x hx => hUn x (model.third_subset hx))
    (fun _ x hx y hy hxy => (model.first_separated x hx y hy hxy).le)
    (fun _ x hx y hy hxy => (model.second_separated x hx y hy hxy).le)
    (fun _ x hx y hy hxy => (model.third_separated x hx y hy hxy).le)
    model.first_frostman model.second_frostman model.third_frostman model.second_line model.third_line
    (fun x hx y hy => hsep x (model.second_subset hx) y (model.third_subset hy))
    model.contained model.nonempty hdense
  have htransfer := model.transfer_dot_cover hδ (by norm_num : (0 : ℝ) ≤ 4)
    hFn hGn hUn hH hcount
  apply htransfer.weaken
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 3 * (4 * 4 + 1))).mpr
  have hh := hbudget δ hδ hsE
  nlinarith

end WangZahlLot.Obl.wz_separated_projection_dichotomy
