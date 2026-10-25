-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_rescaled_fibre_alternatives.ReverseConvex.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.ConvexEnlargement
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.CoarseGeometry

namespace WangZahlLot.Obl.wz_rescaled_fibre_alternatives

open MeasureTheory Set Metric
open scoped ENNReal

noncomputable section

def coarseConvexLoss : ℝ := convexExpansionLoss dilation * coverScale ^ 2 * contraction ^ 3

lemma coarseConvexLoss_pos : 0 < coarseConvexLoss := by
  have := convexExpansionLoss_pos (C := dilation) (by linarith [dilation_ge_one])
  have := coverScale_pos
  unfold coarseConvexLoss
  positivity

lemma reverse_convex_count (e : Space ≃ₗᵢ[ℝ] Space) (y w : Space)
    {r ρ L : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hL : 0 ≤ L)
    {n : ℕ} (x v z u : Fin n → Space)
    (hexpand : ∀ i, tube ρ (z i) (u i) ⊆
      AffineMap.homothety (normalize e y w r hr (x i + (1 / 2 : ℝ) • v i)) dilation ''
        (normalize e y w r hr '' tube (coverScale * r * ρ) (x i) (v i)))
    (hK : ConvexCount ρ L (fun _ => True) (fun i => tube ρ (z i) (u i))) :
    ConvexCount (coverScale * r * ρ) (coarseConvexLoss * L) (fun _ => True)
      (fun i => tube (coverScale * r * ρ) (x i) (v i)) := by
  let f := normalize e y w r hr
  let R := coverScale * r * ρ
  have hscale := coverScale_pos
  have hR : 0 < R := by dsimp [R]; positivity
  have hcounts : WangZahlLot.Obl.wz_tower_convex_count_composition.Counts R (coarseConvexLoss * L) n x v := by
    apply WangZahlLot.Obl.wz_tower_convex_count_composition.counts_of_bounded_open
    intro W hW hWo hWb
    let I : Set (Fin n) := {i | tube R (x i) (v i) ⊆ W}
    change ENNReal.ofReal ((I.ncard : ℝ) * R ^ 2) ≤ _
    rcases I.eq_empty_or_nonempty with hI | ⟨i₀, hi₀⟩
    · simp [hI]
    have hp (i : Fin n) : x i + (1 / 2 : ℝ) • v i ∈ tube R (x i) (v i) :=
      self_subset_thickening hR _ (by simpa using centered_segment (x i) (v i) (a := 0) (by norm_num))
    obtain ⟨V, hV, hWV, hvol⟩ := convex_enlargement (C := dilation) hW hWo hWb
      ⟨_, hi₀ (hp i₀)⟩ (by linarith [dilation_ge_one])
    have hsub (i : Fin n) (hi : i ∈ I) : tube ρ (z i) (u i) ⊆ f '' V := by
      intro q hq
      obtain ⟨p, ⟨p', hp', rfl⟩, rfl⟩ := hexpand i hq
      refine ⟨AffineMap.homothety (x i + (1 / 2 : ℝ) • v i) dilation p',
        hWV _ (hi (hp i)) ⟨p', hi hp', rfl⟩, ?_⟩
      exact affine_homothety f _ _ _
    have hc : I.ncard ≤ {i | tube ρ (z i) (u i) ⊆ f '' V}.ncard := Set.ncard_mono hsub
    have hraw : ENNReal.ofReal ((I.ncard : ℝ) * ρ ^ 2) ≤
        ENNReal.ofReal L * volume (f '' V) := by
      have hh := hK (f '' V) (hV.affine_image f.toAffineEquiv.toAffineMap)
      simp only [true_and] at hh
      exact (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) (sq_nonneg ρ))).trans hh
    have hJ : 0 < jacobian r := by positivity
    have hfactor : (R / ρ) ^ 2 * jacobian r = coverScale ^ 2 * contraction ^ 3 := by
      dsimp [R, jacobian]
      field_simp
    calc
      _ = ENNReal.ofReal ((R / ρ) ^ 2) * ENNReal.ofReal ((I.ncard : ℝ) * ρ ^ 2) := by
        rw [← ENNReal.ofReal_mul (sq_nonneg _)]
        congr 1
        field_simp
      _ ≤ ENNReal.ofReal ((R / ρ) ^ 2) * (ENNReal.ofReal L * volume (f '' V)) :=
        mul_le_mul_right hraw _
      _ = ENNReal.ofReal (coverScale ^ 2 * contraction ^ 3 * L) * volume V := by
        rw [normalize_volume]
        calc
          _ = (ENNReal.ofReal ((R / ρ) ^ 2) * ENNReal.ofReal (jacobian r) * ENNReal.ofReal L) * volume V := by ac_rfl
          _ = _ := by rw [← ENNReal.ofReal_mul (sq_nonneg _), hfactor,
            ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (coverScale ^ 2 * contraction ^ 3 * L) *
          (ENNReal.ofReal (convexExpansionLoss dilation) * volume W) := mul_le_mul_right hvol _
      _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        unfold coarseConvexLoss
        ring
  intro W hW
  simpa only [true_and] using hcounts W hW

end
end WangZahlLot.Obl.wz_rescaled_fibre_alternatives
