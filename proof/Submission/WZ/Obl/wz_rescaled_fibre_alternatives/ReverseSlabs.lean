-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_rescaled_fibre_alternatives.ReverseSlabs.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.CoarseBuffer
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.SlabComparison

namespace WangZahlLot.Obl.wz_rescaled_fibre_alternatives

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (axis)

noncomputable section

def localSlabLoss : ℝ := (448 * coverScale ^ 2 * contraction ^ 3) * (2 / buffer ^ 3)

lemma localSlabLoss_pos : 0 < localSlabLoss := by
  have := coverScale_pos
  have := buffer_pos
  unfold localSlabLoss
  positivity

lemma slabBound_affine_iff (f : Space ≃ᵃ[ℝ] Space) {J : ℝ} (hJ : 0 < J)
    (hvol : ∀ W : Set Space, volume (f '' W) = ENNReal.ofReal J * volume W)
    {D : Set Space} {L : ℝ} {n : ℕ} {P : Fin n → Prop} {U : Fin n → Set Space} :
    SlabBound (f '' D) L P (fun i => f '' U i) ↔ SlabBound D L P U := by
  constructor
  · intro h
    have hvol' (W : Set Space) : volume (f.symm '' W) = ENNReal.ofReal J⁻¹ * volume W := by
      have he : f.symm '' W = f ⁻¹' W := by
        ext p
        constructor
        · rintro ⟨q, hq, rfl⟩
          simpa only [mem_preimage, f.apply_symm_apply] using hq
        · intro hp
          exact ⟨f p, hp, f.symm_apply_apply p⟩
      rw [he]
      exact WangZahlLot.Obl.wz_nonflat_factored_improvement.affine_volume_preimage f hJ hvol W
    have hh := slabBound_affine_image f.symm J⁻¹ hvol' h
    have he (W : Set Space) : f.symm '' (f '' W) = W := by
      rw [← Set.image_comp]
      simp only [Function.comp_def, f.symm_apply_apply, Set.image_id']
    simpa only [he] using hh
  · exact slabBound_affine_image f J hvol

lemma physical_fibre_slab (e : Space ≃ₗᵢ[ℝ] Space) {y w x₀ v₀ z₀ u₀ : Space}
    (hew : e w = axis) {r s ρ L : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hs : 0 < s)
    (hρ : 0 < ρ) (hρk : ρ ≤ contraction ^ 2) (hR : normalizedRadius r s ≤ contraction ^ 2)
    (hcover : 2 * (coverScale * r * ρ) ≤ 1)
    (hv₀ : ‖v₀‖ = 1) (hw : ‖w‖ = 1) (hu₀ : ‖u₀‖ = 1)
    (hT₀ : tube s x₀ v₀ ⊆ tube r y w)
    (hf₀ : normalize e y w r hr '' tube s x₀ v₀ ⊆ tube ρ z₀ u₀)
    {n : ℕ} (P : Fin n → Prop) (x v z u : Fin n → Space)
    (hv : ∀ i, P i → ‖v i‖ = 1) (hu : ∀ i, P i → ‖u i‖ = 1)
    (hT : ∀ i, P i → tube s (x i) (v i) ⊆ tube r y w)
    (hf : ∀ i, P i → normalize e y w r hr '' tube s (x i) (v i) ⊆
      tube (normalizedRadius r s) (z i) (u i))
    (hc : ∀ i, P i → tube (normalizedRadius r s) (z i) (u i) ⊆ tube ρ z₀ u₀)
    (hmid : ∀ i, P i → ‖normalize e y w r hr (x i + (1 / 2 : ℝ) • v i) -
      normalize e y w r hr (x₀ + (1 / 2 : ℝ) • v₀)‖ ≤ 6 * ρ)
    (hSb : SlabBound (doubled ρ z₀ u₀) L P (fun i => tube (normalizedRadius r s) (z i) (u i))) :
    SlabBound (doubled (coverScale * r * ρ) x₀ v₀) (localSlabLoss * L) P
      (fun i => tube s (x i) (v i)) := by
  let f := normalize e y w r hr
  apply (slabBound_affine_iff f.toAffineEquiv (by positivity : 0 < jacobian r)
    (normalize_volume e y w hr)).mp
  have hmain := slabBound_of_comparable buffer_pos
    (by have := coverScale_pos; positivity : 0 ≤ 448 * coverScale ^ 2 * contraction ^ 3)
    dilation_ge_one buffer_dilation
    (fun i => f (x i + (1 / 2 : ℝ) • v i))
    (U := fun i => f '' tube s (x i) (v i))
    (V := fun i => tube (normalizedRadius r s) (z i) (u i))
    (D := f '' doubled (coverScale * r * ρ) x₀ v₀) (E := doubled ρ z₀ u₀)
    (fun i hi => ⟨_, self_subset_thickening hs _ (by simpa using centered_segment (x i) (v i) (a := 0) (by norm_num)), rfl⟩)
    (fun i hi => (hc i hi).trans (tube_subset_doubled hρ.le z₀ u₀))
    (fun i hi => normalized_fine_expansion e hew hr hr1 hs hR (hv i hi) hw (hu i hi) (hT i hi) (hf i hi))
    (fun i hi => normalized_coarse_buffer e hew hr hr1 hs hρ hρk
      (by rw [abs_of_pos buffer_pos]) hv₀ hw hu₀ hT₀ hf₀ (hmid i hi))
    (fun i hi => normalized_coarse_buffer e hew hr hr1 hs hρ hρk
      (by rw [abs_neg, abs_of_pos buffer_pos]) hv₀ hw hu₀ hT₀ hf₀ (hmid i hi))
    (coarse_volume_comparison e y w x₀ v₀ z₀ u₀ hr hρ hcover hv₀ hu₀) hSb
  exact hmain

end
end WangZahlLot.Obl.wz_rescaled_fibre_alternatives
