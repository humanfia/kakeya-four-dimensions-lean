-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.BoundedRescaled.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.RescaledNonconcentrated
import Submission.WZ.Obl.wz_separated_projection_dichotomy.CenteredNonconcCore
import Submission.WZ.Obl.wz_separated_projection_dichotomy.CenteredAnisotropic

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

theorem anisotropic_centered_nonconcentrated_count {F G U : Finset Plane} {H : Finset Triple}
    {δ C K ζ h q c ℓ α ε d : ℝ} {e : Plane}
    (hδ : 0 < δ) (hC : 0 ≤ C) (hK : 1 ≤ K) (hζ : 0 ≤ ζ)
    (hδh : δ ≤ h) (hh1 : h ≤ 1) (hδq : δ ≤ q) (hq : q ≤ 1 / 2) (he : ‖e‖ = 1)
    (hF : ClosedFiniteFrostman δ C F) (hG : ClosedFiniteFrostman δ C G)
    (hU : ClosedFiniteFrostman δ C U)
    (hFnorm : ∀ a ∈ F, ‖a‖ ≤ 4) (hGnorm : ∀ b ∈ G, ‖b‖ ≤ 4)
    (hUnorm : ∀ b ∈ U, ‖b‖ ≤ 4)
    (hFstrip : h < 1 → ∀ a ∈ F, |inner ℝ a e| ≤ h)
    (hGstrip : h < 1 → ∀ x ∈ G, |inner ℝ x (perp e) - c| ≤ h)
    (hUstrip : h < 1 → ∀ b ∈ U, |inner ℝ b (perp e) - c| ≤ h)
    (hGline : StripFrostman δ K ζ h G) (hUline : StripFrostman δ K ζ h U)
    (hsmall : 10 * C * q ≤ δ ^ ζ)
    (hfrbudget : 2 * C ≤ (δ / h) ^ (-ℓ))
    (hlinebudget : K / q ^ ζ ≤ ((δ / h) ^ (-ℓ)) ^ ζ)
    (hdensitybudget : (δ / h) ^ α ≤ d)
    (hsep : ∀ b ∈ G, ∀ x ∈ U, 1 / 2 ≤ ‖b - x‖)
    (hH : H ⊆ F ×ˢ (G ×ˢ U)) (hHne : H.Nonempty)
    (hdensity : d * (F.card : ℝ) * (G.card : ℝ) * (U.card : ℝ) ≤ (H.card : ℝ))
    (hnc : CenteredNonconcentratedAt (δ / h) ℓ ζ α ε) :
    CoverLower δ (DotSet (↑H : Set Triple)) ((δ / h) ^ (ε - 1)) := by
  classical
  have hh : 0 < h := hδ.trans_le hδh
  have hτ : 0 < δ / h := div_pos hδ hh
  have hinv : 1 ≤ h⁻¹ := (one_le_inv₀ hh).mpr hh1
  have hδτ : δ ≤ δ / h := (le_div_iff₀ hh).mpr (by nlinarith)
  let φ := anisotropicMap e h⁻¹ 1
  let ψ := anisotropicMap e 1 h⁻¹
  have hφ : Function.Injective φ := anisotropicMap_injective he hinv le_rfl
  have hψ : Function.Injective ψ := anisotropicMap_injective he le_rfl hinv
  have hF' : ClosedFiniteFrostman (δ / h) ((δ / h) ^ (-ℓ)) (F.image φ) :=
    ((hF.anisotropic hδ.le hC he hinv le_rfl).mono_scale hδτ).mono_constant hτ.le hfrbudget
  have hG' : ClosedFiniteFrostman (δ / h) ((δ / h) ^ (-ℓ)) (G.image ψ) :=
    ((hG.anisotropic hδ.le hC he le_rfl hinv).mono_scale hδτ).mono_constant hτ.le hfrbudget
  have hU' : ClosedFiniteFrostman (δ / h) ((δ / h) ^ (-ℓ)) (U.image ψ) :=
    ((hU.anisotropic hδ.le hC he le_rfl hinv).mono_scale hδτ).mono_constant hτ.le hfrbudget
  have hGl := capped_anisotropic_line_count hδ hC hK hζ hδh hh1 hδq hq he hG.indexed
    (fun hlt x => hGstrip hlt x x.property) hsmall hGline.indexed
  have hUl := capped_anisotropic_line_count hδ hC hK hζ hδh hh1 hδq hq he hU.indexed
    (fun hlt x => hUstrip hlt x x.property) hsmall hUline.indexed
  have hGl' : IndexedLineFrostman (δ / h) ((δ / h) ^ (-ℓ)) ζ (fun x : G.image ψ => (x : Plane)) :=
    indexedLineFrostman_image hψ (indexedLineFrostman_of_scaled_count hτ (by positivity)
      (hδ.trans_le hδq) hlinebudget hGl)
  have hUl' : IndexedLineFrostman (δ / h) ((δ / h) ^ (-ℓ)) ζ (fun x : U.image ψ => (x : Plane)) :=
    indexedLineFrostman_image hψ (indexedLineFrostman_of_scaled_count hτ (by positivity)
      (hδ.trans_le hδq) hlinebudget hUl)
  have hsep' : ∀ b ∈ G.image ψ, ∀ x ∈ U.image ψ, 1 / 2 ≤ ‖b - x‖ := by
    intro b hb x hx
    obtain ⟨b₀, hb₀, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hx
    exact (hsep b₀ hb₀ x₀ hx₀).trans (by
      simpa only [ψ, ← anisotropicMap_sub] using anisotropicMap_norm_lower he le_rfl hinv (b₀ - x₀))
  have hd' : (δ / h) ^ α * ((F.image φ).card : ℝ) * ((G.image ψ).card : ℝ) *
      ((U.image ψ).card : ℝ) ≤ ((H.image (mapTriple φ ψ)).card : ℝ) := by
    rw [Finset.card_image_of_injective _ hφ, Finset.card_image_of_injective _ hψ,
      Finset.card_image_of_injective _ hψ, Finset.card_image_of_injective _ (mapTriple_injective hφ hψ)]
    apply le_trans _ hdensity
    gcongr
  have hcov := hnc (F.image φ) (G.image ψ) (U.image ψ) (H.image (mapTriple φ ψ))
    (cappedAnisotropicCenter e h c)
    (by
      intro a ha
      obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_image.mp ha
      exact capped_anisotropic_first_norm he hh hh1 (hFnorm a₀ ha₀) (fun hlt => hFstrip hlt a₀ ha₀))
    (by
      intro b hb
      obtain ⟨b₀, hb₀, rfl⟩ := Finset.mem_image.mp hb
      exact capped_anisotropic_centered_norm he hh hh1 (hGnorm b₀ hb₀) (fun hlt => hGstrip hlt b₀ hb₀))
    (by
      intro b hb
      obtain ⟨b₀, hb₀, rfl⟩ := Finset.mem_image.mp hb
      exact capped_anisotropic_centered_norm he hh hh1 (hUnorm b₀ hb₀) (fun hlt => hUstrip hlt b₀ hb₀))
    hF' hG' hU' hGl' hUl' hsep' (mapTriple_contained hH φ ψ) (hHne.image _) hd'
  exact hcov.of_anisotropic_triples he hh

end WangZahlLot.Obl.wz_separated_projection_dichotomy
