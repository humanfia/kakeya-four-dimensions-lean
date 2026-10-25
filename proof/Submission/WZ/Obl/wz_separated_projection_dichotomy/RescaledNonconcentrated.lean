-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.RescaledNonconcentrated.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.RadialFrostman
import Submission.WZ.Obl.wz_separated_projection_dichotomy.NonconcentratedCore
import Submission.WZ.Obl.wz_separated_projection_dichotomy.FiniteLineMap
import Submission.WZ.Obl.wz_separated_projection_dichotomy.CappedAnisotropic
import Submission.WZ.Obl.wz_separated_projection_dichotomy.TripleMaps
import Submission.WZ.Obl.wz_separated_projection_dichotomy.ProjectionInterval

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

theorem anisotropic_nonconcentrated_count {F G U : Finset Plane} {H : Finset Triple}
    {δ C K ζ h q c ℓ α ε d : ℝ} {e : Plane}
    (hδ : 0 < δ) (hC : 0 ≤ C) (hK : 1 ≤ K) (hζ : 0 ≤ ζ)
    (hδh : δ ≤ h) (hh1 : h ≤ 1) (hδq : δ ≤ q) (hq : q ≤ 1 / 2) (he : ‖e‖ = 1)
    (hF : ClosedFiniteFrostman δ C F) (hG : ClosedFiniteFrostman δ C G)
    (hU : ClosedFiniteFrostman δ C U)
    (hGstrip : h < 1 → ∀ x ∈ G, |inner ℝ x (perp e) - c| ≤ h)
    (hUstrip : h < 1 → ∀ b ∈ U, |inner ℝ b (perp e) - c| ≤ h)
    (hGline : StripFrostman δ K ζ h G) (hUline : StripFrostman δ K ζ h U)
    (hsmall : 10 * C * q ≤ δ ^ ζ)
    (hfrbudget : 2 * C ≤ (δ / h) ^ (-ℓ))
    (hlinebudget : K / q ^ ζ ≤ ((δ / h) ^ (-ℓ)) ^ ζ)
    (hdensitybudget : (δ / h) ^ α ≤ d)
    (hsep : ∀ b ∈ G, ∀ x ∈ U, 1 / 2 ≤ ‖b - x‖ ∧ ‖b - x‖ ≤ 3)
    (hH : H ⊆ F ×ˢ (G ×ˢ U)) (hHne : H.Nonempty)
    (hdensity : d * (F.card : ℝ) * (G.card : ℝ) * (U.card : ℝ) ≤ (H.card : ℝ))
    (hnc : NonconcentratedAt (δ / h) ℓ ζ α ε) :
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
  have hsep' : ∀ b ∈ G.image ψ, ∀ x ∈ U.image ψ, 1 / 2 ≤ ‖b - x‖ ∧ ‖b - x‖ ≤ 8 := by
    intro b hb x hx
    obtain ⟨b₀, hb₀, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hx
    constructor
    · exact (hsep b₀ hb₀ x₀ hx₀).1.trans (by
        simpa only [ψ, ← anisotropicMap_sub] using anisotropicMap_norm_lower he le_rfl hinv (b₀ - x₀))
    · exact (capped_anisotropic_difference_norm he hh hh1 (hsep b₀ hb₀ x₀ hx₀).2
        (fun hlt => hGstrip hlt b₀ hb₀) (fun hlt => hUstrip hlt x₀ hx₀)).trans (by norm_num)
  have hd' : (δ / h) ^ α * ((F.image φ).card : ℝ) * ((G.image ψ).card : ℝ) *
      ((U.image ψ).card : ℝ) ≤ ((H.image (mapTriple φ ψ)).card : ℝ) := by
    rw [Finset.card_image_of_injective _ hφ, Finset.card_image_of_injective _ hψ,
      Finset.card_image_of_injective _ hψ, Finset.card_image_of_injective _ (mapTriple_injective hφ hψ)]
    apply le_trans _ hdensity
    gcongr
  have hcov := hnc (F.image φ) (G.image ψ) (U.image ψ) (H.image (mapTriple φ ψ))
    hF' hG' hU' hGl' hUl' hsep' (mapTriple_contained hH φ ψ) (hHne.image _) hd'
  exact hcov.of_anisotropic_triples he hh

theorem anisotropic_dot_bound {F G U : Finset Plane} {H : Finset Triple}
    {e : Plane} {h c : ℝ} (he : ‖e‖ = 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (hH : H ⊆ F ×ˢ (G ×ˢ U)) (hFnorm : ∀ a ∈ F, ‖a‖ ≤ 4)
    (hsep : ∀ x ∈ G, ∀ b ∈ U, ‖x - b‖ ≤ 3)
    (hFstrip : h < 1 → ∀ a ∈ F, |inner ℝ a e| ≤ h)
    (hGstrip : h < 1 → ∀ x ∈ G, |inner ℝ x (perp e) - c| ≤ h)
    (hUstrip : h < 1 → ∀ b ∈ U, |inner ℝ b (perp e) - c| ≤ h) :
    ∀ s ∈ DotSet (↑H : Set Triple), |s| ≤ 25 * h := by
  rintro s ⟨p, hp, rfl⟩
  have ha := (Finset.mem_product.mp (hH hp)).1
  have hx := (Finset.mem_product.mp (Finset.mem_product.mp (hH hp)).2).1
  have hb := (Finset.mem_product.mp (Finset.mem_product.mp (hH hp)).2).2
  rw [anisotropicMap_dual_dot he hh, abs_mul, abs_of_pos hh]
  have hA := capped_anisotropic_first_norm he hh hh1 (hFnorm p.1 ha) (fun hlt => hFstrip hlt p.1 ha)
  have hB := capped_anisotropic_difference_norm he hh hh1 (hsep p.2.1 hx p.2.2 hb)
    (fun hlt => hGstrip hlt p.2.1 hx) (fun hlt => hUstrip hlt p.2.2 hb)
  have hi := abs_real_inner_le_norm (anisotropicMap e h⁻¹ 1 p.1)
    (anisotropicMap e 1 h⁻¹ p.2.1 - anisotropicMap e 1 h⁻¹ p.2.2)
  have hprod : ‖anisotropicMap e h⁻¹ 1 p.1‖ *
      ‖anisotropicMap e 1 h⁻¹ p.2.1 - anisotropicMap e 1 h⁻¹ p.2.2‖ ≤ 25 := by
    nlinarith [norm_nonneg (anisotropicMap e h⁻¹ 1 p.1),
      norm_nonneg (anisotropicMap e 1 h⁻¹ p.2.1 - anisotropicMap e 1 h⁻¹ p.2.2)]
  nlinarith

end WangZahlLot.Obl.wz_separated_projection_dichotomy
