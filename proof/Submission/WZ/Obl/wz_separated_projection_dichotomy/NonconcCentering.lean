-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.NonconcCentering.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.CenteredNonconcCore
import Submission.WZ.Obl.wz_separated_projection_dichotomy.CenteredAnisotropic
import Submission.WZ.Obl.wz_separated_projection_dichotomy.RadialFrostman
import Submission.WZ.Obl.wz_separated_projection_dichotomy.PowerBudget

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

attribute [local instance] Classical.propDecidable

theorem IndexedLineFrostman.mono_constant {I : Type*} [Fintype I] {f : I → Plane}
    {δ C D ζ : ℝ} (h : IndexedLineFrostman δ C ζ f)
    (hδ : 0 ≤ δ) (hC : 0 ≤ C) (hCD : C ≤ D) (hζ : 0 ≤ ζ) :
    IndexedLineFrostman δ D ζ f := by
  intro n a r hn hr
  apply (h n a r hn hr).trans
  have hr0 : 0 ≤ r := hδ.trans hr
  gcongr

theorem centered_nonconcentrated_of_bounded
    (hnc : BoundedNonconcentratedPrinciple false) : CenteredNonconcentratedPrinciple := by
  classical
  intro ε hε hε1
  obtain ⟨ℓ, hℓ, hncℓ⟩ := hnc ε hε hε1
  refine ⟨ℓ / 2, by positivity, ?_⟩
  intro ζ hζ hζ1
  obtain ⟨α, d₀, hα, hd₀, hncscale⟩ := hncℓ ζ hζ hζ1
  obtain ⟨dE, hdE, hdE1, hbudget⟩ := exists_monomial_bound (2 : ℝ)
    (a := -(ℓ / 2)) (b := -ℓ) (by linarith)
  refine ⟨α, min d₀ dE, hα, by positivity, ?_⟩
  intro δ hδ hsmall F G U H b hFn hGn hUn hF hG hU hGl hUl hsep hH hHne hden
  have hsmall₀ := hsmall.trans (min_le_left _ _)
  have hsmallE := hsmall.trans (min_le_right _ _)
  have hρ : 0 < δ / 2 := by positivity
  have hρδ : δ / 2 ≤ δ := by linarith
  have hb : δ ^ (-(ℓ / 2)) / (1 / 2) ≤ (δ / 2) ^ (-ℓ) := by
    calc δ ^ (-(ℓ / 2)) / (1 / 2) = 2 * δ ^ (-(ℓ / 2)) := by ring
      _ ≤ δ ^ (-ℓ) := hbudget δ hδ hsmallE
      _ ≤ (δ / 2) ^ (-ℓ) := Real.rpow_le_rpow_of_nonpos hρ hρδ (by linarith)
  let φ : Plane → Plane := zoom 0 (1 / 2)
  let ψ : Plane → Plane := zoom b (1 / 2)
  have hφ : Function.Injective φ := zoom_injective 0 (by norm_num)
  have hψ : Function.Injective ψ := zoom_injective b (by norm_num)
  have hbfr (S : Finset Plane) (c : Plane) (hf : ClosedFiniteFrostman δ (δ ^ (-(ℓ / 2))) S) :
      ClosedFiniteFrostman (δ / 2) ((δ / 2) ^ (-ℓ)) (S.image (zoom c (1 / 2))) := by
    have hh := hf.map_zoom c (by norm_num : (0 : ℝ) < 1 / 2)
    have hscale : (1 / 2 : ℝ) * δ = δ / 2 := by ring
    rw [hscale] at hh
    exact hh.mono_constant hρ.le hb
  have hbl (S : Finset Plane)
      (hf : IndexedLineFrostman δ (δ ^ (-(ℓ / 2))) ζ (fun x : S => (x : Plane))) :
      IndexedLineFrostman (δ / 2) ((δ / 2) ^ (-ℓ)) ζ (fun x : S.image ψ => (x : Plane)) := by
    have hh := hf.image_zoom b (by norm_num : (0 : ℝ) < 1 / 2)
    have hscale : (1 / 2 : ℝ) * δ = δ / 2 := by ring
    rw [hscale] at hh
    exact hh.mono_constant hρ.le (by positivity) hb hζ.le
  have hdense : (δ / 2) ^ α * ((F.image φ).card : ℝ) * ((G.image ψ).card : ℝ) *
      ((U.image ψ).card : ℝ) ≤ ((H.image (mapTriple φ ψ)).card : ℝ) := by
    rw [Finset.card_image_of_injective _ hφ, Finset.card_image_of_injective _ hψ,
      Finset.card_image_of_injective _ hψ, Finset.card_image_of_injective _ (mapTriple_injective hφ hψ)]
    apply le_trans _ hden
    gcongr
  have hcount := hncscale (δ / 2) hρ (hρδ.trans hsmall₀)
    (F.image φ) (G.image ψ) (U.image ψ) (H.image (mapTriple φ ψ))
    (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact half_zoom_norm (by simpa only [sub_zero] using hFn y hy))
    (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact half_zoom_norm (hGn y hy))
    (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact half_zoom_norm (hUn y hy))
    (by intro hf; cases hf) (by intro hf; cases hf) (by intro hf; cases hf)
    (hbfr F 0 hF) (hbfr G b hG) (hbfr U b hU) (hbl G hGl) (hbl U hUl)
    (by
      intro x hx y hy
      obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨y₀, hy₀, rfl⟩ := Finset.mem_image.mp hy
      exact half_zoom_separation (hsep x₀ hx₀ y₀ hy₀))
    (mapTriple_contained hH φ ψ) (hHne.image _) hdense
  have htransfer : CoverLower δ (DotSet (↑H : Set Triple)) ((δ / 2) ^ (ε - 1)) :=
    hcount.of_half_zoom_triples b hδ.le
  apply htransfer.weaken
  exact Real.rpow_le_rpow_of_nonpos hρ hρδ (by linarith)

end WangZahlLot.Obl.wz_separated_projection_dichotomy
