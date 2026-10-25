-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.TripleLocalization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.SupportedRefinement
import Submission.WZ.Obl.wz_separated_projection_dichotomy.TripleRestriction
import Submission.WZ.Obl.wz_separated_projection_dichotomy.StripLocalization

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

/-- A supported, uniform triple refinement whose last two factors are
localized in strips and obey relative strip counting bounds. -/
structure LocalizedTriple (d δ ζ : ℝ) (F G U : Finset Plane) (H : Finset Triple) where
  first : Finset Plane
  second : Finset Plane
  third : Finset Plane
  edges : Finset Triple
  first_subset : first ⊆ F
  second_subset : second ⊆ G
  third_subset : third ⊆ U
  edges_subset : edges ⊆ H
  nonempty : edges.Nonempty
  contained : edges ⊆ first ×ˢ (second ×ˢ third)
  first_support : ∀ a ∈ first, ∃ x b, (a, x, b) ∈ edges
  second_support : ∀ x ∈ second, ∃ a b, (a, x, b) ∈ edges
  third_support : ∀ b ∈ third, ∃ a x, (a, x, b) ∈ edges
  first_retention : (d ^ 3 * δ ^ ζ / 27648) * (F.card : ℝ) ≤ (first.card : ℝ)
  second_retention : (d ^ 3 * δ ^ ζ / 27648) * (G.card : ℝ) ≤ (second.card : ℝ)
  third_retention : (d ^ 3 * δ ^ ζ / 27648) * (U.card : ℝ) ≤ (third.card : ℝ)
  uniform : TripleUniform (d / 1728) first second third edges
  normal_second : Plane
  normal_third : Plane
  center_second : ℝ
  center_third : ℝ
  width_second : ℝ
  width_third : ℝ
  unit_second : ‖normal_second‖ = 1
  unit_third : ‖normal_third‖ = 1
  width_second_lower : δ ≤ width_second
  width_third_lower : δ ≤ width_third
  width_second_upper : width_second ≤ 1
  width_third_upper : width_third ≤ 1
  strip_second : ∀ x ∈ second, |inner ℝ x normal_second - center_second| < width_second
  strip_third : ∀ b ∈ third, |inner ℝ b normal_third - center_third| < width_third
  line_second : StripFrostman δ (13824 / d ^ 2) ζ width_second second
  line_third : StripFrostman δ (13824 / d ^ 2) ζ width_third third

theorem exists_localized_triple {F G U : Finset Plane} {H : Finset Triple} {d δ ζ : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hζ : 0 ≤ ζ)
    (hHne : H.Nonempty) (hH : H ⊆ F ×ˢ (G ×ˢ U))
    (hdensity : d * (F.card : ℝ) * (G.card : ℝ) * (U.card : ℝ) ≤ (H.card : ℝ))
    (hGdiam : ∀ x ∈ G, ∀ y ∈ G, dist x y ≤ 1 / 2)
    (hUdiam : ∀ x ∈ U, ∀ y ∈ U, dist x y ≤ 1 / 2) :
    Nonempty (LocalizedTriple d δ ζ F G U H) := by
  classical
  obtain ⟨R₀⟩ := exists_supported_refinement hd hHne hH hdensity
  obtain ⟨n₁, c₁, w₁, G', hn₁, hw₁, hw₁1, hG', hG'ne, hG'strip, hG'ret, hG'line⟩ :=
    exists_small_diameter_strip_localization R₀.second_nonempty
      (fun x hx y hy => hGdiam x (R₀.second_subset hx) y (R₀.second_subset hy)) hδ hδ1 hζ
  have hH₁ne := restrictSecond_nonempty hG' hG'ne R₀.second_support
  have hH₁ := restrictSecond_contained R₀.contained G'
  have hH₁den := R₀.uniform.restrict_second_density hG' R₀.second_support
  obtain ⟨R₁⟩ := exists_supported_refinement (by positivity : 0 < d / 12) hH₁ne hH₁ hH₁den
  obtain ⟨n₂, c₂, w₂, U', hn₂, hw₂, hw₂1, hU', hU'ne, hU'strip, hU'ret, hU'line⟩ :=
    exists_small_diameter_strip_localization R₁.third_nonempty
      (fun x hx y hy => hUdiam x (R₀.third_subset (R₁.third_subset hx))
        y (R₀.third_subset (R₁.third_subset hy))) hδ hδ1 hζ
  have hH₂ne := restrictThird_nonempty hU' hU'ne R₁.third_support
  have hH₂ := restrictThird_contained R₁.contained U'
  have hH₂den := R₁.uniform.restrict_third_density hU' R₁.third_support
  obtain ⟨R₂⟩ := exists_supported_refinement (by positivity : 0 < d / 12 / 12) hH₂ne hH₂ hH₂den
  have hp0 : 0 < δ ^ ζ := by positivity
  have hp1 : δ ^ ζ ≤ 1 := Real.rpow_le_one hδ.le hδ1 hζ
  have hret₁ : δ ^ ζ / 2 * (R₀.second.card : ℝ) ≤ G'.card := by
    calc δ ^ ζ / 2 * (R₀.second.card : ℝ) ≤ w₁ ^ ζ * (R₀.second.card : ℝ) / 2 := by
          have hp := Real.rpow_le_rpow hδ.le hw₁ hζ
          nlinarith [Nat.cast_nonneg (α := ℝ) R₀.second.card]
      _ ≤ _ := hG'ret
  have hret₂ : δ ^ ζ / 2 * (R₁.third.card : ℝ) ≤ U'.card := by
    calc δ ^ ζ / 2 * (R₁.third.card : ℝ) ≤ w₂ ^ ζ * (R₁.third.card : ℝ) / 2 := by
          have hp := Real.rpow_le_rpow hδ.le hw₂ hζ
          nlinarith [Nat.cast_nonneg (α := ℝ) R₁.third.card]
      _ ≤ _ := hU'ret
  have hFret : d ^ 3 * δ ^ ζ / 27648 * (F.card : ℝ) ≤ R₂.first.card := by
    calc d ^ 3 * δ ^ ζ / 27648 * (F.card : ℝ) ≤
          (d / 12 / 12 / 2) * ((d / 12 / 2) * ((d / 2) * (F.card : ℝ))) := by
            have hnon : 0 ≤ d ^ 3 * (F.card : ℝ) := by positivity
            nlinarith
      _ ≤ (d / 12 / 12 / 2) * ((d / 12 / 2) * (R₀.first.card : ℝ)) := by
        gcongr; exact R₀.first_retention
      _ ≤ (d / 12 / 12 / 2) * (R₁.first.card : ℝ) := by gcongr; exact R₁.first_retention
      _ ≤ _ := R₂.first_retention
  have hGret : d ^ 3 * δ ^ ζ / 27648 * (G.card : ℝ) ≤ R₂.second.card := by
    calc d ^ 3 * δ ^ ζ / 27648 * (G.card : ℝ) =
          (d / 12 / 12 / 2) * ((d / 12 / 2) * (δ ^ ζ / 2 * ((d / 2) * (G.card : ℝ)))) := by ring
      _ ≤ (d / 12 / 12 / 2) * ((d / 12 / 2) * (δ ^ ζ / 2 * (R₀.second.card : ℝ))) := by
        gcongr; exact R₀.second_retention
      _ ≤ (d / 12 / 12 / 2) * ((d / 12 / 2) * (G'.card : ℝ)) := by gcongr
      _ ≤ (d / 12 / 12 / 2) * (R₁.second.card : ℝ) := by gcongr; exact R₁.second_retention
      _ ≤ _ := R₂.second_retention
  have hUret : d ^ 3 * δ ^ ζ / 27648 * (U.card : ℝ) ≤ R₂.third.card := by
    calc d ^ 3 * δ ^ ζ / 27648 * (U.card : ℝ) =
          (d / 12 / 12 / 2) * (δ ^ ζ / 2 * ((d / 12 / 2) * ((d / 2) * (U.card : ℝ)))) := by ring
      _ ≤ (d / 12 / 12 / 2) * (δ ^ ζ / 2 * ((d / 12 / 2) * (R₀.third.card : ℝ))) := by
        gcongr; exact R₀.third_retention
      _ ≤ (d / 12 / 12 / 2) * (δ ^ ζ / 2 * (R₁.third.card : ℝ)) := by gcongr; exact R₁.third_retention
      _ ≤ (d / 12 / 12 / 2) * (U'.card : ℝ) := by gcongr
      _ ≤ _ := R₂.third_retention
  have hGline₁ := hG'line.subset hδ.le (hδ.trans_le hw₁) (by norm_num) (by positivity)
    R₁.second_subset R₁.second_retention
  have hGline₂ := hGline₁.subset hδ.le (hδ.trans_le hw₁) (by positivity) (by positivity)
    R₂.second_subset R₂.second_retention
  have hUline₂ := hU'line.subset hδ.le (hδ.trans_le hw₂) (by norm_num) (by positivity)
    R₂.third_subset R₂.third_retention
  have hGK : (2 / (d / 12 / 2)) / (d / 12 / 12 / 2) = 13824 / d ^ 2 := by field_simp; ring
  have hUK : 2 / (d / 12 / 12 / 2) ≤ 13824 / d ^ 2 := by
    field_simp
    nlinarith
  refine ⟨{
    first := R₂.first
    second := R₂.second
    third := R₂.third
    edges := R₂.edges
    first_subset := ?_
    second_subset := ?_
    third_subset := ?_
    edges_subset := ?_
    nonempty := R₂.nonempty
    contained := R₂.contained
    first_support := R₂.first_support
    second_support := R₂.second_support
    third_support := R₂.third_support
    first_retention := hFret
    second_retention := hGret
    third_retention := hUret
    uniform := ?_
    normal_second := n₁
    normal_third := n₂
    center_second := c₁
    center_third := c₂
    width_second := w₁
    width_third := w₂
    unit_second := hn₁
    unit_third := hn₂
    width_second_lower := hw₁
    width_third_lower := hw₂
    width_second_upper := hw₁1
    width_third_upper := hw₂1
    strip_second := ?_
    strip_third := ?_
    line_second := ?_
    line_third := ?_
  }⟩
  · exact R₂.first_subset.trans (R₁.first_subset.trans R₀.first_subset)
  · exact R₂.second_subset.trans (R₁.second_subset.trans (hG'.trans R₀.second_subset))
  · exact R₂.third_subset.trans (hU'.trans (R₁.third_subset.trans R₀.third_subset))
  · exact R₂.edges_subset.trans ((restrictThird_subset _ _).trans
      (R₁.edges_subset.trans ((restrictSecond_subset _ _).trans R₀.edges_subset)))
  · simpa only [show d / 12 / 12 / 12 = d / 1728 by ring] using R₂.uniform
  · exact fun x hx => hG'strip x (R₁.second_subset (R₂.second_subset hx))
  · exact fun b hb => hU'strip b (R₂.third_subset hb)
  · simpa only [hGK] using hGline₂
  · exact hUline₂.mono_constant hδ.le (hδ.trans_le hw₂) hUK

end WangZahlLot.Obl.wz_separated_projection_dichotomy
