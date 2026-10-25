-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.TwoStripAlignment.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.Alignment
import Submission.WZ.Obl.wz_separated_projection_dichotomy.TripleSwap

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

theorem perp_neg_perp (n : Plane) : perp (-perp n) = n := by
  ext i
  fin_cases i <;> simp [perp]

/-- Align using whichever of the two localized strips has smaller width.
Only one invocation of the alignment lemma is needed. -/
theorem two_strip_alignment {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → δ ≤ 1 →
      ∀ (F G U : Finset Plane) (H : Finset Triple), H.Nonempty → H ⊆ F ×ˢ (G ×ˢ U) →
        (∀ a ∈ F, ‖a‖ ≤ 4) → (∀ x ∈ G, ‖x‖ ≤ 4) → (∀ b ∈ U, ‖b‖ ≤ 4) →
        ClosedFiniteFrostman δ (δ ^ (-η)) F → ClosedFiniteFrostman δ (δ ^ (-η)) G →
        ClosedFiniteFrostman δ (δ ^ (-η)) U →
        (∀ x ∈ G, ∀ b ∈ U, 1 / 2 ≤ ‖b - x‖) →
        TripleUniform (δ ^ η) F G U H →
        (∀ a ∈ F, ∃ x b, (a, x, b) ∈ H) →
        (∀ x ∈ G, ∃ a b, (a, x, b) ∈ H) → (∀ b ∈ U, ∃ a x, (a, x, b) ∈ H) →
        ∀ (n₁ n₂ : Plane) (c₁ c₂ w₁ w₂ : ℝ), ‖n₁‖ = 1 → ‖n₂‖ = 1 → δ ≤ w₁ → δ ≤ w₂ →
          (∀ x ∈ G, |inner ℝ x n₁ - c₁| ≤ w₁) → (∀ b ∈ U, |inner ℝ b n₂ - c₂| ≤ w₂) →
          (∃ (e : Plane) (c : ℝ), ‖e‖ = 1 ∧
            (∀ a ∈ F, |inner ℝ a e| ≤ δ ^ (-ε) * min w₁ w₂) ∧
            (∀ x ∈ G, |inner ℝ x (perp e) - c| ≤ δ ^ (-ε) * min w₁ w₂) ∧
            (∀ b ∈ U, |inner ℝ b (perp e) - c| ≤ δ ^ (-ε) * min w₁ w₂)) ∨
          ProjectionGain δ η ε (↑H : Set Triple) := by
  classical
  obtain ⟨η, δ₀, hη, hδ₀, halign⟩ := strip_alignment hε hε1
  refine ⟨η, δ₀, hη, hδ₀, ?_⟩
  intro δ hδ hsmall hδ1 F G U H hHne hH hFn hGn hUn hF hG hU hsep huni hFon hGon hUon
    n₁ n₂ c₁ c₂ w₁ w₂ hn₁ hn₂ hw₁ hw₂ hstrip₁ hstrip₂
  have hpow : 1 ≤ δ ^ (-ε) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have he₁ : ‖-perp n₁‖ = 1 := by simpa only [norm_neg, perp_norm] using hn₁
  have he₂ : ‖-perp n₂‖ = 1 := by simpa only [norm_neg, perp_norm] using hn₂
  by_cases hw : w₁ ≤ w₂
  · have hal := halign δ hδ hsmall F G U H hHne hH hFn hGn hUn hF hG hsep huni hFon hUon
      (-perp n₁) c₁ w₁ he₁ hw₁ (by simpa only [perp_neg_perp] using hstrip₁)
    rcases hal with htrap | hgain
    · left
      refine ⟨-perp n₁, c₁, he₁, ?_, ?_, ?_⟩
      · simpa only [min_eq_left hw] using htrap.1
      · intro x hx
        rw [min_eq_left hw, perp_neg_perp]
        exact (hstrip₁ x hx).trans (by nlinarith [hδ.trans_le hw₁])
      · simpa only [min_eq_left hw] using htrap.2
    · exact Or.inr hgain
  · have hw' : w₂ ≤ w₁ := (lt_of_not_ge hw).le
    have hFon' : ∀ a ∈ F, ∃ b x, (a, b, x) ∈ H.image swapTriple := by
      intro a ha
      obtain ⟨x, b, hp⟩ := hFon a ha
      exact ⟨b, x, Finset.mem_image.mpr ⟨(a, x, b), hp, rfl⟩⟩
    have hGon' : ∀ x ∈ G, ∃ a b, (a, b, x) ∈ H.image swapTriple := by
      intro x hx
      obtain ⟨a, b, hp⟩ := hGon x hx
      exact ⟨a, b, Finset.mem_image.mpr ⟨(a, x, b), hp, rfl⟩⟩
    have hsep' : ∀ b ∈ U, ∀ x ∈ G, 1 / 2 ≤ ‖x - b‖ := by
      intro b hb x hx
      simpa only [norm_sub_rev] using hsep x hx b hb
    have hal := halign δ hδ hsmall F U G (H.image swapTriple) (hHne.image _) (swapTriple_contained hH)
      hFn hUn hGn hF hU hsep' huni.swap hFon' hGon'
      (-perp n₂) c₂ w₂ he₂ hw₂ (by simpa only [perp_neg_perp] using hstrip₂)
    rcases hal with htrap | hgain
    · left
      refine ⟨-perp n₂, c₂, he₂, ?_, ?_, ?_⟩
      · simpa only [min_eq_right hw'] using htrap.1
      · simpa only [min_eq_right hw'] using htrap.2
      · intro b hb
        rw [min_eq_right hw', perp_neg_perp]
        exact (hstrip₂ b hb).trans (by nlinarith [hδ.trans_le hw₂])
    · exact Or.inr hgain.of_swap

end WangZahlLot.Obl.wz_separated_projection_dichotomy
