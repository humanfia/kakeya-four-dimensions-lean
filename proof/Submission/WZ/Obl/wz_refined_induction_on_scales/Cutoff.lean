-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_refined_induction_on_scales.Cutoff.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_refined_induction_on_scales.FiniteScales

namespace WangZahlLot.Obl.wz_refined_induction_on_scales

open MeasureTheory LeanEval.Analysis.WangZahlKakeya

/-- Removing a small-scale cutoff costs only the leading volume constant.
The geometric second alternative is arbitrary and is preserved exactly. -/
theorem remove_scale_cutoff {σ w η κ₀ δ₀ : ℝ} (hσ : 0 ≤ σ) (hη : 0 ≤ η)
    (hκ₀ : 0 < κ₀) (hδ₀ : 0 < δ₀)
    (B : ℝ → (n : ℕ) → (Fin n → Space) → (Fin n → Space) →
      (Fin n → Set Space) → Prop)
    (hsmall : ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → δ ≤ δ₀ → ∀ n x v Y,
      Hypotheses δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y →
      ENNReal.ofReal (κ₀ * δ ^ w * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤
        volume (⋃ i, Y i) ∨ B δ n x v Y) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ n x v Y,
      Hypotheses δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y →
      ENNReal.ofReal (κ * δ ^ w * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤
        volume (⋃ i, Y i) ∨ B δ n x v Y := by
  obtain ⟨κ₁, hκ₁, hlarge⟩ := first_alternative_away_from_zero hσ hη hδ₀ w
  refine ⟨min κ₀ κ₁, lt_min hκ₀ hκ₁, ?_⟩
  intro δ hδ hδ100 n x v Y h
  have hcompare : ∀ κ' : ℝ, min κ₀ κ₁ ≤ κ' →
      ENNReal.ofReal (min κ₀ κ₁ * δ ^ w * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤
        ENNReal.ofReal (κ' * δ ^ w * (n * δ ^ 2) * (n * δ) ^ (-σ)) := by
    intro κ' hκ'
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hκ' (Real.rpow_nonneg hδ.le _)) (by positivity))
      (Real.rpow_nonneg (by positivity) _)
  by_cases hδsmall : δ ≤ δ₀
  · rcases hsmall δ hδ hδ100 hδsmall n x v Y h with hbound | hB
    · exact Or.inl ((hcompare κ₀ (min_le_left _ _)).trans hbound)
    · exact Or.inr hB
  · exact Or.inl ((hcompare κ₁ (min_le_right _ _)).trans
      (hlarge δ (le_of_not_ge hδsmall) (by linarith) n x v Y h))

end WangZahlLot.Obl.wz_refined_induction_on_scales
