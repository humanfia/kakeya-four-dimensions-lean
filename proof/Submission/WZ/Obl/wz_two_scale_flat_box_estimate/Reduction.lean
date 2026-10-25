-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_two_scale_flat_box_estimate.Reduction.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.Monotonicity

namespace WangZahlLot.Obl.wz_two_scale_flat_box_estimate

open MeasureTheory Set Metric

/-- The only remaining configurations are at sufficiently small scales and have
an aspect ratio larger than the error allowance. -/
def FlatSmallScaleConclusion (σ ω : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ κ η d : ℝ, 0 < κ ∧ 0 < η ∧ 0 < d ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → δ ≤ d →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
    Admissible δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y →
    ∀ ρ : ℝ, δ ≤ ρ → ρ ≤ 1 → ∀ N y w f, Cover δ η n x v Y .univ Y ρ N y w f →
    ∀ a b c : ℝ, ρ ≤ a → a ≤ b → b ≤ c → 1 ≤ c → c ≤ 8 →
    δ ^ (-(ε / 2)) < (b / a) ^ ω →
    ∀ (L : ℕ) (z : Fin L → Space) (e : Fin L → Space ≃ₗᵢ[ℝ] Space) (g : Fin N → Fin L),
    BoxCover δ η ρ a b c N L y w z e g →
    ENNReal.ofReal (bound σ ω ε κ δ a b n) ≤ volume (⋃ i, Y i)

/-- The elementary E applications absorb the cutoff and near-round cases,
including the loss from selecting a common admissibility exponent. -/
theorem conclusion_of_flat_small_scale {σ ω : ℝ} (hσ : 0 ≤ σ) (hω : 0 ≤ ω)
    (hE : Estimate σ ω) (hFlat : FlatSmallScaleConclusion σ ω) : Conclusion σ ω := by
  intro ε hε
  obtain ⟨κf, ηf, d, hκf, hηf, hd, Hf⟩ := hFlat ε hε
  obtain ⟨κr, ηr, hκr, hηr, Hr⟩ := near_round_from_estimate hσ hE hε
  obtain ⟨κl, ηl, hκl, hηl, Hl⟩ := large_scale_from_estimate hσ hω hE hε hd
  let κ := min κf (min κr κl)
  let η := min ηf (min ηr ηl)
  have hκ : 0 < κ := lt_min hκf (lt_min hκr hκl)
  have hη : 0 < η := lt_min hηf (lt_min hηr hηl)
  have hκf' : κ ≤ κf := min_le_left _ _
  have hκr' : κ ≤ κr := (min_le_right _ _).trans (min_le_left _ _)
  have hκl' : κ ≤ κl := (min_le_right _ _).trans (min_le_right _ _)
  have hηf' : η ≤ ηf := min_le_left _ _
  have hηr' : η ≤ ηr := (min_le_right _ _).trans (min_le_left _ _)
  have hηl' : η ≤ ηl := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨κ, hκ, η, hη, ?_⟩
  intro δ hδ hδ100 n x v Y hA ρ hδρ hρ1 N y w f hC a b c hρa hab hbc hc1 hc8 L z e g hBox
  have hδ1 : δ ≤ 1 := hδ100.trans (by norm_num)
  have hδa : δ ≤ a := hδρ.trans hρa
  have ha : 0 < a := hδ.trans_le hδa
  have hb : 0 < b := ha.trans_le hab
  by_cases hsmall : δ ≤ d
  · by_cases hround : (b / a) ^ ω ≤ δ ^ (-(ε / 2))
    · exact (ENNReal.ofReal_le_ofReal
        (bound_mono hκr' hδ.le ha.le hb.le (Nat.cast_nonneg n))).trans
        (Hr δ hδ hδ100 n x v Y (admissible_mono_error hδ hδ1 hηr' hA) a b hround)
    · exact (ENNReal.ofReal_le_ofReal
        (bound_mono hκf' hδ.le ha.le hb.le (Nat.cast_nonneg n))).trans
        (Hf δ hδ hδ100 hsmall n x v Y (admissible_mono_error hδ hδ1 hηf' hA)
          ρ hδρ hρ1 N y w f (cover_mono_error hδ hδ1 hηf' hC)
          a b c hρa hab hbc hc1 hc8 (lt_of_not_ge hround)
          L z e g (boxCover_mono_error hδ hδ1 hηf' hBox))
  · exact (ENNReal.ofReal_le_ofReal
      (bound_mono hκl' hδ.le ha.le hb.le (Nat.cast_nonneg n))).trans
      (Hl δ hδ hδ100 (le_of_not_ge hsmall) n x v Y
        (admissible_mono_error hδ hδ1 hηl' hA) a b hδa hb.le (hbc.trans hc8))

end WangZahlLot.Obl.wz_two_scale_flat_box_estimate
