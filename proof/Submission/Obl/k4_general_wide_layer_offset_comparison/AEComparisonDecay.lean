import Submission.Obl.k4_general_wide_layer_offset_comparison.AEComparison

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/AEComparisonDecay.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set Metric
open Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

noncomputable section

namespace AEWeightComparison

variable {ι₁ ι₂ Λ Ω : Type*} [MeasurableSpace Ω]
    [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] [DecidableEq Λ]
    (S : AEWeightComparison ι₁ ι₂ Λ Ω)

/-- The geometric discrepancy bound applies to the original smoothed law
with its literal almost-everywhere support statements. -/
theorem decay_against_original_weights_ae
    (r : ℕ) (hr : 0 < r)
    (hweights : ∀ l, S.weight₁ l ≤ (r : ℝ) * S.weight₂ l)
    (hround : ∀ l, (r : ℝ) * S.weight₂ l ≤ 2 * S.weight₁ l)
    (hK : 0 < S.K) (hw : ∀ l, 0 < S.weight₂ l)
    (J : JetData) {M₀ R A d₀ ε₀ R₀ ε d : ℝ}
    (hmb : MatchBound d₀ ε₀ R₀) (hR₀ : 2 ≤ R₀)
    (hε : 0 < ε) (hεε₀ : ε ≤ ε₀) (hM₀ : 0 < M₀)
    (hReq : R = M₀ / (2 * S.error)) (hR : R₀ ≤ R)
    (hC : 3 * J.C₂ ≤ R ^ ε) (hA : 0 ≤ A) (hAR : A ≤ 2 * R ^ d₀)
    (hdd : d ≤ d₀)
    (hband : ∀ i : ι₁ ⊕ ι₂, ∀ k : ℕ,
      S.law {p | S.lab₁ (S.src p) = Sum.elim S.lab₁ S.lab₂ i ∧
        ‖Sum.elim S.φ₁ S.φ₂ i (emb (S.point p)) - (S.value p : ℂ)‖ ≤ 2 * (M₀ * 2 ^ k)} ≤
        ENNReal.ofReal (S.K * S.weight₂ (Sum.elim S.lab₁ S.lab₂ i) * A * ((2 : ℝ) ^ d) ^ k)) :
    S.law {p | ∃ y : EuclideanSpace ℝ (Fin 3), ‖y‖ ≤ 1 / 2 ∧
      M₀ ≤ ‖S.φ₁ (S.src p) (emb y) - S.φ₂ (S.wit p) (emb y)‖} ≤
      ENNReal.ofReal (8 *
        (((2 * cubeRadius J + 1) ^ Fintype.card (↥J.V × Fin J.q) : ℕ) : ℝ) /
        (1 - (2 : ℝ) ^ (-ε / 2)) * S.K * R ^ (-ε) *
          (2 * (∑ i, S.weight₁ (S.lab₁ i)) + ∑ j, S.weight₂ (S.lab₂ j))) := by
  obtain ⟨G, hG, hfull, hgood⟩ := S.exists_full_carrier
  let C := S.onCarrier G hG hgood
  have hbandC : ∀ i : ι₁ ⊕ ι₂, ∀ k : ℕ,
      C.law {p | C.lab₁ (C.src p) = Sum.elim C.lab₁ C.lab₂ i ∧
        ‖Sum.elim C.φ₁ C.φ₂ i (emb (C.point p)) - (C.value p : ℂ)‖ ≤ 2 * (M₀ * 2 ^ k)} ≤
        ENNReal.ofReal (C.K * C.weight₂ (Sum.elim C.lab₁ C.lab₂ i) * A * ((2 : ℝ) ^ d) ^ k) := by
    intro i k
    change (S.law.comap (Subtype.val : G → Ω)) (Subtype.val ⁻¹'
      {p | S.lab₁ (S.src p) = Sum.elim S.lab₁ S.lab₂ i ∧
        ‖Sum.elim S.φ₁ S.φ₂ i (emb (S.point p)) - (S.value p : ℂ)‖ ≤ 2 * (M₀ * 2 ^ k)}) ≤ _
    rw [S.carrier_event_measure G hG hfull]
    exact hband i k
  have hb := C.decay_against_original_weights r hr hweights hround hK hw J hmb hR₀
    hε hεε₀ hM₀ hReq hR hC hA hAR hdd hbandC
  change (S.law.comap (Subtype.val : G → Ω)) (Subtype.val ⁻¹'
      {p | ∃ y : EuclideanSpace ℝ (Fin 3), ‖y‖ ≤ 1 / 2 ∧
        M₀ ≤ ‖S.φ₁ (S.src p) (emb y) - S.φ₂ (S.wit p) (emb y)‖}) ≤ _ at hb
  rwa [S.carrier_event_measure G hG hfull] at hb

end AEWeightComparison
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
