import Submission.Obl.k4_general_wide_layer_offset_comparison.ClonedComparison

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/WeightedComparisonDecay.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set Metric
open Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing
open Submission.Lib.K4OriginalStatePreparation

noncomputable section

namespace TwoWeightComparison

variable {ι₁ ι₂ Λ Ω : Type*} [MeasurableSpace Ω]
    [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] [DecidableEq Λ]
    (S : TwoWeightComparison ι₁ ι₂ Λ Ω)

/-- A native band ceiling at every discrepancy scale gives a power saving
against the two separate original reference budgets. The rounding copies
cost at most twice the coarse reference weight. -/
theorem decay_against_original_weights
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
  have hRp : 0 < R := lt_of_lt_of_le (by linarith : (0 : ℝ) < R₀) hR
  have hχ : 0 < (2 : ℝ) ^ (-ε / 2) := by positivity
  have hχ1 : (2 : ℝ) ^ (-ε / 2) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  let θ : Λ → ℝ := fun l => 2 * S.K * S.weight₂ l * R ^ (-ε)
  let G : Λ → ℝ := fun l => S.K * S.weight₂ l * A
  have hθ (l : Λ) : 0 < θ l := by
    have hwl := hw l
    dsimp [θ]
    positivity
  have hG (l : Λ) : 0 ≤ G l := by
    have hwl := hw l
    dsimp [G]
    positivity
  have hρ (l : Λ) : (S.K * S.weight₂ l) * R ^ (-ε) ≤ θ l / 2 := by
    dsimp [θ]
    linarith
  have hΓ (l : Λ) : G l / θ l ≤ R ^ (d₀ + ε) := by
    rw [div_le_iff₀ (hθ l)]
    dsimp [G, θ]
    have hprod : R ^ (d₀ + ε) * R ^ (-ε) = R ^ d₀ := by
      rw [← Real.rpow_add hRp]
      congr 1
      ring
    calc
      _ ≤ S.K * S.weight₂ l * (2 * R ^ d₀) :=
        mul_le_mul_of_nonneg_left hAR (mul_nonneg hK.le (hw l).le)
      _ = _ := by
        calc
          _ = (2 * S.K * S.weight₂ l) * (R ^ (d₀ + ε) * R ^ (-ε)) := by rw [hprod]; ring
          _ = _ := by ring
  have hρgrow : (2 : ℝ) ^ (-ε) ≤ (2 : ℝ) ^ (-ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hΓgrow : (2 : ℝ) ^ d ≤ (2 : ℝ) ^ (-ε / 2) * (2 : ℝ) ^ (d₀ + ε) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hbase : R₀ * (2 * S.error) ≤ M₀ := by
    have h := (le_div_iff₀ (by have := S.error_pos; positivity : 0 < 2 * S.error)).mp
      (hR.trans_eq hReq)
    exact h
  have hb := S.discrepancy_mass_le r hr hweights J M₀ θ G hmb hR₀ hε hεε₀ hM₀
    hχ hχ1 hθ hG hbase (by simpa only [← hReq] using hC)
    (by intro l; simpa only [← hReq] using hρ l) hρgrow
    (by intro l; simpa only [← hReq] using hΓ l) hΓgrow hband
  have hθsum₁ : (∑ i, θ (S.lab₁ i)) =
      (2 * S.K * R ^ (-ε)) * ∑ i, S.weight₂ (S.lab₁ i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [θ]
    ring
  have hθsum₂ : (∑ j, θ (S.lab₂ j)) =
      (2 * S.K * R ^ (-ε)) * ∑ j, S.weight₂ (S.lab₂ j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [θ]
    ring
  rw [hθsum₁, hθsum₂] at hb
  apply hb.trans
  apply ENNReal.ofReal_le_ofReal
  have hbudget : (r : ℝ) * (∑ i, S.weight₂ (S.lab₁ i)) ≤
      2 * ∑ i, S.weight₁ (S.lab₁ i) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hround (S.lab₁ i)
  have hfactor : 0 ≤ 4 *
      (((2 * cubeRadius J + 1) ^ Fintype.card (↥J.V × Fin J.q) : ℕ) : ℝ) /
      (1 - (2 : ℝ) ^ (-ε / 2)) * (2 * S.K * R ^ (-ε)) := by positivity
  calc
    _ = (4 *
      (((2 * cubeRadius J + 1) ^ Fintype.card (↥J.V × Fin J.q) : ℕ) : ℝ) /
      (1 - (2 : ℝ) ^ (-ε / 2)) * (2 * S.K * R ^ (-ε))) *
        ((r : ℝ) * (∑ i, S.weight₂ (S.lab₁ i)) + ∑ j, S.weight₂ (S.lab₂ j)) := by ring
    _ ≤ (4 *
      (((2 * cubeRadius J + 1) ^ Fintype.card (↥J.V × Fin J.q) : ℕ) : ℝ) /
      (1 - (2 : ℝ) ^ (-ε / 2)) * (2 * S.K * R ^ (-ε))) *
        (2 * (∑ i, S.weight₁ (S.lab₁ i)) + ∑ j, S.weight₂ (S.lab₂ j)) :=
      mul_le_mul_of_nonneg_left (add_le_add hbudget le_rfl) hfactor
    _ = _ := by ring

end TwoWeightComparison
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
