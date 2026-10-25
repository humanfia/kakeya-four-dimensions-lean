import Submission.Obl.k4_oss_weighted_level_transfer.Finite

open MeasureTheory Set
open scoped BigOperators NNReal ENNReal

namespace Submission.Obl.k4_oss_weighted_level_transfer

/-- The finite averaged-energy hypothesis at one scale. -/
def FiniteGain (s γ θ δ : ℝ) : Prop :=
  ∀ d : ℝ, 0 ≤ d → d ≤ 1 - γ / 4 →
  ∀ A B : Finset ℝ, A.Nonempty → B.Nonempty →
  (∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → δ ≤ dist a a') →
  (∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → δ ≤ dist b b') →
  (∀ x u : ℝ, δ ≤ u →
    ((A.filter (fun a => dist a x ≤ u)).card : ℝ) ≤ δ ^ (-θ) * u ^ (s / 2) * A.card) →
  (∀ x u : ℝ, δ ≤ u →
    ((B.filter (fun a => dist a x ≤ u)).card : ℝ) ≤ δ ^ (-θ) * u ^ (s / 2) * B.card) →
  δ ^ (θ - d) ≤ (A.card : ℝ) → (A.card : ℝ) ≤ δ ^ (-d - θ) →
  δ ^ (θ - d) ≤ (B.card : ℝ) → (B.card : ℝ) ≤ δ ^ (-d - θ) →
  ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ν (Icc (1 / 4 : ℝ) 1)ᶜ = 0 →
  (∀ x u : ℝ, δ ≤ u → u ≤ 1 →
    ν (Icc (x - u) (x + u)) ≤ ENNReal.ofReal (δ ^ (-θ) * u ^ (s / 2))) →
  (∫⁻ t, ENNReal.ofReal (finiteEnergy δ t A B) ∂ν) ≤
    ENNReal.ofReal (δ ^ θ * (A.card : ℝ) ^ 2 * (B.card : ℝ))

lemma common_dimension {δ γ θ h X Y : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hγ : 0 < γ) (hhθ : h ≤ θ) (hθ : 0 ≤ θ)
    (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hXu : X ≤ δ ^ (-1 + γ / 2)) (hYu : Y ≤ δ ^ (-1 + γ / 2))
    (hXY : δ ^ h * X ≤ Y) (hYX : δ ^ h * Y ≤ X) :
    ∃ d : ℝ, 0 ≤ d ∧ d ≤ 1 - γ / 4 ∧
      δ ^ (θ - d) ≤ X ∧ X ≤ δ ^ (-d - θ) ∧
      δ ^ (θ - d) ≤ Y ∧ Y ≤ δ ^ (-d - θ) := by
  let N := max X Y
  let d := -Real.logb δ N
  have hN : 0 < N := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hX.trans (le_max_left _ _))
  have hd : δ ^ (-d) = N := by
    simp only [d, neg_neg]
    exact Real.rpow_logb hδ (ne_of_lt hδ1) hN
  have hd0 : 0 ≤ d := by
    have hpow : δ ^ (0 : ℝ) ≤ δ ^ (-d) := by
      rw [Real.rpow_zero, hd]
      exact hX.trans (le_max_left _ _)
    have := (Real.rpow_le_rpow_left_iff_of_base_lt_one hδ hδ1).mp hpow
    linarith
  have hd1 : d ≤ 1 - γ / 2 := by
    have hpow : δ ^ (-d) ≤ δ ^ (-1 + γ / 2) := by
      rw [hd]
      exact max_le hXu hYu
    have := (Real.rpow_le_rpow_left_iff_of_base_lt_one hδ hδ1).mp hpow
    linarith
  have hlo : δ ^ (θ - d) ≤ δ ^ h * N := by
    rw [sub_eq_add_neg, Real.rpow_add hδ, hd]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1.le hhθ) hN.le
  have hhi : N ≤ δ ^ (-d - θ) := by
    rw [sub_eq_add_neg, Real.rpow_add hδ, hd]
    have hp : 1 ≤ δ ^ (-θ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1.le (by linarith)
    nlinarith
  refine ⟨d, hd0, by linarith, ?_, (le_max_left _ _).trans hhi, ?_, (le_max_right _ _).trans hhi⟩
  · apply hlo.trans
    rcases le_total X Y with horder | horder
    · simpa only [N, max_eq_right horder] using hYX
    · simpa only [N, max_eq_left horder] using
        (show δ ^ h * X ≤ X from (hXY.trans horder))
  · apply hlo.trans
    rcases le_total X Y with horder | horder
    · simpa only [N, max_eq_right horder] using
        (show δ ^ h * Y ≤ Y from (hYX.trans horder))
    · simpa only [N, max_eq_left horder] using hXY

end Submission.Obl.k4_oss_weighted_level_transfer
