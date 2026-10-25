/- Adapted from this LOT tree, obligation o100, session x0340, commit efabdd9,
   Submission/Obl/k4_scalar_marked_profile_selection/Budgets.lean. -/
import Submission.Obl.k4_marked_scalar_grid_selection.Scalar.FiniteBands
import Submission.Obl.k4_marked_scalar_grid_selection.Scalar.Losses

noncomputable section

namespace Submission.Obl.k4_marked_scalar_grid_selection.Scalar

open MeasureTheory Set
open scoped ENNReal

/-- The three support and overlap polynomials are absorbed by a fixed cubic. -/
theorem geometry_coefficients_le {K : ℝ} (hK : 1 ≤ K) :
    52 * (10 * (K + 1) + 1) * (8 * (10 * (K + 1)) + 18) ≤ geometryLoss K ∧
    jointOverlapLoss (10 * (K + 1)) ≤ geometryLoss K ∧
    pureOverlapLoss K (10 * (K + 1)) ≤ geometryLoss K ∧
    2 * (10 * (K + 1) + 1) * (8 * (10 * (K + 1)) + 18) ≤ geometryLoss K := by
  dsimp [geometryLoss, jointOverlapLoss, pureOverlapLoss]
  have hK0 : 0 ≤ K := by linarith
  have hK2 : 1 ≤ K ^ 2 := one_le_pow₀ hK
  have hK23 : K ^ 2 ≤ K ^ 3 := by nlinarith [sq_nonneg (K - 1)]
  have h1 : 10 * (K + 1) + 1 ≤ 21 * K := by linarith
  have h2 : 8 * (10 * (K + 1)) + 18 ≤ 178 * K := by linarith
  have h3 : 8 * (10 * (K + 1)) + 10 ≤ 170 * K := by linarith
  have h4 : 8 * K + 10 ≤ 18 * K := by linarith
  have hprod1 := mul_le_mul h1 h2 (by positivity) (by positivity : 0 ≤ 21 * K)
  have hprod2 := mul_le_mul h3 h2 (by positivity) (by positivity : 0 ≤ 170 * K)
  have hprod3 := mul_le_mul hprod2 h4 (by positivity) (by positivity : 0 ≤ 170 * K * (178 * K))
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

/-- Repeating a probability vector over time cells gives total tag weight `J`. -/
theorem atom_tag_weight_sum_le {H J : ℕ} (w : Fin H → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hw1 : ∑ j, w j = 1) (I : Finset (AtomIndex H J)) :
    ∑ i ∈ I, w i.1 ≤ (J : ℝ) := by
  classical
  calc
    _ ≤ ∑ i : AtomIndex H J, w i.1 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I) (fun i _ _ => hw i.1)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← Finset.mul_sum, hw1, mul_one]

/-- A uniform atom cap can be summed before estimating the old record budget. -/
theorem node_weight_sum_le {H J : ℕ} (w : Fin H → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hw1 : ∑ j, w j = 1) (I : Finset (AtomIndex H J)) {c : ℝ} (hc : 0 ≤ c) :
    (∑ i ∈ I, ENNReal.ofReal (w i.1) * ENNReal.ofReal c) ≤ ENNReal.ofReal ((J : ℝ) * c) := by
  rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i.1),
    ← ENNReal.ofReal_mul (Finset.sum_nonneg (fun i _ => hw i.1))]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (atom_tag_weight_sum_le w hw hw1 I) hc)

/-- The noise-gain factor cancels the enlargement of the slope support. -/
theorem max_noise_cancellation {σ ρ : ℝ} (hσ : 0 < σ) (hρ : 0 < ρ) :
    max σ ρ / ρ * min 1 (ρ / σ) = 1 := by
  rcases le_total ρ σ with h | h
  · rw [max_eq_left h, min_eq_right ((div_le_one hσ).mpr h)]
    field_simp
  · rw [max_eq_right h, min_eq_left ((le_div_iff₀ hσ).mpr (by simpa using h))]
    field_simp

/-- The entire original joint record budget is polynomial in the coefficient loss. -/
theorem joint_record_budget {H J : ℕ} (hJ : 0 < J) {σ ρ K : ℝ}
    (hσ : 0 < σ) (hρ : 0 < ρ) (hK : 1 ≤ K)
    (w : Fin H → ℝ) (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1)
    (I : Finset (AtomIndex H J)) :
    ENNReal.ofReal (jointVolumeLoss J σ ρ (max σ ρ) (10 * (K + 1))) *
      (∑ i ∈ I, jointNodeWeight σ ρ w i) ≤ ENNReal.ofReal (geometryLoss K) := by
  have hJ0 : 0 < (J : ℝ) := Nat.cast_pos.mpr hJ
  have hc : 0 ≤ σ⁻¹ * min 1 (ρ / σ) := by positivity
  have hA : 0 ≤ jointVolumeLoss J σ ρ (max σ ρ) (10 * (K + 1)) := by
    dsimp [jointVolumeLoss]; positivity
  calc
    _ ≤ ENNReal.ofReal (jointVolumeLoss J σ ρ (max σ ρ) (10 * (K + 1))) *
        ENNReal.ofReal ((J : ℝ) * (σ⁻¹ * min 1 (ρ / σ))) :=
      mul_le_mul' le_rfl (node_weight_sum_le w hw hw1 I hc)
    _ = ENNReal.ofReal (52 * (10 * (K + 1) + 1) * (8 * (10 * (K + 1)) + 18)) := by
      have halg : jointVolumeLoss J σ ρ (max σ ρ) (10 * (K + 1)) *
          ((J : ℝ) * (σ⁻¹ * min 1 (ρ / σ))) =
          52 * (10 * (K + 1) + 1) * (8 * (10 * (K + 1)) + 18) := by
        dsimp [jointVolumeLoss]
        calc
          _ = (52 * (10 * (K + 1) + 1) * (8 * (10 * (K + 1)) + 18)) *
              (max σ ρ / ρ * min 1 (ρ / σ)) := by
                field_simp [ne_of_gt hσ, ne_of_gt hJ0]
                <;> ring
          _ = _ := by rw [max_noise_cancellation hσ hρ, mul_one]
      rw [← ENNReal.ofReal_mul hA, halg]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (geometry_coefficients_le hK).1

/-- The pure record budget uses the same normalized atom weights at slope depth zero. -/
theorem pure_record_budget {H J : ℕ} (hJ : 0 < J) {σ K : ℝ}
    (hσ : 0 < σ) (hK : 1 ≤ K)
    (w : Fin H → ℝ) (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1)
    (I : Finset (AtomIndex H J)) :
    ENNReal.ofReal (pureVolumeLoss J σ (10 * (K + 1))) *
      (∑ i ∈ I, pureNodeWeight σ w i) ≤ ENNReal.ofReal (geometryLoss K) := by
  have hJ0 : 0 < (J : ℝ) := Nat.cast_pos.mpr hJ
  have hA : 0 ≤ pureVolumeLoss J σ (10 * (K + 1)) := by dsimp [pureVolumeLoss]; positivity
  calc
    _ ≤ ENNReal.ofReal (pureVolumeLoss J σ (10 * (K + 1))) *
        ENNReal.ofReal ((J : ℝ) * σ⁻¹) :=
      mul_le_mul' le_rfl (node_weight_sum_le w hw hw1 I (inv_nonneg.mpr hσ.le))
    _ = ENNReal.ofReal (2 * (10 * (K + 1) + 1) * (8 * (10 * (K + 1)) + 18)) := by
      rw [← ENNReal.ofReal_mul hA]
      congr 1
      dsimp [pureVolumeLoss]
      field_simp [ne_of_gt hσ, ne_of_gt hJ0]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (geometry_coefficients_le hK).2.2.2

/-- At unit slope width the joint and pure original node weights coincide. -/
theorem jointNodeWeight_one {H J : ℕ} {σ : ℝ} (hσ : 0 < σ) (hσ₁ : σ ≤ 1)
    (w : Fin H → ℝ) (i : AtomIndex H J) :
    jointNodeWeight σ 1 w i = pureNodeWeight σ w i := by
  have h : 1 ≤ 1 / σ := (le_div_iff₀ hσ).mpr (by simpa using hσ₁)
  simp only [jointNodeWeight, pureNodeWeight, min_eq_left h, mul_one]

end Submission.Obl.k4_marked_scalar_grid_selection.Scalar
