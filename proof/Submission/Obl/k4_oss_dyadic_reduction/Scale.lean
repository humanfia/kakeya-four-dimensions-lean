import Submission.Obl.k4_oss_dyadic_reduction.Basic

open scoped BigOperators

namespace Submission.Obl.k4_oss_dyadic_reduction

lemma prod_abs_le_factor {n : ℕ} (a : Fin n → ℝ) (ha : ∀ j, |a j| ≤ 1) (j : Fin n) :
    (∏ i, |a i|) ≤ |a j| := by
  classical
  simpa using (Finset.prod_le_prod_of_subset_of_le_one₀
    (s := {j}) (t := Finset.univ) (f := fun i => |a i|) (by simp)
    (fun _ _ => abs_nonneg _) (fun i _ _ => ha i))

lemma scale_data {n N : ℕ} (hN : 0 < N) (a : Fin n → ℝ)
    (ha0 : ∀ j, 0 < |a j|) (ha1 : ∀ j, |a j| ≤ 1)
    (haN : ∀ j, 1 / N ≤ |a j|) {r : ℝ} (hr : 0 < r) :
    let δ := r / (∏ j, |a j|)
    0 < δ ∧ δ ≤ r * (N : ℝ) ^ n ∧
      (∀ j, r ≤ |a j| * δ) ∧
      ∀ ξ : ℝ, r⁻¹ ≤ |ξ| → |ξ| ≤ 2 * r⁻¹ →
        δ⁻¹ ≤ |ξ * ∏ j, a j| ∧ |ξ * ∏ j, a j| ≤ 2 * δ⁻¹ := by
  dsimp
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : 0 < ∏ j, |a j| := Finset.prod_pos fun j _ => ha0 j
  have hprod : (1 / (N : ℝ)) ^ n ≤ ∏ j, |a j| := by
    calc
      _ = ∏ _ : Fin n, (1 / (N : ℝ)) := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun j _ => haN j)
  refine ⟨div_pos hr hc, ?_, ?_, ?_⟩
  · calc
      r / (∏ j, |a j|) ≤ r / ((1 / (N : ℝ)) ^ n) :=
        div_le_div_of_nonneg_left hr.le (by positivity) hprod
      _ = r * (N : ℝ) ^ n := by simp [div_eq_mul_inv]
  · intro j
    have hj := prod_abs_le_factor a ha1 j
    have he : r = (∏ j, |a j|) * (r / ∏ j, |a j|) := by field_simp
    calc
      r = (∏ j, |a j|) * (r / ∏ j, |a j|) := he
      _ ≤ _ := mul_le_mul_of_nonneg_right hj (div_nonneg hr.le hc.le)
  · intro ξ hξ1 hξ2
    have habs : |ξ * ∏ j, a j| = |ξ| * ∏ j, |a j| := by
      rw [abs_mul, Finset.abs_prod]
    have hinv : (r / ∏ j, |a j|)⁻¹ = r⁻¹ * ∏ j, |a j| := by
      rw [inv_div, div_eq_mul_inv, mul_comm]
    rw [habs, hinv]
    constructor
    · exact mul_le_mul_of_nonneg_right hξ1 hc.le
    · simpa [mul_assoc] using mul_le_mul_of_nonneg_right hξ2 hc.le

end Submission.Obl.k4_oss_dyadic_reduction
