import Mathlib

/-!
# Dyadic sums for the collision bound

With plank caps `A w min(1, w/w₁)` at the dyadic widths `w_i = 2^(i+1) ε`, `ε = w₁/2^s`,
the weighted dyadic sum of the collision bound is at most `8 q A ε (k + 3)` when the
sum runs up to `i = s + k`: the scales below `w₁` form a convergent geometric series and
each scale above contributes `8 q A ε`.
-/

namespace Submission.Obl.k4_scalar_initial_true_horizon

open scoped ENNReal

/-- `∑_{i<s} 2^(i+1)/2^s ≤ 2`. -/
theorem geom_head_le (s : ℕ) : ∑ i ∈ Finset.range s, (2 : ℝ) ^ (i + 1) / 2 ^ s ≤ 2 := by
  have h : ∑ i ∈ Finset.range s, (2 : ℝ) ^ (i + 1) = 2 ^ (s + 1) - 2 := by
    induction s with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; ring
  rw [← Finset.sum_div, h, div_le_iff₀ (by positivity)]
  have : (2 : ℝ) ^ (s + 1) = 2 * 2 ^ s := by ring
  linarith

/-- The terms `min (1, 2^(i+1)/2^s)` summed over `i ≤ s + k` are at most `k + 3`. -/
theorem sum_min_dyadic_le (s k : ℕ) :
    ∑ i ∈ Finset.range (s + k + 1), min (1 : ℝ) ((2 : ℝ) ^ (i + 1) / 2 ^ s) ≤ k + 3 := by
  have hsplit : Finset.range (s + k + 1) = Finset.range s ∪ Finset.Ico s (s + k + 1) := by
    ext i; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
  rw [hsplit, Finset.sum_union (Finset.disjoint_left.mpr fun i hi hi' => by
    simp only [Finset.mem_range, Finset.mem_Ico] at hi hi'; omega)]
  have h1 : ∑ i ∈ Finset.range s, min (1 : ℝ) ((2 : ℝ) ^ (i + 1) / 2 ^ s) ≤ 2 :=
    (Finset.sum_le_sum fun i _ => min_le_right _ _).trans (geom_head_le s)
  have h2 : ∑ i ∈ Finset.Ico s (s + k + 1), min (1 : ℝ) ((2 : ℝ) ^ (i + 1) / 2 ^ s) ≤ k + 1 := by
    calc ∑ i ∈ Finset.Ico s (s + k + 1), min (1 : ℝ) ((2 : ℝ) ^ (i + 1) / 2 ^ s)
        ≤ ∑ _i ∈ Finset.Ico s (s + k + 1), (1 : ℝ) := Finset.sum_le_sum fun i _ => min_le_left _ _
      _ = k + 1 := by
          simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
          rw [show s + k + 1 - s = k + 1 by omega]; push_cast; ring
  linarith

/-- **The dyadic collision sum.** -/
theorem dyadic_collision_sum_le {q A w₁ : ℝ} (hq : 0 ≤ q) (hA : 0 ≤ A) (hw₁ : 0 < w₁)
    (s k : ℕ) :
    ∑ i ∈ Finset.range (s + k + 1), ENNReal.ofReal (4 * q / 2 ^ i) *
        ENNReal.ofReal (A * (2 ^ (i + 1) * (w₁ / 2 ^ s)) *
          min 1 (2 ^ (i + 1) * (w₁ / 2 ^ s) / w₁)) ≤
      ENNReal.ofReal (8 * q * A * (w₁ / 2 ^ s) * (k + 3)) := by
  have hmul : ∀ i ∈ Finset.range (s + k + 1), ENNReal.ofReal (4 * q / 2 ^ i) *
        ENNReal.ofReal (A * (2 ^ (i + 1) * (w₁ / 2 ^ s)) *
          min 1 (2 ^ (i + 1) * (w₁ / 2 ^ s) / w₁)) =
      ENNReal.ofReal ((4 * q / 2 ^ i) * (A * (2 ^ (i + 1) * (w₁ / 2 ^ s)) *
          min 1 (2 ^ (i + 1) * (w₁ / 2 ^ s) / w₁))) := by
    intro i _
    exact (ENNReal.ofReal_mul (p := 4 * q / 2 ^ i) (by positivity)).symm
  rw [Finset.sum_congr rfl hmul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => by
    apply mul_nonneg (by positivity)
    apply mul_nonneg (by positivity)
    exact le_min zero_le_one (by positivity))]
  · apply ENNReal.ofReal_le_ofReal
    have hterm : ∀ i ∈ Finset.range (s + k + 1),
        (4 * q / 2 ^ i) * (A * (2 ^ (i + 1) * (w₁ / 2 ^ s)) *
          min 1 (2 ^ (i + 1) * (w₁ / 2 ^ s) / w₁)) =
        8 * q * A * (w₁ / 2 ^ s) * min (1 : ℝ) ((2 : ℝ) ^ (i + 1) / 2 ^ s) := by
      intro i _
      have : 2 ^ (i + 1) * (w₁ / 2 ^ s) / w₁ = (2 : ℝ) ^ (i + 1) / 2 ^ s := by
        field_simp
      rw [this]
      field_simp
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left (sum_min_dyadic_le s k)
    positivity

end Submission.Obl.k4_scalar_initial_true_horizon
