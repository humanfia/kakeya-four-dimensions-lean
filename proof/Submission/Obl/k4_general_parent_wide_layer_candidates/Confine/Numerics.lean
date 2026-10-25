import Submission.Obl.k4_general_parent_projected_layers.Support.ParentMass

/-!
# Numerics of deep confinement

The three scale inequalities of deep native-signal confinement at one fixed `k`, each
reduced to one strict inequality of the form `A * K ^ p * N ^ a < N ^ b` (which holds
eventually by `eventually_subpower_mul_rpow_lt` of accepted o213):

* the physical mesh `N ^ (-((J + κ + ℓ) s + 1))` resolves the normalized packet of every
  true block at depth `s` at the scale `parentFilling ^ (-J)`;
* the loss `K * parentFilling⁻¹` at depth `s` is at most `N ^ (-ε) / 4`;
* the oscillation bound of the two groups at depth `s`, on a deep label at depth `t`, is at
  most `N ^ (-w) / 2`.
-/

namespace Submission.Obl.k4_general_parent_wide_layer_candidates

open Submission.Obl.k4_general_parent_projected_layers

noncomputable section

theorem parentFilling_rpow_eq {N K s : ℝ} (hN : 0 < N) (C : ℕ) :
    parentFilling K (N ^ (-s)) ^ C = 3000000 ^ C * K ^ (20 * C) * N ^ ((C : ℝ) * s) := by
  have hpf : parentFilling K (N ^ (-s)) = 3000000 * K ^ 20 * N ^ s := by
    unfold parentFilling
    rw [Real.rpow_neg hN.le, div_inv_eq_mul]
  rw [hpf, mul_pow, mul_pow, ← pow_mul, ← Real.rpow_mul_natCast hN.le, mul_comm s]

theorem parentFilling_pos {N K s : ℝ} (hN : 0 < N) (hK : 1 ≤ K) :
    0 < parentFilling K (N ^ (-s)) := by
  unfold parentFilling
  have : 0 < N ^ (-s) := Real.rpow_pos_of_pos hN _
  have : 0 < K := by linarith
  positivity

/-- The physical mesh resolves every normalized packet at depth `s`. -/
theorem resolution_numeric {N K Q κ ℓ s : ℝ} {J : ℕ} (hN : 0 < N) (hK : 1 ≤ K)
    (hQ0 : 0 < Q) (hQ : Q ≤ K * N ^ (κ * s))
    (h4 : 3000000 ^ J * K ^ (20 * J + 1) * N ^ (-1 : ℝ) < N ^ (0 : ℝ)) :
    N ^ (-(((J : ℝ) + κ + ℓ) * s + 1)) / (Q⁻¹ * N ^ (-ℓ * s)) ≤
      (parentFilling K (N ^ (-s)) ^ J)⁻¹ := by
  have hK0 : 0 < K := by linarith
  rw [parentFilling_rpow_eq hN J]
  have hA : 0 < (3000000 : ℝ) ^ J * K ^ (20 * J) := by positivity
  have hNJ : 0 < N ^ ((J : ℝ) * s) := Real.rpow_pos_of_pos hN _
  have hNl : 0 < N ^ (ℓ * s) := Real.rpow_pos_of_pos hN _
  have hNk : 0 < N ^ (κ * s) := Real.rpow_pos_of_pos hN _
  have hN1 : 0 < N ^ (-1 : ℝ) := Real.rpow_pos_of_pos hN _
  have h4' : 3000000 ^ J * K ^ (20 * J + 1) * N ^ (-1 : ℝ) ≤ 1 := by
    rw [Real.rpow_zero] at h4
    exact h4.le
  -- rewrite the left side as a product of powers
  have hsplit : N ^ (-(((J : ℝ) + κ + ℓ) * s + 1)) =
      N ^ (-1 : ℝ) * (N ^ ((J : ℝ) * s))⁻¹ * (N ^ (κ * s))⁻¹ * (N ^ (ℓ * s))⁻¹ := by
    rw [← Real.rpow_neg hN.le, ← Real.rpow_neg hN.le, ← Real.rpow_neg hN.le,
      ← Real.rpow_add hN, ← Real.rpow_add hN, ← Real.rpow_add hN]
    congr 1
    ring
  have hg : N ^ (-ℓ * s) = (N ^ (ℓ * s))⁻¹ := by rw [neg_mul, Real.rpow_neg hN.le]
  rw [hsplit, hg]
  have hlhs : N ^ (-1 : ℝ) * (N ^ ((J : ℝ) * s))⁻¹ * (N ^ (κ * s))⁻¹ * (N ^ (ℓ * s))⁻¹ /
      (Q⁻¹ * (N ^ (ℓ * s))⁻¹) =
      N ^ (-1 : ℝ) * (N ^ ((J : ℝ) * s))⁻¹ * (N ^ (κ * s))⁻¹ * Q := by
    field_simp
  rw [hlhs]
  have hQ' : (N ^ (κ * s))⁻¹ * Q ≤ K := by
    rw [inv_mul_le_iff₀ hNk]
    linarith
  have hstep : N ^ (-1 : ℝ) * (N ^ ((J : ℝ) * s))⁻¹ * (N ^ (κ * s))⁻¹ * Q ≤
      N ^ (-1 : ℝ) * (N ^ ((J : ℝ) * s))⁻¹ * K := by
    rw [mul_assoc (N ^ (-1 : ℝ) * (N ^ ((J : ℝ) * s))⁻¹)]
    exact mul_le_mul_of_nonneg_left hQ' (by positivity)
  refine hstep.trans ?_
  have hrhs : (3000000 ^ J * K ^ (20 * J) * N ^ ((J : ℝ) * s))⁻¹ =
      (N ^ ((J : ℝ) * s))⁻¹ * (3000000 ^ J * K ^ (20 * J))⁻¹ := by
    rw [mul_inv, mul_comm]
  rw [hrhs]
  have hkey : N ^ (-1 : ℝ) * K ≤ (3000000 ^ J * K ^ (20 * J))⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hA]
    calc N ^ (-1 : ℝ) * K * (3000000 ^ J * K ^ (20 * J)) =
        3000000 ^ J * K ^ (20 * J + 1) * N ^ (-1 : ℝ) := by ring
      _ ≤ 1 := h4'
  calc N ^ (-1 : ℝ) * (N ^ ((J : ℝ) * s))⁻¹ * K =
      (N ^ ((J : ℝ) * s))⁻¹ * (N ^ (-1 : ℝ) * K) := by ring
    _ ≤ (N ^ ((J : ℝ) * s))⁻¹ * (3000000 ^ J * K ^ (20 * J))⁻¹ :=
      mul_le_mul_of_nonneg_left hkey (by positivity)

/-- The loss of the two groups at depth `s` is at most `N ^ (-ε) / 4`. -/
theorem loss_numeric {N K s w ε : ℝ} (hN1 : 1 ≤ N) (hK : 1 ≤ K) (hεw : ε ≤ w)
    (h3 : 4 * N ^ (-s) < N ^ (-w)) :
    ENNReal.ofReal K * ENNReal.ofReal ((parentFilling K (N ^ (-s)))⁻¹) ≤
      ENNReal.ofReal (N ^ (-ε) / 4) := by
  have hN : 0 < N := by linarith
  have hK0 : 0 < K := by linarith
  rw [← ENNReal.ofReal_mul hK0.le]
  apply ENNReal.ofReal_le_ofReal
  have hNs : 0 < N ^ (-s) := Real.rpow_pos_of_pos hN _
  have hpf : (parentFilling K (N ^ (-s)))⁻¹ = N ^ (-s) / (3000000 * K ^ 20) := by
    unfold parentFilling
    rw [inv_div]
  rw [hpf]
  have hK20 : K ≤ 3000000 * K ^ 20 := by
    have : 1 ≤ K ^ 19 := one_le_pow₀ hK
    nlinarith
  have h1 : K * (N ^ (-s) / (3000000 * K ^ 20)) ≤ N ^ (-s) := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hK20 hNs.le]
  have h2 : N ^ (-w) ≤ N ^ (-ε) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  linarith

/-- The oscillation bound of the two groups at depth `s`, on a deep label of depth `t`. -/
theorem osc_numeric {N K Q Qt κ ℓ s t w : ℝ} {C : ℕ} (hN : 0 < N) (hK : 1 ≤ K)
    (hQ0 : 0 < Q) (hQ : Q ≤ K * N ^ (κ * s)) (hQt : N ^ (κ * t) / K ≤ Qt)
    (h1 : 2 ^ 17 * K ^ 14 * N ^ (-s) < N ^ (-w))
    (h2 : 288 * 3000000 ^ C * K ^ (20 * C + 6) * N ^ (((C : ℝ) + κ + ℓ) * s - κ * t) <
      N ^ (-w)) :
    2 * (2 * K) ^ 14 * N ^ (-s) +
        parentFilling K (N ^ (-s)) ^ C *
          (12 * K ^ 2 * (6 * K ^ 2 * Qt⁻¹) / (Q⁻¹ * N ^ (-ℓ * s))) ≤
      N ^ (-w) / 2 := by
  have hK0 : 0 < K := by linarith
  have hNkt : 0 < N ^ (κ * t) := Real.rpow_pos_of_pos hN _
  have hQt0 : 0 < Qt := lt_of_lt_of_le (by positivity) hQt
  have hNs : 0 < N ^ (-s) := Real.rpow_pos_of_pos hN _
  -- the first term
  have hterm1 : 2 * (2 * K) ^ 14 * N ^ (-s) ≤ N ^ (-w) / 4 := by
    have he : 2 * (2 * K) ^ 14 * N ^ (-s) = (2 ^ 17 * K ^ 14 * N ^ (-s)) / 4 := by ring
    rw [he]
    linarith
  -- the second term
  have hQtinv : Qt⁻¹ ≤ K * N ^ (-(κ * t)) := by
    have h := inv_anti₀ (by positivity) hQt
    rw [inv_div, Real.rpow_neg hN.le] at *
    calc Qt⁻¹ ≤ K / N ^ (κ * t) := h
      _ = K * (N ^ (κ * t))⁻¹ := div_eq_mul_inv _ _
  have hfrac : 12 * K ^ 2 * (6 * K ^ 2 * Qt⁻¹) / (Q⁻¹ * N ^ (-ℓ * s)) =
      72 * K ^ 4 * Q * Qt⁻¹ * N ^ (ℓ * s) := by
    rw [neg_mul, Real.rpow_neg hN.le]
    have hNl : 0 < N ^ (ℓ * s) := Real.rpow_pos_of_pos hN _
    field_simp
    ring
  have hNls : 0 < N ^ (ℓ * s) := Real.rpow_pos_of_pos hN _
  have hNCs : 0 < N ^ ((C : ℝ) * s) := Real.rpow_pos_of_pos hN _
  have hpow : N ^ ((C : ℝ) * s) * N ^ (κ * s) * N ^ (-(κ * t)) * N ^ (ℓ * s) =
      N ^ (((C : ℝ) + κ + ℓ) * s - κ * t) := by
    rw [← Real.rpow_add hN, ← Real.rpow_add hN, ← Real.rpow_add hN]
    congr 1
    ring
  have hterm2 : parentFilling K (N ^ (-s)) ^ C *
      (12 * K ^ 2 * (6 * K ^ 2 * Qt⁻¹) / (Q⁻¹ * N ^ (-ℓ * s))) ≤ N ^ (-w) / 4 := by
    rw [parentFilling_rpow_eq hN C, hfrac]
    calc 3000000 ^ C * K ^ (20 * C) * N ^ ((C : ℝ) * s) *
          (72 * K ^ 4 * Q * Qt⁻¹ * N ^ (ℓ * s)) ≤
        3000000 ^ C * K ^ (20 * C) * N ^ ((C : ℝ) * s) *
          (72 * K ^ 4 * (K * N ^ (κ * s)) * (K * N ^ (-(κ * t))) * N ^ (ℓ * s)) := by
          gcongr
      _ = 72 * 3000000 ^ C * K ^ (20 * C + 6) *
          (N ^ ((C : ℝ) * s) * N ^ (κ * s) * N ^ (-(κ * t)) * N ^ (ℓ * s)) := by ring
      _ = 72 * 3000000 ^ C * K ^ (20 * C + 6) * N ^ (((C : ℝ) + κ + ℓ) * s - κ * t) := by
          rw [hpow]
      _ ≤ N ^ (-w) / 4 := by linarith
  linarith

end

end Submission.Obl.k4_general_parent_wide_layer_candidates
