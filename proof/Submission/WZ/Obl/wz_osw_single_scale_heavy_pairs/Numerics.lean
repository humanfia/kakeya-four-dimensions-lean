-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs.Numerics.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

/-!
# Numerics for the choice of the exponent `M`
-/

namespace WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs

/-- For large `u`, `(A * X ^ (-u)) ^ a ≤ Q * X⁻¹` for every `X ≥ 2`. -/
lemma exists_large_exp {A Q a : ℝ} (hA : 0 < A) (hQ : 0 < Q) (ha : 0 < a) :
    ∃ u₀ : ℝ, 0 ≤ u₀ ∧ ∀ u : ℝ, u₀ ≤ u → ∀ X : ℝ, 2 ≤ X →
      (A * X ^ (-u)) ^ a ≤ Q * X⁻¹ := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (A ^ a / Q) (by norm_num : (1 : ℝ) < 2)
  refine ⟨(n + 1) / a, by positivity, ?_⟩
  intro u hu X hX
  have hX0 : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hua : (n : ℝ) + 1 ≤ u * a := by
    have := mul_le_mul_of_nonneg_right hu ha.le
    rwa [div_mul_cancel₀ _ ha.ne'] at this
  -- X ^ (u * a - 1) ≥ 2 ^ n > A ^ a / Q
  have h2n : (2 : ℝ) ^ (n : ℝ) ≤ X ^ (u * a - 1) := by
    calc (2 : ℝ) ^ (n : ℝ) ≤ X ^ (n : ℝ) :=
          Real.rpow_le_rpow (by norm_num) hX (Nat.cast_nonneg n)
      _ ≤ X ^ (u * a - 1) := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  rw [Real.rpow_natCast] at h2n
  have hkey : A ^ a / Q < X ^ (u * a - 1) := lt_of_lt_of_le hn h2n
  rw [div_lt_iff₀ hQ] at hkey
  have hXu : (A * X ^ (-u)) ^ a = A ^ a * X ^ (-(u * a)) := by
    rw [Real.mul_rpow hA.le (Real.rpow_nonneg hX0.le _), ← Real.rpow_mul hX0.le]
    ring_nf
  rw [hXu]
  have hsplit : X ^ (-(u * a)) = (X ^ (u * a - 1))⁻¹ * X⁻¹ := by
    rw [show -(u * a) = -(u * a - 1) + (-1 : ℝ) by ring, Real.rpow_add hX0, Real.rpow_neg hX0.le,
      Real.rpow_neg_one]
  rw [hsplit]
  have hpos : 0 < X ^ (u * a - 1) := Real.rpow_pos_of_pos hX0 _
  have : A ^ a * (X ^ (u * a - 1))⁻¹ ≤ Q := by
    rw [← div_eq_mul_inv, div_le_iff₀ hpos]
    linarith
  have hXinv : 0 ≤ X⁻¹ := inv_nonneg.mpr hX0.le
  calc A ^ a * ((X ^ (u * a - 1))⁻¹ * X⁻¹) = (A ^ a * (X ^ (u * a - 1))⁻¹) * X⁻¹ := by ring
    _ ≤ Q * X⁻¹ := mul_le_mul_of_nonneg_right this hXinv

/-- Geometric sums of dyadic scales. -/
lemma sum_dyad_rpow_le {δ θ : ℝ} (hδ : 0 < δ) (hθ : 0 < θ) (N : ℕ) :
    ∑ j ∈ Finset.range N, (2 * (2 ^ j * δ)) ^ θ ≤ (2 * (2 ^ N * δ)) ^ θ / (2 ^ θ - 1) := by
  have hq : (1 : ℝ) < 2 ^ θ := Real.one_lt_rpow (by norm_num) hθ
  have hterm : ∀ j : ℕ, (2 * (2 ^ j * δ)) ^ θ = (2 * δ) ^ θ * (2 ^ θ) ^ j := by
    intro j
    rw [show 2 * (2 ^ j * δ) = (2 * δ) * 2 ^ j by ring,
      Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_mul (by norm_num), mul_comm]
  simp_rw [hterm]
  rw [← Finset.mul_sum, geom_sum_eq hq.ne' N]
  have hq1 : 0 < (2 : ℝ) ^ θ - 1 := by linarith
  rw [mul_div_assoc']
  apply div_le_div_of_nonneg_right _ hq1.le
  have h0 : 0 ≤ (2 * δ) ^ θ := by positivity
  nlinarith [pow_pos (show (0:ℝ) < 2 ^ θ by linarith) N]

end WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs
