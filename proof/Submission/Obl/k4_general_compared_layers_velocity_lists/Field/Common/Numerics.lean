-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.Common.Numerics; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
/- Written for obligation o254 (k4_general_parent_wide_layer_candidates), session x0900. -/
import Submission.Obl.k4_general_parent_projected_layers.Support.ParentMass

/-!
# Numerics of the common-field application at one scale

Pure real inequalities, each reduced to the strict eventual inequalities of the main proof:
the fine mesh resolves the slabs of a normalized cell and their motion, the transverse slabs
absorb the shear of the cell, and the subpower loss `H ≤ N^δ` is dominated by the exponents.
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open Submission.Obl.k4_general_parent_projected_layers (parentFilling)

noncomputable section

namespace FieldCommon

/-- The fine mesh resolves a normalized cell of side `N^(-βb)` (in block time `q`). -/
theorem fine_cell_numeric {N K q a βb Mf : ℝ} (hN : 0 < N) (hK : 1 ≤ K)
    (hq : (K * N ^ a)⁻¹ ≤ q) (he : 2 * K ^ 3 * N ^ (-Mf) < N ^ (-a - βb)) :
    (K + K ^ 2) * N ^ (-Mf) ≤ q * N ^ (-βb) := by
  have hK0 : 0 < K := by linarith
  have hNa : 0 < N ^ a := Real.rpow_pos_of_pos hN _
  have hNb : 0 < N ^ (-βb) := Real.rpow_pos_of_pos hN _
  have hNM : 0 < N ^ (-Mf) := Real.rpow_pos_of_pos hN _
  have h1 : N ^ (-a - βb) = (N ^ a)⁻¹ * N ^ (-βb) := by
    rw [sub_eq_add_neg, Real.rpow_add hN, Real.rpow_neg hN.le]
  rw [h1] at he
  have hKq : (N ^ a)⁻¹ ≤ K * q := by
    have : (N ^ a)⁻¹ = K * (K * N ^ a)⁻¹ := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hq hK0.le
  have h2 : (N ^ a)⁻¹ * N ^ (-βb) ≤ K * q * N ^ (-βb) :=
    mul_le_mul_of_nonneg_right hKq hNb.le
  have h3 : K * ((K + K ^ 2) * N ^ (-Mf)) ≤ 2 * K ^ 3 * N ^ (-Mf) := by
    have : K * (K + K ^ 2) ≤ 2 * K ^ 3 := by nlinarith
    nlinarith
  have h4 : K * ((K + K ^ 2) * N ^ (-Mf)) ≤ K * (q * N ^ (-βb)) := by
    nlinarith only [h2, h3, he]
  exact le_of_mul_le_mul_left h4 hK0

/-- The fine mesh resolves a transverse slab of width `N^(-ρU)` (in block width `q g`). -/
theorem fine_slab_numeric {N K q a l ρU Mf : ℝ} (hN : 0 < N) (hK : 1 ≤ K)
    (hq : (K * N ^ a)⁻¹ ≤ q) (he : 2 * K ^ 3 * N ^ (-Mf) < N ^ (-a - l - ρU)) :
    (K + K ^ 2) * N ^ (-Mf) ≤ q * N ^ (-l) * N ^ (-ρU) := by
  have h1 : N ^ (-a - l - ρU) = N ^ (-a - (l + ρU)) := by ring_nf
  have h2 : N ^ (-(l + ρU)) = N ^ (-l) * N ^ (-ρU) := by
    rw [← Real.rpow_add hN]
    ring_nf
  rw [h1] at he
  have := fine_cell_numeric hN hK hq he
  rw [h2] at this
  linarith only [this]

/-- The transverse slabs absorb the shear of a normalized cell. -/
theorem shear_numeric {N K q βb l ρU : ℝ} (hN : 0 < N) (hq : 0 < q)
    (he : 1 * K ^ 1 * N ^ (-βb) < N ^ (-l - ρU)) :
    K * q * N ^ (-βb) ≤ q * N ^ (-l) * N ^ (-ρU) := by
  have h1 : N ^ (-l - ρU) = N ^ (-l) * N ^ (-ρU) := by
    rw [sub_eq_add_neg, Real.rpow_add hN]
  rw [h1, one_mul, pow_one] at he
  have := mul_le_mul_of_nonneg_left he.le hq.le
  linarith only [this]

/-- Powers of a subpower loss. -/
theorem loss_pow_le {N H δ : ℝ} (hN : 0 < N) (hH : 0 ≤ H) (hHN : H ≤ N ^ δ) (n : ℕ) :
    H ^ n ≤ N ^ ((n : ℝ) * δ) := by
  calc H ^ n ≤ (N ^ δ) ^ n := pow_le_pow_left₀ hH hHN n
    _ = N ^ ((n : ℝ) * δ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le, mul_comm]

/-- The subpower loss is dominated by the exponents. -/
theorem loss_numerics {N K H δ η r m l θ ε Lf : ℝ} (hN : 1 ≤ N) (hK : 1 ≤ K) (hKH : K ≤ H)
    (hHN : H ≤ N ^ δ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (e10 : 99 * N ^ (4 * δ) < N ^ η) (e12 : 24 * N ^ (2 * δ) < N ^ r)
    (e13 : 32 * N ^ (4 * δ - m + l * r) < N ^ (-θ)) (e14 : 2 * N ^ (ε / 2) < N ^ ε)
    (hLf : Lf = (parentFilling K (N ^ (-r)))⁻¹) :
    98 * H ^ 4 + 1 ≤ N ^ η ∧ 24 * K * H * Lf ≤ 1 ∧
      32 * H ^ 4 * N ^ (-m) / N ^ (-l * r) ≤ N ^ (-θ) ∧ 1 + N ^ (ε / 2) ≤ N ^ ε := by
  have hN0 : 0 < N := by linarith
  have hH1 : 1 ≤ H := hK.trans hKH
  have hH0 : 0 ≤ H := by linarith
  have hH4 : H ^ 4 ≤ N ^ (4 * δ) := by
    have := loss_pow_le hN0 hH0 hHN 4
    norm_num at this
    exact this
  have hH2 : H ^ 2 ≤ N ^ (2 * δ) := by
    have := loss_pow_le hN0 hH0 hHN 2
    norm_num at this
    exact this
  have hN4 : 1 ≤ N ^ (4 * δ) := Real.one_le_rpow hN (by positivity)
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith only [hH4, hN4, e10]
  · have hpf0 : 0 < parentFilling K (N ^ (-r)) := by
      unfold parentFilling
      have : 0 < N ^ (-r) := Real.rpow_pos_of_pos hN0 _
      have : 0 < K := by linarith
      positivity
    have hpfN : N ^ r ≤ parentFilling K (N ^ (-r)) := by
      unfold parentFilling
      rw [Real.rpow_neg hN0.le, div_inv_eq_mul]
      have h1 : 1 ≤ K ^ 20 := one_le_pow₀ hK
      have hNr : 0 < N ^ r := Real.rpow_pos_of_pos hN0 _
      nlinarith only [h1, hNr]
    rw [hLf, ← div_eq_mul_inv, div_le_one hpf0]
    have hKH2 : K * H ≤ H ^ 2 := by nlinarith only [hKH, hH1]
    nlinarith only [hKH2, hH2, e12, hpfN]
  · have h1 : N ^ (4 * δ) * N ^ (-m) / N ^ (-l * r) = N ^ (4 * δ - m + l * r) := by
      rw [← Real.rpow_add hN0, ← Real.rpow_sub hN0]
      ring_nf
    have hNm : 0 ≤ N ^ (-m) / N ^ (-l * r) := by
      have : 0 < N ^ (-m) := Real.rpow_pos_of_pos hN0 _
      have : 0 < N ^ (-l * r) := Real.rpow_pos_of_pos hN0 _
      positivity
    have h2 : 32 * H ^ 4 * N ^ (-m) / N ^ (-l * r) ≤
        32 * (N ^ (4 * δ) * N ^ (-m) / N ^ (-l * r)) := by
      have := mul_le_mul_of_nonneg_right hH4 hNm
      calc 32 * H ^ 4 * N ^ (-m) / N ^ (-l * r) = 32 * (H ^ 4 * (N ^ (-m) / N ^ (-l * r))) := by
            ring
        _ ≤ 32 * (N ^ (4 * δ) * (N ^ (-m) / N ^ (-l * r))) := by linarith only [this]
        _ = 32 * (N ^ (4 * δ) * N ^ (-m) / N ^ (-l * r)) := by ring
    rw [h1] at h2
    linarith only [h2, e13]
  · have : 1 ≤ N ^ (ε / 2) := Real.one_le_rpow hN (by positivity)
    linarith only [this, e14]

end FieldCommon

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
