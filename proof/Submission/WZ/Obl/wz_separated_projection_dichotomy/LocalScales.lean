-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.LocalScales.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.LocalizationBudget

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

theorem rpow_multiple_nat {δ : ℝ} (hδ : 0 ≤ δ) (η : ℝ) (n : ℕ) :
    δ ^ ((n : ℝ) * η) = (δ ^ η) ^ n := by
  rw [mul_comm, Real.rpow_mul hδ, Real.rpow_natCast]

theorem local_density_identity {δ η : ℝ} (hδ : 0 < δ) :
    (δ ^ (4 * η) / (75 : ℝ) ^ 3) / (2 * (25 / (δ ^ (12 * η)) ^ 2) ^ 3) =
      δ ^ (76 * η) / ((75 : ℝ) ^ 3 * (2 * (25 : ℝ) ^ 3)) := by
  have hp := Real.rpow_pos_of_pos hδ η
  have h4 := rpow_multiple_nat hδ.le η 4
  have h12 := rpow_multiple_nat hδ.le η 12
  have h76 := rpow_multiple_nat hδ.le η 76
  norm_num only [Nat.cast_ofNat] at h4 h12 h76
  rw [h4, h12, h76]
  field_simp

theorem LocalizationBudget.degeneracy_bound {δ η ε θ : ℝ}
    (h : LocalizationBudget δ η ε θ) :
    4 * (225 * δ ^ (-4 * η)) * δ ^ (10 * η) ≤ δ ^ (4 * η) / (75 : ℝ) ^ 3 := by
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < (75 : ℝ) ^ 3)).mpr
  have hid : δ ^ (-4 * η) * δ ^ (10 * η) = δ ^ (2 * η) * δ ^ (4 * η) := by
    rw [← Real.rpow_add h.delta_pos, ← Real.rpow_add h.delta_pos]
    congr 1
    ring
  calc 4 * (225 * δ ^ (-4 * η)) * δ ^ (10 * η) * (75 : ℝ) ^ 3 =
        (900 * (75 : ℝ) ^ 3) * (δ ^ (-4 * η) * δ ^ (10 * η)) := by ring
    _ = ((900 * (75 : ℝ) ^ 3) * δ ^ (2 * η)) * δ ^ (4 * η) := by rw [hid]; ring
    _ ≤ 1 * δ ^ (4 * η) :=
      mul_le_mul_of_nonneg_right h.remove_degeneracies (Real.rpow_nonneg h.delta_pos.le _)
    _ = _ := one_mul _

theorem LocalizationBudget.retained_density {δ η ε θ : ℝ}
    (h : LocalizationBudget δ η ε θ) :
    δ ^ (80 * η) ≤
      (δ ^ (4 * η) / (75 : ℝ) ^ 3) / (2 * (25 / (δ ^ (12 * η)) ^ 2) ^ 3) := by
  rw [local_density_identity h.delta_pos]
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < (75 : ℝ) ^ 3 * (2 * (25 : ℝ) ^ 3))).mpr
  have hid : δ ^ (80 * η) = δ ^ (4 * η) * δ ^ (76 * η) := by
    rw [← Real.rpow_add h.delta_pos]
    congr 1
    ring
  rw [hid]
  nlinarith [mul_le_mul_of_nonneg_right h.density_reserve
    (Real.rpow_nonneg h.delta_pos.le (76 * η))]

theorem LocalizationBudget.refined_frostman_bound {δ η ε θ : ℝ}
    (h : LocalizationBudget δ η ε θ) :
    2 * ((225 * δ ^ (-4 * η)) / δ ^ (80 * η)) ≤ δ ^ (-θ) := by
  have hid : 2 * ((225 * δ ^ (-4 * η)) / δ ^ (80 * η)) = 450 * δ ^ (-84 * η) := by
    rw [mul_div_assoc, ← mul_assoc, ← mul_div_assoc]
    norm_num
    rw [mul_div_assoc, ← Real.rpow_sub h.delta_pos]
    congr 2
    ring
  exact hid ▸ h.frostman_reserve

theorem LocalizationBudget.zoom_bound {δ η ε θ : ℝ}
    (h : LocalizationBudget δ η ε θ) :
    16 / (δ ^ (10 * η)) ^ 2 ≤ δ ^ (-24 * η) := by
  have hpow : (δ ^ (10 * η)) ^ 2 = δ ^ (20 * η) := by
    have hh := Real.rpow_mul h.delta_pos.le (10 * η) (2 : ℝ)
    norm_num at hh
    convert hh.symm using 1 <;> congr 1 <;> ring
  rw [hpow]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos h.delta_pos _)).mpr
  rw [← Real.rpow_add h.delta_pos, show -24 * η + 20 * η = -(4 * η) by ring,
    Real.rpow_neg h.delta_pos.le, inv_eq_one_div]
  exact (le_div_iff₀ (Real.rpow_pos_of_pos h.delta_pos _)).mpr h.zoom_reserve

theorem LocalizationBudget.length_bound {δ η ε θ : ℝ}
    (h : LocalizationBudget δ η ε θ) (hηθ : 25 * η ≤ θ) :
    δ ^ (-24 * η) * δ ^ (-η) ≤ δ ^ (-θ) := by
  rw [← Real.rpow_add h.delta_pos]
  exact Real.rpow_le_rpow_of_exponent_ge h.delta_pos h.delta_le_one (by linarith)

theorem LocalizationBudget.projection_bound {δ η ε θ : ℝ}
    (h : LocalizationBudget δ η ε θ) :
    3 * δ ^ (-24 * η) ≤ (δ ^ (-θ)) ^ ((ε / 2) / 2) := by
  rw [← Real.rpow_mul h.delta_pos.le]
  convert h.projection_reserve using 2 <;> ring

theorem LocalizationBudget.line_bound {δ η ε θ : ℝ}
    (h : LocalizationBudget δ η ε θ) {k : ℝ} (hk : 0 < k)
    (hkmax : k ^ 2 ≤ δ ^ (-24 * η)) :
    δ ^ (ε - 1) ≤ δ ^ (ε / 4 - 1) / (9 * k ^ 2) := by
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 9 * k ^ 2)).mpr
  calc δ ^ (ε - 1) * (9 * k ^ 2) ≤ δ ^ (ε - 1) * (9 * δ ^ (-24 * η)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hkmax (by norm_num))
        (Real.rpow_nonneg h.delta_pos.le _)
    _ = 9 * (δ ^ (ε - 1) * δ ^ (-24 * η)) := by ring
    _ = 9 * δ ^ (ε - 24 * η - 1) := by
      rw [← Real.rpow_add h.delta_pos]
      congr 2
      ring
    _ ≤ δ ^ (ε / 4 - 1) := h.line_reserve

end WangZahlLot.Obl.wz_separated_projection_dichotomy
