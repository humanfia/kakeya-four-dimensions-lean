-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonconcentrated_dot_products.PowerBudget.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_nonconcentrated_dot_products

/-- Any fixed constant can be absorbed by a positive power reserve at a
sufficiently small, explicitly positive scale. -/
theorem exists_power_bound (C : ℝ) {s : ℝ} (hs : 0 < s) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → C ≤ δ ^ (-s) := by
  by_cases hC : C ≤ 1
  · refine ⟨1, zero_lt_one, le_rfl, ?_⟩
    intro δ hδ hδ1
    exact hC.trans (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith))
  have hCpos : 0 < C := zero_lt_one.trans (lt_of_not_ge hC)
  let d : ℝ := (C⁻¹) ^ s⁻¹
  have hd : 0 < d := Real.rpow_pos_of_pos (inv_pos.mpr hCpos) _
  refine ⟨min 1 d, lt_min zero_lt_one hd, min_le_left _ _, ?_⟩
  intro δ hδ hδ₀
  have hp : δ ^ s ≤ C⁻¹ := by
    calc δ ^ s ≤ d ^ s :=
        Real.rpow_le_rpow hδ.le (hδ₀.trans (min_le_right _ _)) hs.le
      _ = C⁻¹ := Real.rpow_inv_rpow (inv_nonneg.mpr hCpos.le) hs.ne'
  rw [Real.rpow_neg hδ.le, inv_eq_one_div]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hδ s)).mpr
  calc C * δ ^ s ≤ C * C⁻¹ := mul_le_mul_of_nonneg_left hp hCpos.le
    _ = 1 := mul_inv_cancel₀ hCpos.ne'

theorem exists_monomial_bound (C : ℝ) {a b : ℝ} (hab : b < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → C * δ ^ a ≤ δ ^ b := by
  obtain ⟨δ₀, hδ₀, hδ₀1, hbound⟩ := exists_power_bound C (sub_pos.mpr hab)
  refine ⟨δ₀, hδ₀, hδ₀1, ?_⟩
  intro δ hδ hδsmall
  calc C * δ ^ a ≤ δ ^ (-(a - b)) * δ ^ a :=
      mul_le_mul_of_nonneg_right (hbound δ hδ hδsmall) (Real.rpow_nonneg hδ.le _)
    _ = δ ^ b := by rw [← Real.rpow_add hδ]; congr 1; ring

end WangZahlLot.Obl.wz_nonconcentrated_dot_products
