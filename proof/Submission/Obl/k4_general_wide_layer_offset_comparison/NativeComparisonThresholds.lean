-- Adapted from this LOT tree, obligation o254, branch x0898, commit 00585850, file Submission/Obl/k4_general_parent_wide_layer_candidates/NativeComparisonThresholds.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
import Mathlib

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

noncomputable section

def nativePruning (M R : ℝ) : ℝ := 8 * M * R

def nativeListParameter (M B R : ℝ) : ℝ := 1 + 14 * B * nativePruning M R

def nativeMatchingBase (M B R C : ℝ) : ℝ :=
  8 * M * (C * (6 * B) * R) + nativeListParameter M B R

def nativeMatchingParameter (M B R C ε : ℝ) : ℝ :=
  M * (nativeMatchingBase M B R C) ^ (1 / ε)

/-- Explicit pruning and matching thresholds charge each comparison
loss by at most one eighth of the original dense mass scale. -/
theorem native_comparison_thresholds {M B R C ε : ℝ}
    (hM : 1 ≤ M) (hB : 0 < B) (hR : 0 < R) (hC : 0 ≤ C)
    (hCM : C ≤ M) (hε : 0 < ε) :
    0 < nativePruning M R ∧
      1 ≤ nativeListParameter M B R ∧
      14 * B * nativePruning M R ≤ nativeListParameter M B R ∧
      1 ≤ nativeMatchingParameter M B R C ε ∧
      C * (nativeListParameter M B R) ^ (1 / ε) ≤ nativeMatchingParameter M B R C ε ∧
      R / nativePruning M R ≤ (8 * M)⁻¹ ∧
      C * (6 * B) * (nativeMatchingParameter M B R C ε) ^ (-ε) * R ≤ (8 * M)⁻¹ := by
  let F := nativePruning M R
  let L := nativeListParameter M B R
  let W := nativeMatchingBase M B R C
  let Λ := nativeMatchingParameter M B R C ε
  have hMp : 0 < M := zero_lt_one.trans_le hM
  have hF : 0 < F := by dsimp [F, nativePruning]; positivity
  have hL1 : 1 ≤ L := by
    change 1 ≤ 1 + 14 * B * F
    nlinarith [mul_nonneg hB.le hF.le]
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hLW : L ≤ W := by
    dsimp [W, nativeMatchingBase]
    exact le_add_of_nonneg_left (by positivity)
  have hW1 : 1 ≤ W := hL1.trans hLW
  have hWp : 0 < W := zero_lt_one.trans_le hW1
  have hεinv : 0 < 1 / ε := one_div_pos.mpr hε
  have hpower : 1 ≤ W ^ (1 / ε) := Real.one_le_rpow hW1 hεinv.le
  have hΛ1 : 1 ≤ Λ := by
    change 1 ≤ M * W ^ (1 / ε)
    simpa only [one_mul] using mul_le_mul hM hpower zero_le_one hMp.le
  have hthreshold : C * L ^ (1 / ε) ≤ Λ :=
    mul_le_mul hCM (Real.rpow_le_rpow hL0.le hLW hεinv.le)
      (Real.rpow_nonneg hL0.le _) hMp.le
  have hΛbase : W ^ (1 / ε) ≤ Λ :=
    le_mul_of_one_le_left (Real.rpow_nonneg hWp.le _) hM
  have hinvPower : (W ^ (1 / ε)) ^ (-ε) = W⁻¹ := by
    rw [← Real.rpow_mul hWp.le, show (1 / ε) * (-ε) = (-1 : ℝ) by field_simp]
    exact Real.rpow_neg_one W
  have hdecay : Λ ^ (-ε) ≤ W⁻¹ := by
    have hh := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hWp _)
      hΛbase (by linarith : -ε ≤ 0)
    rwa [hinvPower] at hh
  have hP : 0 ≤ C * (6 * B) * R := by positivity
  have hratio : (C * (6 * B) * R) / W ≤ (8 * M)⁻¹ := by
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ hWp (by positivity)).mpr
    dsimp [W, nativeMatchingBase]
    nlinarith [hL0]
  refine ⟨hF, hL1, ?_, hΛ1, hthreshold, ?_, ?_⟩
  · dsimp [nativeListParameter]
    linarith
  · have heq : R / nativePruning M R = (8 * M)⁻¹ := by
      dsimp [nativePruning]
      field_simp
    exact heq.le
  · calc
      _ = (C * (6 * B) * R) * Λ ^ (-ε) := by ring
      _ ≤ (C * (6 * B) * R) * W⁻¹ := mul_le_mul_of_nonneg_left hdecay hP
      _ = (C * (6 * B) * R) / W := (div_eq_mul_inv _ _).symm
      _ ≤ _ := hratio

theorem retained_native_comparison_mass {M c₁ c₂ : ℝ} {before after : ENNReal}
    (hM : 0 < M) (hbefore : ENNReal.ofReal ((2 * M)⁻¹) ≤ before)
    (hbudget : before ≤ after + ENNReal.ofReal c₁ + ENNReal.ofReal c₂)
    (h₁ : c₁ ≤ (8 * M)⁻¹) (h₂ : c₂ ≤ (8 * M)⁻¹) :
    ENNReal.ofReal ((4 * M)⁻¹) ≤ after := by
  have heq₈ : ENNReal.ofReal ((8 * M)⁻¹) + ENNReal.ofReal ((8 * M)⁻¹) =
      ENNReal.ofReal ((4 * M)⁻¹) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    field_simp
    ring
  have heq₄ : ENNReal.ofReal ((4 * M)⁻¹) + ENNReal.ofReal ((4 * M)⁻¹) =
      ENNReal.ofReal ((2 * M)⁻¹) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    field_simp
    ring
  have hb := hbudget.trans (add_le_add
    (add_le_add le_rfl (ENNReal.ofReal_le_ofReal h₁)) (ENNReal.ofReal_le_ofReal h₂))
  rw [add_assoc, heq₈] at hb
  have hh : ENNReal.ofReal ((4 * M)⁻¹) + ENNReal.ofReal ((4 * M)⁻¹) ≤
      after + ENNReal.ofReal ((4 * M)⁻¹) := by
    rw [heq₄]
    exact hbefore.trans hb
  exact ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top hh

end
end Submission.Obl.k4_general_wide_layer_offset_comparison
