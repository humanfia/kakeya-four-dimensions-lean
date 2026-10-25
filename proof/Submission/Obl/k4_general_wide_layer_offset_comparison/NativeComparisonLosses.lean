-- Adapted from this LOT tree, obligation o254, branch x0898, commit 00585850, file Submission/Obl/k4_general_parent_wide_layer_candidates/NativeComparisonLosses.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
import Submission.Obl.k4_general_wide_layer_offset_comparison.ActualNativeComparisonAt
import Submission.Obl.k4_general_wide_layer_offset_comparison.NativeComparisonThresholds
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.Subpower

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open Filter
open Native.SheetComparison
open Submission.Obl.k4_contact_affine_residual_candidate_transfer

noncomputable section

def nativeReference (M H d : ℝ) : ℝ :=
  (8 * nativeSheetLoss M) ^ d * (475200 * M ^ 5 + 360 * H ^ 4 * M)

def nativeFinalListLoss (M H d ε C : ℝ) : ℝ :=
  let V := nativeSheetLoss M
  let B := commonNativeCapConstant M
  let R := nativeReference M H d
  let L := nativeListParameter M B R
  let Λ := nativeMatchingParameter M B R C ε
  4 * M + (1320 * M ^ 2 * (10000 * V) ^ 2 * 2 + 84 * (10000 * V) ^ 2) *
    (L * Λ ^ d) + 2

theorem nativeReference_pos {M H d : ℝ} (hM : 0 < M) : 0 < nativeReference M H d := by
  unfold nativeReference nativeSheetLoss
  positivity

theorem nativeFinalListLoss_bounds {M H d ε C : ℝ}
    (hM : 1 ≤ M) (hC : 0 ≤ C) (hCM : C ≤ M) (hε : 0 < ε) :
    let V := nativeSheetLoss M
    let B := commonNativeCapConstant M
    let R := nativeReference M H d
    let L := nativeListParameter M B R
    let Λ := nativeMatchingParameter M B R C ε
    4 * M ≤ nativeFinalListLoss M H d ε C ∧
      (1320 * M ^ 2 * (10000 * V) ^ 2) * (2 * (L * Λ ^ d)) ≤
        nativeFinalListLoss M H d ε C ∧
      (84 * (10000 * V) ^ 2) * (L * Λ ^ d) ≤ nativeFinalListLoss M H d ε C := by
  intro V B R L Λ
  have hMp : 0 < M := zero_lt_one.trans_le hM
  have hB : 0 < B := by dsimp [B, commonNativeCapConstant]; positivity
  have hR : 0 < R := nativeReference_pos hMp
  have hh := native_comparison_thresholds hM hB hR hC hCM hε
  have hL : 0 ≤ L := zero_le_one.trans hh.2.1
  have hΛ : 0 ≤ Λ := zero_le_one.trans hh.2.2.2.1
  have hpair : 0 ≤ L * Λ ^ d := mul_nonneg hL (Real.rpow_nonneg hΛ _)
  have hA : 0 ≤ 1320 * M ^ 2 * (10000 * V) ^ 2 := by positivity
  have hD : 0 ≤ 84 * (10000 * V) ^ 2 := by positivity
  dsimp [nativeFinalListLoss]
  change 4 * M ≤ 4 * M + (1320 * M ^ 2 * (10000 * V) ^ 2 * 2 +
      84 * (10000 * V) ^ 2) * (L * Λ ^ d) + 2 ∧ _ ∧ _
  constructor
  · nlinarith [mul_nonneg hA hpair, mul_nonneg hD hpair]
  constructor <;> nlinarith [mul_nonneg hA hpair, mul_nonneg hD hpair]

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

theorem commonComparisonReference_native {M : ℕ → ℝ} {k : ℕ} {s H : ℝ}
    (hN : 0 < p.N k) :
    commonComparisonReference (p.withLoss M).toParams k s H
      (p.nativeComparisonTolerance M k s) = nativeReference (M k) H p.d := by
  dsimp [commonComparisonReference, nativeReference, nativeComparisonTolerance,
    Submission.Obl.k4_general_parent_projected_layers.PreparedModel.width, toParams, Parent.withLoss]
  rw [mul_div_cancel_right₀ _ (Real.rpow_pos_of_pos hN _).ne']

theorem nativeComparisonTime_ratio {M : ℕ → ℝ} {k : ℕ} {s : ℝ} :
    p.toModel.q k s / p.nativeComparisonTime M k s = 10000 * nativeSheetLoss (M k) := by
  have hQ : p.toModel.q k s ≠ 0 := by
    unfold Submission.Obl.k4_general_parent_projected_layers.PreparedModel.q
    positivity
  dsimp [nativeComparisonTime]
  rw [div_div_eq_mul_div, mul_div_cancel_left₀ _ hQ]

end Parent

/-- Every loss in the actual native comparison is subpower, including
the real matching powers and the aggregation to original short domains. -/
theorem nativeFinalListLoss_small {N M H : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hM : Small N M) (hH : Small N H) {d ε C : ℝ}
    (hd : 0 ≤ d) (hε : 0 < ε) (hC : 0 ≤ C) :
    Small N (fun k => nativeFinalListLoss (M k) (H k) d ε C) := by
  have hN0 : ∀ k, 0 ≤ N k := fun k => zero_le_one.trans (hN k)
  have hc (c : ℝ) (h : 0 ≤ c) : Small N (fun _ => c) := Small.const hNt h
  have hV : Small N (fun k => nativeSheetLoss (M k)) := hM.pow hN0 hNt nativeSheetExponent
  have hB : Small N (fun k => commonNativeCapConstant (M k)) :=
    ((hc 27000000 (by norm_num)).mul hN0 hM).mul hN0
      (((hc 2 (by norm_num)).mul hN0 hM).add hNt (hc 5 (by norm_num)))
  have hR : Small N (fun k => nativeReference (M k) (H k) d) :=
    (((hc 8 (by norm_num)).mul hN0 hV).rpow hN hd).mul hN0
      (((hc 475200 (by norm_num)).mul hN0 (hM.pow hN0 hNt 5)).add hNt
        (((hc 360 (by norm_num)).mul hN0 (hH.pow hN0 hNt 4)).mul hN0 hM))
  have hF : Small N (fun k => nativePruning (M k) (nativeReference (M k) (H k) d)) :=
    ((hc 8 (by norm_num)).mul hN0 hM).mul hN0 hR
  have hL : Small N (fun k => nativeListParameter (M k) (commonNativeCapConstant (M k))
      (nativeReference (M k) (H k) d)) :=
    (hc 1 (by norm_num)).add hNt (((hc 14 (by norm_num)).mul hN0 hB).mul hN0 hF)
  have hW : Small N (fun k => nativeMatchingBase (M k) (commonNativeCapConstant (M k))
      (nativeReference (M k) (H k) d) C) :=
    (((hc 8 (by norm_num)).mul hN0 hM).mul hN0
      (((hc C hC).mul hN0 ((hc 6 (by norm_num)).mul hN0 hB)).mul hN0 hR)).add hNt hL
  have hΛ : Small N (fun k => nativeMatchingParameter (M k) (commonNativeCapConstant (M k))
      (nativeReference (M k) (H k) d) C ε) :=
    hM.mul hN0 (hW.rpow hN (by positivity))
  have hpair := hL.mul hN0 (hΛ.rpow hN hd)
  have htime := ((hc 10000 (by norm_num)).mul hN0 hV).pow hN0 hNt 2
  have hforward := (((hc 1320 (by norm_num)).mul hN0
    (hM.pow hN0 hNt 2)).mul hN0 htime).mul hN0 (hc 2 (by norm_num))
  have hreverse := (hc 84 (by norm_num)).mul hN0 htime
  exact (((hc 4 (by norm_num)).mul hN0 hM).add hNt
    ((hforward.add hNt hreverse).mul hN0 hpair)).add hNt (hc 2 (by norm_num))

end
end Submission.Obl.k4_general_wide_layer_offset_comparison
