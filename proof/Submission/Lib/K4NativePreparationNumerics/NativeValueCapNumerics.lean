/-
Adapted from: here:o204
Original file: Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/NativeValueCapNumerics.lean.
Any earlier attribution is retained below.
-/
import Submission.Lib.K4NativePreparationNumerics.NativeScaleNumerics
import Submission.Lib.K4NativePreparationNumerics.NativeTimeRatio

/-! The original pure ceiling pays native value/core geometry without
using the entropy palette parameter. The envelope depends only on the path
factor, original source factor, and freely chosen density tolerances. -/

namespace Submission.Lib.K4NativePreparationNumerics

open scoped ENNReal

noncomputable def nativePreGeometryEnvelope (κ source N tolerance : ℝ) : ℝ :=
  2304 * max κ source * N ^ tolerance

theorem native_pre_geometry_envelope_bounds {κ source N tolerance : ℝ}
    (hκ : 1 ≤ κ) (hN : 1 ≤ N) (htolerance : 0 ≤ tolerance) :
    2304 ≤ nativePreGeometryEnvelope κ source N tolerance ∧
      3 * κ ≤ nativePreGeometryEnvelope κ source N tolerance ∧
      max κ source ≤ nativePreGeometryEnvelope κ source N tolerance ∧
      N ^ tolerance ≤ nativePreGeometryEnvelope κ source N tolerance := by
  have hmax : 1 ≤ max κ source := hκ.trans (le_max_left _ _)
  have hpow : 1 ≤ N ^ tolerance := Real.one_le_rpow hN htolerance
  have hmax0 : 0 ≤ max κ source := by linarith
  have hpow0 : 0 ≤ N ^ tolerance := by linarith
  unfold nativePreGeometryEnvelope
  have hconstant : 2304 ≤ 2304 * max κ source * N ^ tolerance := by
    nlinarith [mul_le_mul hmax hpow (by norm_num : (0 : ℝ) ≤ 1) hmax0]
  have hscale : 2304 * max κ source ≤ 2304 * max κ source * N ^ tolerance := by
    nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 2304) hmax0]
  have hpower : N ^ tolerance ≤ 2304 * max κ source * N ^ tolerance := by
    nlinarith
  exact ⟨hconstant, (by nlinarith [le_max_left κ source]), by nlinarith, hpower⟩

/-- The actual coefficient used by source_heavy_original_value_branches
is bounded by a fixed power of the pregeometry envelope. The profile value
cancels exactly, before any sampled seven-bin restriction. -/
theorem native_original_value_cap_budget {N κ source tolerance profile K : ℝ} {q : ℕ}
    (hN : 0 < N) (hκ : 1 ≤ κ) (hK : 2304 ≤ K)
    (hmax : max κ source ≤ K) (hpower : N ^ tolerance ≤ K) (hq : 7 ≤ q) :
    ((ENNReal.ofReal (N ^ (-profile + tolerance)) *
        ENNReal.ofReal (64 * (max κ source) ^ 2)) *
        ENNReal.ofReal (κ * N ^ profile)) * ENNReal.ofReal (36 * κ ^ 2) ≤
      ENNReal.ofReal (K ^ q) := by
  have hκ0 : 0 ≤ κ := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hmax0 : 0 ≤ max κ source := hκ0.trans (le_max_left _ _)
  have hκK : κ ≤ K := (le_max_left _ _).trans hmax
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hcancel : N ^ (-profile + tolerance) * N ^ profile = N ^ tolerance := by
    rw [← Real.rpow_add hN]
    congr 1
    ring
  calc
    _ = 2304 * κ ^ 3 * (max κ source) ^ 2 *
        (N ^ (-profile + tolerance) * N ^ profile) := by ring
    _ = 2304 * κ ^ 3 * (max κ source) ^ 2 * N ^ tolerance := by rw [hcancel]
    _ ≤ K * K ^ 3 * K ^ 2 * K := by gcongr
    _ = K ^ 7 := by ring
    _ ≤ K ^ q := pow_le_pow_right₀ hK1 hq

/-- The pregeometry envelope has any prescribed small exponent once the
source factor, path factor and density tolerance have been budgeted. -/
theorem native_pre_geometry_envelope_power {κ source N tolerance σ slack budget : ℝ}
    (hN : 1 ≤ N) (hκ : κ ≤ N ^ σ) (hsource : source ≤ N ^ σ)
    (hconstant : 2304 ≤ N ^ slack) (hbudget : slack + σ + tolerance ≤ budget) :
    nativePreGeometryEnvelope κ source N tolerance ≤ N ^ budget := by
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  unfold nativePreGeometryEnvelope
  calc
    _ ≤ 2304 * N ^ σ * N ^ tolerance := by
      gcongr
      exact max_le hκ hsource
    _ ≤ N ^ slack * N ^ σ * N ^ tolerance := by gcongr
    _ = N ^ (slack + σ + tolerance) := by rw [Real.rpow_add hNpos, Real.rpow_add hNpos]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN hbudget

end Submission.Lib.K4NativePreparationNumerics
