/-
Adapted from: here:o204
Original file: Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/NativeScaleNumerics.lean.
Any earlier attribution is retained below.
-/
import Submission.Lib.K4NativePreparationNumerics.PaletteBudgetChoice
import Mathlib.Tactic.Linarith

/-! Actual palette and angular constants fit a path-power envelope without
putting the entropy power into the geometric or observation-list envelope. -/

namespace Submission.Lib.K4NativePreparationNumerics

open scoped ENNReal

theorem native_palette_integer_bounds {κ : ℝ} (hκ : 1 ≤ κ) :
    1 ≤ ⌈(4 * κ + 6) ^ 2⌉₊ ∧ (⌈(4 * κ + 6) ^ 2⌉₊ : ℝ) ≤ 101 * κ ^ 2 := by
  have hpos : 0 < (4 * κ + 6) ^ 2 := by positivity
  have hceil := Nat.ceil_lt_add_one hpos.le
  refine ⟨Nat.one_le_ceil_iff.mpr hpos, ?_⟩
  have hlinear : 4 * κ + 6 ≤ 10 * κ := by linarith
  have hsquare : (4 * κ + 6) ^ 2 ≤ (10 * κ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hlinear 2
  have hκsquare : 1 ≤ κ ^ 2 := one_le_pow₀ hκ
  nlinarith

theorem native_palette_inverse_floor {κ E R fraction : ℝ} {K : ℕ}
    (hκ : 0 ≤ κ) (hκE : κ ≤ E) (_hK : 1 ≤ K) (hKupper : (K : ℝ) ≤ 101 * κ ^ 2)
    (hfraction : 0 < fraction) (hconstant : 12928 / fraction ≤ E) (hR : 0 ≤ R) :
    (fraction / (R / palettePruningThreshold K))⁻¹ ≤ E ^ 3 * R := by
  have heq : (fraction / (R / palettePruningThreshold K))⁻¹ = (128 / fraction) * K * R := by
    unfold palettePruningThreshold
    rw [inv_div, div_inv_eq_mul]
    ring
  rw [heq]
  have hE : 0 ≤ E := hκ.trans hκE
  have hsquare : κ ^ 2 ≤ E ^ 2 := pow_le_pow_left₀ hκ hκE 2
  calc
    _ ≤ (128 / fraction) * (101 * κ ^ 2) * R := by gcongr
    _ = (12928 / fraction) * κ ^ 2 * R := by ring
    _ ≤ E * E ^ 2 * R := by gcongr
    _ = _ := by ring

theorem native_angular_coefficient_envelope {κ E x y : ℝ} (m : ℕ)
    (hκ : 0 ≤ κ) (hκE : κ ≤ E) (hconstant : 819200 * (m : ℝ) ≤ E)
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    819200 * (m : ℝ) * κ ^ 3 * x ≤ E ^ 4 * y := by
  have hE : 0 ≤ E := hκ.trans hκE
  have hc : 819200 * (m : ℝ) * κ ^ 3 ≤ E ^ 4 := by
    calc
      _ ≤ E * E ^ 3 := mul_le_mul hconstant (pow_le_pow_left₀ hκ hκE 3) (by positivity) hE
      _ = _ := by ring
  exact mul_le_mul hc hxy hx (pow_nonneg hE _)

theorem native_overlap_original_budget {κ E : ℝ} (hκ : 1 ≤ κ) (hκE : κ ≤ E) :
    (100 * E ^ 8)⁻¹ ≤ κ⁻¹ / 64 := by
  have hκpos : 0 < κ := zero_lt_one.trans_le hκ
  have hE : 1 ≤ E := hκ.trans hκE
  have hpow : E ≤ E ^ 8 := by
    calc
      E = E * 1 := by ring
      _ ≤ E * E ^ 7 := mul_le_mul_of_nonneg_left (one_le_pow₀ hE) (by linarith)
      _ = E ^ 8 := by ring
  have hden : 64 * κ ≤ 100 * E ^ 8 := by nlinarith
  have h := one_div_le_one_div_of_le (by positivity : 0 < 64 * κ) hden
  have heq : 1 / (64 * κ) = κ⁻¹ / 64 := by ring
  simpa only [one_div, heq] using h

noncomputable def nativeEnvelopeConstant (m Jpred : ℕ) (fraction : ℝ) : ℝ :=
  103 + (m : ℝ) + 819200 * (m : ℝ) + 12928 / fraction + 250 * (Jpred : ℝ)

theorem native_envelope_constants (m Jpred : ℕ) {fraction κ : ℝ}
    (hfraction : 0 < fraction) (hκ : 1 ≤ κ) :
    let E0 := nativeEnvelopeConstant m Jpred fraction
    1 ≤ E0 ∧ 100 ≤ E0 * κ ∧ 3 * κ ≤ E0 * κ ∧ (m : ℝ) * κ ≤ E0 * κ ∧
      12928 / fraction ≤ E0 * κ ∧ 819200 * (m : ℝ) ≤ E0 * κ ∧
      250 * (Jpred : ℝ) ≤ E0 * κ := by
  have hf : 0 ≤ 12928 / fraction := by positivity
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hJ : 0 ≤ (Jpred : ℝ) := Nat.cast_nonneg _
  let E0 := nativeEnvelopeConstant m Jpred fraction
  have hE0 : 103 ≤ E0 := by dsimp only [E0, nativeEnvelopeConstant]; nlinarith
  have hE0κ : E0 ≤ E0 * κ := by
    calc
      _ = E0 * 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hκ (by linarith)
  have hκpos : 0 ≤ κ := by linarith
  have hmE0 : (m : ℝ) ≤ E0 := by dsimp only [E0, nativeEnvelopeConstant]; nlinarith
  have hfE0 : 12928 / fraction ≤ E0 := by dsimp only [E0, nativeEnvelopeConstant]; nlinarith
  have hcE0 : 819200 * (m : ℝ) ≤ E0 := by dsimp only [E0, nativeEnvelopeConstant]; nlinarith
  have hJE0 : 250 * (Jpred : ℝ) ≤ E0 := by dsimp only [E0, nativeEnvelopeConstant]; nlinarith
  exact ⟨by linarith, by linarith,
    mul_le_mul_of_nonneg_right (by linarith : (3 : ℝ) ≤ E0) hκpos,
    mul_le_mul_of_nonneg_right hmE0 hκpos, hfE0.trans hE0κ, hcE0.trans hE0κ, hJE0.trans hE0κ⟩

end Submission.Lib.K4NativePreparationNumerics
