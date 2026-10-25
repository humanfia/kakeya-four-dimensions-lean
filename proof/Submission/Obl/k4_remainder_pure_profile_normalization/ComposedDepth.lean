import Submission.Obl.k4_remainder_pure_profile_normalization.Definitions
import Submission.Lib.K4Homogenization.DensityExponents

namespace Submission.Obl.k4_remainder_pure_profile_normalization
open Filter
open scoped Topology

/-- The exact original depth corresponding to the product of two dyadic widths. -/
noncomputable def composedDepth (N r s : ℝ) : ℝ :=
  ((⌊r * Real.log N / Real.log 2⌋ : ℤ) + (⌊s * Real.log N / Real.log 2⌋ : ℤ) : ℝ) *
    Real.log 2 / Real.log N

theorem delta_composedDepth {N : ℝ} (hN : 1 < N) (r s : ℝ) :
    δ N (composedDepth N r s) = δ N r * δ N s := by
  have hlogN : Real.log N ≠ 0 := (Real.log_pos hN).ne'
  have hlog2 : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have heq : composedDepth N r s * Real.log N / Real.log 2 =
      ((⌊r * Real.log N / Real.log 2⌋ : ℤ) + (⌊s * Real.log N / Real.log 2⌋ : ℤ) : ℝ) := by
    unfold composedDepth
    field_simp
  unfold δ
  rw [heq]
  rw [← Int.cast_add, Int.floor_intCast, neg_add, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]

theorem composedDepth_bounds {N : ℝ} (hN : 1 < N) (r s : ℝ) :
    r + s - 2 * (Real.log 2 / Real.log N) ≤ composedDepth N r s ∧
      composedDepth N r s ≤ r + s := by
  have hlogN : 0 < Real.log N := Real.log_pos hN
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hrlo := Int.sub_one_lt_floor (r * Real.log N / Real.log 2)
  have hslo := Int.sub_one_lt_floor (s * Real.log N / Real.log 2)
  have hrhi := Int.floor_le (r * Real.log N / Real.log 2)
  have hshi := Int.floor_le (s * Real.log N / Real.log 2)
  have hfactor : 0 < Real.log 2 / Real.log N := div_pos hlog2 hlogN
  have heq (x : ℝ) : (x * Real.log N / Real.log 2) * (Real.log 2 / Real.log N) = x := by
    field_simp
  constructor
  · have hh := mul_le_mul_of_nonneg_right (le_of_lt (add_lt_add hrlo hslo)) hfactor.le
    dsimp only [composedDepth]
    push_cast
    rw [sub_add_sub_comm, sub_mul, add_mul, heq, heq] at hh
    convert hh using 1 <;> ring
  · have hh := mul_le_mul_of_nonneg_right (add_le_add hrhi hshi) hfactor.le
    dsimp only [composedDepth]
    push_cast
    simp only [add_mul, heq] at hh
    convert hh using 1 <;> ring

theorem composedDepth_nonneg {N r s : ℝ} (hN : 1 < N) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    0 ≤ composedDepth N r s := by
  unfold composedDepth
  have hln : 0 ≤ Real.log N := (Real.log_pos hN).le
  have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hfr : 0 ≤ (⌊r * Real.log N / Real.log 2⌋ : ℤ) :=
    Int.floor_nonneg.mpr (div_nonneg (mul_nonneg hr hln) h2.le)
  have hfs : 0 ≤ (⌊s * Real.log N / Real.log 2⌋ : ℤ) :=
    Int.floor_nonneg.mpr (div_nonneg (mul_nonneg hs hln) h2.le)
  positivity

theorem composedDepth_tendsto {N : ℕ → ℝ} (hN : ∀ k, 1 < N k)
    (ht : Tendsto N atTop atTop) (r s : ℝ) :
    Tendsto (fun k => composedDepth (N k) r s) atTop (𝓝 (r + s)) := by
  have herr := Submission.Lib.K4Homogenization.dyadic_density_rounding_tendsto_zero ht
  have hlo : Tendsto (fun k => r + s - 2 * (Real.log 2 / Real.log (N k)))
      atTop (𝓝 (r + s)) := by
    simpa only [mul_zero, sub_zero] using tendsto_const_nhds.sub (tendsto_const_nhds.mul herr)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds
    (fun k => (composedDepth_bounds (hN k) r s).1)
    (fun k => (composedDepth_bounds (hN k) r s).2)

end Submission.Obl.k4_remainder_pure_profile_normalization
