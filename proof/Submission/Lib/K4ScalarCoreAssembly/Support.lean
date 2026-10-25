/-
Adapted from: here:o062
The bounded power difference estimate comes from accepted here:o070,
Submission/Obl/k4_matching_switching_target_certificate/Jitter.lean, lemma
abs_pow_sub_pow_le_of_abs_le. That file credits o080/x0305,
Submission/Obl/k4_matching_geometric_path_cover/Jitter.lean, written by x0274;
its endpoint estimates additionally credit o015/x0047/EndpointLipschitz.lean.
This is the only promoted primitive from that source.
-/

import Mathlib
import Submission.Lib.K4ScalarCoreTools
import Submission.Lib.K4ScalarSwitching.PolynomialDegree

namespace Submission.Lib.K4ScalarCoreAssembly

lemma bounded_pow_difference {a b B : ℝ} (hB : 1 ≤ B) (ha : |a| ≤ B) (hb : |b| ≤ B)
    {k n : ℕ} (hkn : k ≤ n) : |a ^ k - b ^ k| ≤ (n : ℝ) * B ^ n * |a - b| := by
  have hmax0 : 0 ≤ max |a| |b| := le_max_of_le_left (abs_nonneg _)
  have hpow : max |a| |b| ^ (k - 1) ≤ B ^ n :=
    (pow_le_pow_left₀ hmax0 (max_le ha hb) _).trans (pow_le_pow_right₀ hB (by omega))
  have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
  calc |a ^ k - b ^ k| ≤ |a - b| * k * max |a| |b| ^ (k - 1) := abs_pow_sub_pow_le a b k
    _ ≤ |a - b| * n * B ^ n := by
        gcongr
    _ = (n : ℝ) * B ^ n * |a - b| := by ring



/-- The integer window underlying accepted here:o177/GraphCaps.floor_offset_mem,
written here directly from Mathlib floor bounds for neighborhood transport. -/
theorem bounded_floor_offset_mem {a L x y : ℝ} (ha : 0 < a)
    (hfit : |x-y| ≤ L*a) :
    ⌊x/a⌋-⌊y/a⌋ ∈ Finset.Icc (-⌈L+1⌉) ⌈L+1⌉ := by
  have hxy : |x/a-y/a| ≤ L := by
    rw [← sub_div, abs_div, abs_of_pos ha]
    exact (div_le_iff₀ ha).mpr hfit
  have hx₀ := Int.floor_le (x/a)
  have hx₁ := Int.lt_floor_add_one (x/a)
  have hy₀ := Int.floor_le (y/a)
  have hy₁ := Int.lt_floor_add_one (y/a)
  have hc := Int.le_ceil (L+1)
  have hh : |((⌊x/a⌋-⌊y/a⌋ : ℤ) : ℝ)| ≤ (⌈L+1⌉ : ℤ) := by
    rw [Int.cast_sub, abs_le]
    constructor <;> linarith [(abs_le.mp hxy).1, (abs_le.mp hxy).2]
  rw [abs_le] at hh
  exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hh.1, by exact_mod_cast hh.2⟩

end Submission.Lib.K4ScalarCoreAssembly
