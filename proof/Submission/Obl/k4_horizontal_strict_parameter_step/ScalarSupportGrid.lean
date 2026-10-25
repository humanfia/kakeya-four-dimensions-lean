import Submission.Lib.K4ScalarFiniteGuard.GridLists

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open Set
open Submission.Lib.K4ScalarFiniteGuard

/-- Passing from one scalar width to a finer comparable width costs a fixed
factor. All bins are taken from the same set of scalar values. -/
theorem scalar_support_at_comparable_width {Ω : Type*} (E : Set Ω) (S : Ω → ℝ)
    {w v K d : ℝ} (hw : 0 < w) (hv : 0 < v) (hwv : w ≤ v)
    (hvw : v ≤ 2 * w) (hK : 0 ≤ K) (hd : 0 ≤ d)
    (C : Finset ℤ) (hC : (C.card : ℝ) ≤ K * v ^ (-d))
    (hcover : ∀ l ∈ E, ⌊S l / v⌋ ∈ C) :
    ∃ B : Finset ℤ, (B.card : ℝ) ≤ 6 * K * w ^ (-d) ∧
      ∀ l ∈ E, ⌊S l / w⌋ ∈ B := by
  classical
  let B := C.biUnion (overlapBins w v hw hv)
  have hcard : (B.card : ℝ) ≤ 6 * C.card := by
    calc
      _ ≤ ∑ c ∈ C, ((overlapBins w v hw hv c).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _c ∈ C, (6 : ℝ) := by
        apply Finset.sum_le_sum
        intro c hc
        have hh := overlapBins_card_le w v hw hv c
        have hratio : 2 * v / w ≤ 4 := (div_le_iff₀ hw).mpr (by linarith)
        linarith
      _ = _ := by simp [mul_comm]
  refine ⟨B, ?_, fun l hl => ?_⟩
  · calc
      _ ≤ 6 * (C.card : ℝ) := hcard
      _ ≤ 6 * (K * v ^ (-d)) := mul_le_mul_of_nonneg_left hC (by norm_num)
      _ ≤ 6 * (K * w ^ (-d)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hw hwv (neg_nonpos.mpr hd)) hK) (by norm_num)
      _ = _ := by ring
  · exact Finset.mem_biUnion.mpr
      ⟨⌊S l / v⌋, hcover l hl, floor_mem_overlapBins w v hw hv (S l)⟩

/-- Scalar support on comparable grid widths gives the full requested width
range. The grid cardinality causes no further loss. -/
theorem scalar_support_from_comparable_grid {Ω T ι : Type*}
    (E : Set (Ω × T)) (S : Ω → T → ℝ) (grid : ι → ℝ)
    {ζ K d : ℝ} (hζ : 0 < ζ) (hK : 0 ≤ K) (hd : 0 ≤ d)
    (hgrid : ∀ i, 0 < grid i)
    (happrox : ∀ w : ℝ, ζ ≤ w → w ≤ 1 → ∃ i, w ≤ grid i ∧ grid i ≤ 2 * w)
    (hsupport : ∀ (t : T) (i : ι), ∃ C : Finset ℤ,
      (C.card : ℝ) ≤ K * (grid i) ^ (-d) ∧
        ∀ l, (l, t) ∈ E → ⌊S l t / grid i⌋ ∈ C) :
    ∀ (t : T) (w : ℝ), ζ ≤ w → w ≤ 1 → ∃ C : Finset ℤ,
      (C.card : ℝ) ≤ 6 * K * w ^ (-d) ∧
        ∀ l, (l, t) ∈ E → ⌊S l t / w⌋ ∈ C := by
  intro t w hw hw1
  obtain ⟨i, hwi, hiw⟩ := happrox w hw hw1
  obtain ⟨C, hC, hcover⟩ := hsupport t i
  exact scalar_support_at_comparable_width {l | (l, t) ∈ E} (fun l => S l t)
    (hζ.trans_le hw) (hgrid i) hwi hiw hK hd C hC hcover

end Submission.Obl.k4_horizontal_strict_parameter_step
