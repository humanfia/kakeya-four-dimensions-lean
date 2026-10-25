/- Adapted from: here:o223
   x0775 at 69bf431e (VelocityBins.lean); tightened to three bins by x0927. -/
import Mathlib
import Submission.Lib.K4ChartLifting.NormAngular
import Submission.Lib.K4HorizontalCoercivity.VelocityWitnesses

namespace Submission.Lib.K4ContactAffine

open MeasureTheory Set

/-- A closed interval of radius one mesh step is covered by three offsets
from its center's floor bin, including both boundary cases. -/
theorem interval_cap_of_floor_bin_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Set Ω) (v : Ω → ℝ) {h : ℝ} (hh : 0 < h)
    (cap : ENNReal)
    (hcap : ∀ a : ℤ, μ {p | p ∈ S ∧ ⌊v p / h⌋ = a} ≤ cap) (w : ℝ) :
    μ (S ∩ {p | |v p - w| ≤ h}) ≤ 3 * cap := by
  let F : Finset ℤ := Finset.Icc (-1) 1
  have hsub : S ∩ {p | |v p - w| ≤ h} ⊆
      ⋃ a ∈ F, {p | p ∈ S ∧ ⌊v p / h⌋ = ⌊w / h⌋ + a} := by
    intro p hp
    have hdist : |v p / h - w / h| ≤ (1 : ℝ) := by
      rw [← sub_div, abs_div, abs_of_pos hh]
      exact (div_le_one hh).mpr hp.2
    have hbin := Submission.Lib.K4ChartLifting.Frame.floor_close zero_le_one hdist
    have hbounds : -(1 : ℤ) ≤ ⌊v p / h⌋ - ⌊w / h⌋ ∧
        ⌊v p / h⌋ - ⌊w / h⌋ ≤ 1 := by
      simpa only [Int.ceil_one, abs_le] using hbin
    have hmem : ⌊v p / h⌋ - ⌊w / h⌋ ∈ F := by
      simp only [F, Finset.mem_Icc]
      omega
    exact mem_iUnion₂.mpr ⟨_, hmem, hp.1, by omega⟩
  calc
    _ ≤ μ (⋃ a ∈ F, {p | p ∈ S ∧ ⌊v p / h⌋ = ⌊w / h⌋ + a}) := measure_mono hsub
    _ ≤ ∑ a ∈ F, μ {p | p ∈ S ∧ ⌊v p / h⌋ = ⌊w / h⌋ + a} :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _a ∈ F, cap := Finset.sum_le_sum fun a _ => hcap (⌊w / h⌋ + a)
    _ = _ := by norm_num [F, Int.card_Icc, nsmul_eq_mul]


end Submission.Lib.K4ContactAffine
