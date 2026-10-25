import Mathlib
import ChallengeDeps

-- Adapted from this LOT tree, o158, session x0576, branch x0576:
-- Submission/Obl/k4_matched_pair_representative_realization/DensityDeletion.lean.

namespace Submission.Obl.k4_pair_bin_atlas_assembly

open Set MeasureTheory
open scoped ENNReal

/-- Charge source-base exceptions to the original pair laws before fixing the
source time. The density normalization is quadratic in the block frequency,
whereas the pair mass is linear in that frequency. -/
theorem weighted_source_exception_le {ι X Z : Type*}
    [Fintype ι] [MeasurableSpace X] [MeasurableSpace Z]
    (μ : ι → Measure X) (ρ : Measure Z) (H : ι → Set X) (base : ι → X → Z)
    (ω β : ι → ℝ≥0∞) {q B e : ℝ≥0∞} (hq0 : q ≠ 0) (hqtop : q ≠ ∞)
    (hdensity : ∀ i U, MeasurableSet U →
      q ^ 2 * μ i (H i ∩ base i ⁻¹' U) ≤ β i * ρ U)
    (hbudget : (∑ i, ω i * β i / q) ≤ B)
    (U : ι → Set Z) (hU : ∀ i, MeasurableSet (U i)) (hvol : ∀ i, ρ (U i) ≤ e) :
    (∑ i, (ω i * q) * μ i (H i ∩ base i ⁻¹' U i)) ≤ B * e := by
  have hcancel (i : ι) :
      (ω i * q) * μ i (H i ∩ base i ⁻¹' U i) =
        (ω i / q) * (q ^ 2 * μ i (H i ∩ base i ⁻¹' U i)) := by
    symm
    calc
      _ = (ω i * (q⁻¹ * q)) * (q * μ i (H i ∩ base i ⁻¹' U i)) := by
        simp only [div_eq_mul_inv, pow_two]
        ac_rfl
      _ = _ := by
        rw [ENNReal.inv_mul_cancel hq0 hqtop, mul_one]
        ac_rfl
  calc
    _ = ∑ i, (ω i / q) * (q ^ 2 * μ i (H i ∩ base i ⁻¹' U i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hcancel i
    _ ≤ ∑ i, (ω i / q) * (β i * e) := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ (ω i / q) * (β i * ρ (U i)) := by
          gcongr 1
          exact hdensity i (U i) (hU i)
        _ ≤ _ := by
          gcongr
          exact hvol i
    _ = (∑ i, ω i * β i / q) * e := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      simp only [div_eq_mul_inv]
      ac_rfl
    _ ≤ B * e := by gcongr

/-- Each fixed source has at most two possible representatives. Their bad
base sets therefore cost twice one sublevel volume, independently of how
many representatives there are globally. -/
theorem weighted_two_candidate_exception_le {ι X Z : Type*}
    [Fintype ι] [MeasurableSpace X] [MeasurableSpace Z]
    (μ : ι → Measure X) (ρ : Measure Z) (H : ι → Set X) (base : ι → X → Z)
    (ω β : ι → ℝ≥0∞) {q B e : ℝ≥0∞} (hq0 : q ≠ 0) (hqtop : q ≠ ∞)
    (hdensity : ∀ i U, MeasurableSet U →
      q ^ 2 * μ i (H i ∩ base i ⁻¹' U) ≤ β i * ρ U)
    (hbudget : (∑ i, ω i * β i / q) ≤ B)
    (U : ι → Bool → Set Z) (hU : ∀ i b, MeasurableSet (U i b))
    (hvol : ∀ i b, ρ (U i b) ≤ e) :
    (∑ i, (ω i * q) * μ i (H i ∩ base i ⁻¹' (U i false ∪ U i true))) ≤
      B * (2 * e) := by
  apply weighted_source_exception_le μ ρ H base ω β hq0 hqtop hdensity hbudget
    (fun i => U i false ∪ U i true) (fun i => (hU i false).union (hU i true))
  intro i
  calc
    ρ (U i false ∪ U i true) ≤ ρ (U i false) + ρ (U i true) := measure_union_le _ _
    _ ≤ e + e := add_le_add (hvol i false) (hvol i true)
    _ = 2 * e := (two_mul e).symm

/-- The density deletion bound with the real weights and normalization that
occur in the frozen paired-sheet system. -/
theorem weighted_source_exception_real_le {ι X Z : Type*}
    [Fintype ι] [MeasurableSpace X] [MeasurableSpace Z]
    (μ : ι → Measure X) (ρ : Measure Z) (H : ι → Set X) (base : ι → X → Z)
    (ω β : ι → ℝ) (hω : ∀ i, 0 ≤ ω i) (hβ : ∀ i, 0 ≤ β i)
    {q B e : ℝ} (hq : 0 < q)
    (hdensity : ∀ i U, MeasurableSet U →
      ENNReal.ofReal q ^ 2 * μ i (H i ∩ base i ⁻¹' U) ≤ ENNReal.ofReal (β i) * ρ U)
    (hbudget : (∑ i, ω i * β i / q) ≤ B)
    (U : ι → Set Z) (hU : ∀ i, MeasurableSet (U i))
    (hvol : ∀ i, ρ (U i) ≤ ENNReal.ofReal e) :
    (∑ i, ENNReal.ofReal (ω i * q) * μ i (H i ∩ base i ⁻¹' U i)) ≤
      ENNReal.ofReal (B * e) := by
  have hnonneg (i : ι) : 0 ≤ ω i * β i / q :=
    div_nonneg (mul_nonneg (hω i) (hβ i)) hq.le
  have hB : 0 ≤ B := (Finset.sum_nonneg fun i _ => hnonneg i).trans hbudget
  have hb : (∑ i, ENNReal.ofReal (ω i) * ENNReal.ofReal (β i) /
      ENNReal.ofReal q) ≤ ENNReal.ofReal B := by
    calc
      _ = ENNReal.ofReal (∑ i, ω i * β i / q) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun i _ => hnonneg i]
        apply Finset.sum_congr rfl
        intro i _
        rw [ENNReal.ofReal_div_of_pos hq, ENNReal.ofReal_mul (hω i)]
      _ ≤ _ := ENNReal.ofReal_le_ofReal hbudget
  calc
    _ = ∑ i, (ENNReal.ofReal (ω i) * ENNReal.ofReal q) *
        μ i (H i ∩ base i ⁻¹' U i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [ENNReal.ofReal_mul (hω i)]
    _ ≤ ENNReal.ofReal B * ENNReal.ofReal e :=
      weighted_source_exception_le μ ρ H base (fun i => ENNReal.ofReal (ω i))
        (fun i => ENNReal.ofReal (β i)) (ENNReal.ofReal_ne_zero_iff.mpr hq)
        ENNReal.ofReal_ne_top hdensity hb U hU hvol
    _ = _ := (ENNReal.ofReal_mul hB).symm

/-- A finite candidate table of size at most two costs only two sublevel
volumes for each source, regardless of the total representative family size. -/
theorem weighted_finite_candidate_exception_real_le {ι X Z Bins : Type*}
    [Fintype ι] [MeasurableSpace X] [MeasurableSpace Z] [DecidableEq Bins]
    (μ : ι → Measure X) (ρ : Measure Z) (H : ι → Set X) (base : ι → X → Z)
    (ω β : ι → ℝ) (hω : ∀ i, 0 ≤ ω i) (hβ : ∀ i, 0 ≤ β i)
    {q B e : ℝ} (hq : 0 < q)
    (hdensity : ∀ i U, MeasurableSet U →
      ENNReal.ofReal q ^ 2 * μ i (H i ∩ base i ⁻¹' U) ≤ ENNReal.ofReal (β i) * ρ U)
    (hbudget : (∑ i, ω i * β i / q) ≤ B)
    (cand : ι → Finset Bins) (hcard : ∀ i, (cand i).card ≤ 2)
    (U : ι → Bins → Set Z) (hU : ∀ i b, MeasurableSet (U i b))
    (hvol : ∀ i b, b ∈ cand i → ρ (U i b) ≤ ENNReal.ofReal e) :
    (∑ i, ENNReal.ofReal (ω i * q) *
      μ i (H i ∩ base i ⁻¹' (⋃ b ∈ cand i, U i b))) ≤
      ENNReal.ofReal (B * (2 * e)) := by
  apply weighted_source_exception_real_le μ ρ H base ω β hω hβ hq hdensity hbudget
    (fun i => ⋃ b ∈ cand i, U i b)
  · intro i
    exact Finset.measurableSet_biUnion (cand i) fun b _ => hU i b
  · intro i
    calc
      _ ≤ ∑ b ∈ cand i, ρ (U i b) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _b ∈ cand i, ENNReal.ofReal e := Finset.sum_le_sum fun b hb => hvol i b hb
      _ = ((cand i).card : ℝ≥0∞) * ENNReal.ofReal e := by simp
      _ ≤ 2 * ENNReal.ofReal e := by gcongr; exact_mod_cast hcard i
      _ = ENNReal.ofReal (2 * e) := by rw [ENNReal.ofReal_mul (by norm_num)]; norm_num

end Submission.Obl.k4_pair_bin_atlas_assembly
