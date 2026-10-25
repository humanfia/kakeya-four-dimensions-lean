-- Adapted from: here:o202 (session x0952), Regularization/LightBins.lean.
import Submission.Lib.K4CoefficientBinRegularization.Model

namespace Submission.Lib.K4CoefficientBinRegularization.Reg

open MeasureTheory Set
open scoped ENNReal Classical

/-- Deleting light original bins only charges the bins that meet the selected labels.
The threshold uses the original measure of the entire bin. -/
theorem light_code_mass {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (ν : Measure Ω) (code : Ω → ι) (L : Set Ω) (C : Finset ι) {τ : ℝ} (hτ : 0 ≤ τ)
    (hcover : ∀ l ∈ L, code l ∈ C) :
    ν (L ∩ lightCodeSet ν code (fun _ => ENNReal.ofReal τ)) ≤
      ENNReal.ofReal ((C.card : ℝ) * τ) := by
  classical
  let B := C.filter fun b => ν {l | code l = b} < ENNReal.ofReal τ
  have hsub : L ∩ lightCodeSet ν code (fun _ => ENNReal.ofReal τ) ⊆
      ⋃ b ∈ B, {l | code l = b} := by
    rintro l ⟨hl, hlight⟩
    exact mem_biUnion (Finset.mem_filter.mpr ⟨hcover l hl, hlight⟩) rfl
  calc
    _ ≤ ν (⋃ b ∈ B, {l | code l = b}) := measure_mono hsub
    _ ≤ ∑ b ∈ B, ν {l | code l = b} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _b ∈ B, ENNReal.ofReal τ :=
      Finset.sum_le_sum fun b hb => (Finset.mem_filter.mp hb).2.le
    _ ≤ ∑ _b ∈ C, ENNReal.ofReal τ :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul,
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-- A geometric family of original light-bin deletions has a summable cost. -/
theorem geometric_light_code_mass {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (ν : Measure Ω) (code : ℕ → Ω → ι) (L : Set Ω) (active : ℕ → Prop)
    (τ : ℕ → ℝ) {B ratio : ℝ} (hB : 0 ≤ B) (hratio : 0 ≤ ratio) (hratio1 : ratio < 1)
    (hcost : ∀ n, active n →
      ν (L ∩ lightCodeSet ν (code n) (fun _ => ENNReal.ofReal (τ n))) ≤
        ENNReal.ofReal (B * ratio ^ n)) :
    ν (L ∩ ⋃ n : ℕ, if active n then lightCodeSet ν (code n) (fun _ => ENNReal.ofReal (τ n))
      else ∅) ≤ ENNReal.ofReal (B / (1 - ratio)) := by
  classical
  have hsub : L ∩ (⋃ n : ℕ, if active n then lightCodeSet ν (code n) (fun _ => ENNReal.ofReal (τ n))
      else ∅) ⊆ ⋃ n : ℕ, L ∩ (if active n then
        lightCodeSet ν (code n) (fun _ => ENNReal.ofReal (τ n)) else ∅) := by
    rintro l ⟨hl, he⟩
    obtain ⟨n, hn⟩ := mem_iUnion.mp he
    exact mem_iUnion.mpr ⟨n, hl, hn⟩
  calc
    _ ≤ ν (⋃ n : ℕ, L ∩ (if active n then
        lightCodeSet ν (code n) (fun _ => ENNReal.ofReal (τ n)) else ∅)) := measure_mono hsub
    _ ≤ ∑' n : ℕ, ν (L ∩ (if active n then
        lightCodeSet ν (code n) (fun _ => ENNReal.ofReal (τ n)) else ∅)) := measure_iUnion_le _
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (B * ratio ^ n) := by
      apply ENNReal.tsum_le_tsum
      intro n
      split_ifs with hn
      · exact hcost n hn
      · simp
    _ = ENNReal.ofReal (∑' n : ℕ, B * ratio ^ n) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg hB (pow_nonneg hratio n))
        ((summable_geometric_of_lt_one hratio hratio1).mul_left B)).symm
    _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hratio hratio1, div_eq_mul_inv]

end Submission.Lib.K4CoefficientBinRegularization.Reg
