/- Adapted from: here:o247 (session x0870, original proofs in commits
4fa3d421, 60e815aa, 71be63c4, and 30be2d73). -/
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

namespace Submission.Lib.K4OriginalStatePreparation

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Add a uniform finite copy index without changing the original law. -/
def uniformCopies {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (r : ℕ) :
    Measure (Ω × Fin r) :=
  μ.prod ((r : ℝ≥0∞)⁻¹ • Measure.count)

theorem uniformIndex_probability {r : ℕ} (hr : 0 < r) :
    IsProbabilityMeasure ((r : ℝ≥0∞)⁻¹ • (Measure.count : Measure (Fin r))) := by
  constructor
  rw [Measure.smul_apply, smul_eq_mul, Measure.count_univ]
  have hcount : (ENat.card (Fin r) : ℝ≥0∞) = r := by simp
  rw [hcount]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hr.ne') (by finiteness)

theorem uniformCopies_singleton {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (r : ℕ) (E : Set Ω) (j : Fin r) :
    uniformCopies μ r (E ×ˢ {j}) = μ E * (r : ℝ≥0∞)⁻¹ := by
  have hr : 0 < r := lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
  haveI := uniformIndex_probability hr
  simp [uniformCopies, Measure.prod_prod, Measure.smul_apply]

theorem uniformCopies_preimage {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {r : ℕ} (hr : 0 < r) (E : Set Ω) :
    uniformCopies μ r (Prod.fst ⁻¹' E) = μ E := by
  haveI := uniformIndex_probability hr
  have hset : Prod.fst ⁻¹' E = E ×ˢ (univ : Set (Fin r)) := by ext p; simp
  rw [hset, uniformCopies, Measure.prod_prod, Measure.smul_apply, smul_eq_mul,
    Measure.count_univ]
  have hcount : (ENat.card (Fin r) : ℝ≥0∞) = r := by simp
  rw [hcount, ENNReal.inv_mul_cancel (by exact_mod_cast hr.ne') (by finiteness), mul_one]

theorem uniformCopies_finite {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {r : ℕ} (hr : 0 < r) :
    IsFiniteMeasure (uniformCopies μ r) := by
  constructor
  have h := uniformCopies_preimage μ hr univ
  simp only [preimage_univ] at h
  rw [h]
  exact measure_lt_top _ _

/-- Splitting a source label into `r` equiprobable copies divides its
index/base ceiling by `r`, in the same original mass units. -/
theorem uniformCopies_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {r : ℕ} (hr : 0 < r)
    (E : Set Ω) (j : Fin r) (A : ℝ) (B : ℝ≥0∞)
    (hcap : μ E ≤ ENNReal.ofReal ((r : ℝ) * A) * B) :
    uniformCopies μ r (E ×ˢ {j}) ≤ ENNReal.ofReal A * B := by
  rw [uniformCopies_singleton]
  calc
    _ ≤ (ENNReal.ofReal ((r : ℝ) * A) * B) * (r : ℝ≥0∞)⁻¹ :=
      mul_le_mul_of_nonneg_right hcap zero_le
    _ = _ := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg r), ENNReal.ofReal_natCast]
      calc
        ((r : ℝ≥0∞) * ENNReal.ofReal A * B) * (r : ℝ≥0∞)⁻¹ =
            ((r : ℝ≥0∞) * (r : ℝ≥0∞)⁻¹) * (ENNReal.ofReal A * B) := by ring
        _ = _ := by
          rw [ENNReal.mul_inv_cancel (by exact_mod_cast hr.ne') (by finiteness), one_mul]

/-- The reference sum for the copied source indices is exactly `r` times
its old fine-weight sum. The witness indices are unchanged. -/
theorem uniformCopies_reference_sum {ι₁ ι₂ Λ : Type*} [Fintype ι₁] [Fintype ι₂]
    (lab₁ : ι₁ → Λ) (lab₂ : ι₂ → Λ) (w : Λ → ℝ) (r : ℕ) :
    (∑ i : (ι₁ × Fin r) ⊕ ι₂, w (Sum.elim (fun p => lab₁ p.1) lab₂ i)) =
      (r : ℝ) * (∑ i, w (lab₁ i)) + ∑ j, w (lab₂ j) := by
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Sum.elim_inl, Sum.elim_inr,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]

/-- Rounding the ratio of the two layer weights creates at most a factor
of two in the original reference budget. -/
theorem uniformCopies_reference_budget {ι₁ ι₂ Λ : Type*} [Fintype ι₁] [Fintype ι₂]
    (lab₁ : ι₁ → Λ) (lab₂ : ι₂ → Λ) (coarse fine : Λ → ℝ) (r : ℕ)
    (hround : ∀ l, (r : ℝ) * fine l ≤ 2 * coarse l) :
    (∑ i : (ι₁ × Fin r) ⊕ ι₂, fine (Sum.elim (fun p => lab₁ p.1) lab₂ i)) ≤
      2 * (∑ i, coarse (lab₁ i)) + ∑ j, fine (lab₂ j) := by
  rw [uniformCopies_reference_sum, Finset.mul_sum, Finset.mul_sum]
  exact add_le_add (Finset.sum_le_sum fun i _ => hround (lab₁ i)) le_rfl

end

end Submission.Lib.K4OriginalStatePreparation
