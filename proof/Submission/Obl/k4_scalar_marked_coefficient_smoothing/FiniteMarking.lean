import Submission.Obl.k4_scalar_marked_coefficient_smoothing.Interface

namespace Submission.Obl.k4_scalar_marked_coefficient_smoothing

open MeasureTheory Set
open scoped ENNReal

/-- Marking above a relative floor retains inverse-polynomial reference mass. -/
theorem select_marked_mass {ι : Type*} [Fintype ι]
    {K : ℝ} (hK : 0 < K) (v a : ι → ℝ)
    (hv : ∀ i, 0 ≤ v i) (hsum : (∑ i, v i) = 1)
    (hcap : ∀ i, a i ≤ K * v i) (hlower : K⁻¹ ≤ ∑ i, a i) :
    ∃ mark : ι → Bool,
      (∀ i, mark i = true → v i / (2 * K) ≤ a i) ∧
      1 / (2 * K ^ 2) ≤ ∑ i, if mark i = true then v i else 0 := by
  classical
  let mark : ι → Bool := fun i => decide (v i / (2 * K) ≤ a i)
  refine ⟨mark, ?_, ?_⟩
  · intro i hi
    exact of_decide_eq_true hi
  · have hpoint (i : ι) : a i ≤
        K * (if mark i = true then v i else 0) + v i / (2 * K) := by
      by_cases hi : mark i = true
      · rw [ite_eq_left hi]
        exact (hcap i).trans (le_add_of_nonneg_right (div_nonneg (hv i) (by positivity)))
      · rw [ite_eq_right hi, mul_zero, zero_add]
        have : ¬ v i / (2 * K) ≤ a i := by simpa [mark] using hi
        exact (lt_of_not_ge this).le
    have htot := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div, hsum] at htot
    have htotal : K⁻¹ ≤ K * (∑ i, if mark i = true then v i else 0) + 1 / (2 * K) :=
      hlower.trans htot
    have hm : (1 / (2 * K ^ 2)) * K + 1 / (2 * K) = K⁻¹ := by
      field_simp
      <;> ring
    rw [← hm] at htotal
    have : (1 / (2 * K ^ 2)) * K ≤ K * ∑ i, if mark i = true then v i else 0 := by
      linarith
    nlinarith

end Submission.Obl.k4_scalar_marked_coefficient_smoothing
