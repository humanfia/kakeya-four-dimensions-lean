/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/OldLayerBudgets.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.Interface
import Submission.Obl.k4_quadratic_atlas_normalization.AssignmentMass

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set

noncomputable section

/-- A full-time layer pays for all of its geometric numerators from its current
mass. The estimate uses disjoint original assignments, with no count of charts. -/
theorem LayerAt.numerator_budget {α : Type} [MeasurableSpace α]
    {N : ℕ → ℝ} {d e₀ : ℝ} {π : ℕ → Measure ℝ}
    {b : ℕ → α → Fin 6 → ℝ} {k : ℕ} {ε D a : ℝ}
    {ρH : Measure (α × ℝ)} {n : ℕ} {A : Fin n → Set α}
    {q : Fin n → Fin 3 → ℤ} {h : Fin n → Fin 6 → ℝ}
    (H : LayerAt N d e₀ π b k ε ρH D a n A q h) (hN : 0 < N k) :
    (∑ i, ENNReal.ofReal (D ^ 2 * a ^ d) *
      π k (Ico ((q i 0 : ℝ) * N k ^ (-e₀))
        (((q i 0 : ℝ) + 1) * N k ^ (-e₀)))) ≤
      ENNReal.ofReal (N k ^ ε) * ρH univ := by
  have hp : 0 < N k ^ ε := Real.rpow_pos_of_pos hN _
  have hcancel : ENNReal.ofReal (N k ^ ε) *
      ENNReal.ofReal (D ^ 2 * a ^ d / N k ^ ε) =
      ENNReal.ofReal (D ^ 2 * a ^ d) := by
    rw [← ENNReal.ofReal_mul hp.le]
    congr 1
    field_simp
  have hsum : (∑ i, ρH (A i ×ˢ Icc (0 : ℝ) 1)) ≤ ρH univ := by
    simpa using
      Submission.Obl.k4_quadratic_atlas_normalization.sum_measure_assignment_fiber_le
        ρH (fun _ : Fin n => ()) (fun i => A i ×ˢ Icc (0 : ℝ) 1) ()
        (fun i => (H.1 i).prod measurableSet_Icc)
        (fun i i' hne _ => (H.2.1 i i' hne).set_prod_left _ _)
  calc
    _ = ENNReal.ofReal (N k ^ ε) *
        ∑ i, ENNReal.ofReal (D ^ 2 * a ^ d / N k ^ ε) *
          π k (Ico ((q i 0 : ℝ) * N k ^ (-e₀))
            (((q i 0 : ℝ) + 1) * N k ^ (-e₀))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [← mul_assoc, hcancel]
    _ ≤ ENNReal.ofReal (N k ^ ε) * ∑ i, ρH (A i ×ˢ Icc (0 : ℝ) 1) := by
      gcongr with i
      exact (H.2.2.1 i).2.2.2
    _ ≤ _ := by gcongr

/-- The original prior of each full-time assignment already controls its
geometric numerator. Restricting the current law never changes this denominator. -/
theorem LayerAt.original_prior_bound {α : Type} [MeasurableSpace α]
    {N : ℕ → ℝ} {d e₀ : ℝ} {π : ℕ → Measure ℝ}
    {b : ℕ → α → Fin 6 → ℝ} {k : ℕ} {ε D a K : ℝ}
    {ρH : Measure (α × ℝ)} {ν : Measure α} {n : ℕ} {A : Fin n → Set α}
    {q : Fin n → Fin 3 → ℤ} {h : Fin n → Fin 6 → ℝ}
    (H : LayerAt N d e₀ π b k ε ρH D a n A q h) (hN : 0 < N k)
    (hdom : ρH ≤ ENNReal.ofReal K • (ν.prod volume)) (i : Fin n) :
    ENNReal.ofReal (D ^ 2 * a ^ d) *
      π k (Ico ((q i 0 : ℝ) * N k ^ (-e₀))
        (((q i 0 : ℝ) + 1) * N k ^ (-e₀))) ≤
      ENNReal.ofReal (N k ^ ε) * ENNReal.ofReal K * ν (A i) := by
  have hp : 0 < N k ^ ε := Real.rpow_pos_of_pos hN _
  have hf := mul_le_mul_right ((H.2.2.1 i).2.2.2) (ENNReal.ofReal (N k ^ ε))
  have hcancel : ENNReal.ofReal (N k ^ ε) *
      ENNReal.ofReal (D ^ 2 * a ^ d / N k ^ ε) =
      ENNReal.ofReal (D ^ 2 * a ^ d) := by
    rw [← ENNReal.ofReal_mul hp.le]
    congr 1
    field_simp
  rw [← mul_assoc, hcancel] at hf
  apply hf.trans
  have hb := hdom (A i ×ˢ Icc (0 : ℝ) 1)
  rw [Measure.smul_apply, Measure.prod_prod] at hb
  simp only [Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one, smul_eq_mul] at hb
  calc
    _ ≤ ENNReal.ofReal (N k ^ ε) *
        (ENNReal.ofReal K * ν (A i)) := by gcongr
    _ = _ := (mul_assoc _ _ _).symm

end

end Submission.Obl.k4_horizontal_strict_parameter_step
