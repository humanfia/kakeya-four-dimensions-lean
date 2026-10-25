-- Adapted from this LOT tree, o206, session x0709, commit 18669b18,
-- Submission/Obl/k4_coarse_pair_frame_preparation/Construction/PrepCoverageBothDerivatives.lean. The data hypotheses are specialized to the native source facts.
import Submission.Obl.k4_homogeneous_native_pair_preparation.PairAux.KernelDerivative
import Submission.Obl.k4_homogeneous_native_pair_preparation.PairMeasure

/-! Both opposite derivative floors for the native two-time stage. -/

namespace Submission.Obl.k4_homogeneous_native_pair_preparation.PairAux

open MeasureTheory Set MvPolynomial
open scoped ENNReal BigOperators

namespace Data

/-- The source equation fails its derivative floor at the witness time. -/
def coverageOwnDerivativeBad (D : Data) (b : Fin D.C) : Set PairPoint :=
  D.coverageRawPairs b ∩ {p |
    |eval (x p.1 p.2.2) (pderiv (3 : Fin 4) (D.R b))| < D.dfl * D.B (D.γ b)}

/-- Either native equation fails at the opposite time. -/
def coverageCrossDerivativeBad (D : Data) (b : Fin D.C) : Set PairPoint :=
  D.coverageOwnDerivativeBad b ∪ D.coverageSourceDerivativeBad b

variable {D : Data} {E : Fin D.W → Set Incidence}

theorem Hyp.coverageOwnDerivativeBad_meas (h : D.Hyp E) (b : Fin D.C) :
    MeasurableSet (D.coverageOwnDerivativeBad b) := by
  have hc : Continuous (fun p : PairPoint =>
      eval (x p.1 p.2.2) (pderiv (3 : Fin 4) (D.R b))) := by
    apply (pderiv (3 : Fin 4) (D.R b)).continuous_eval.comp
    apply continuous_pi
    intro i
    fin_cases i <;> simp [x] <;> fun_prop
  exact (h.coverageRawPairs_meas b).inter
    (measurableSet_lt hc.abs.measurable measurable_const)

theorem Hyp.coverageCrossDerivativeBad_meas (h : D.Hyp E) (b : Fin D.C) :
    MeasurableSet (D.coverageCrossDerivativeBad b) :=
  (h.coverageOwnDerivativeBad_meas b).union (h.coverageSourceDerivativeBad_meas b)

/-- The second opposite floor has the same original-law budget as the first. -/
theorem Hyp.coverage_own_derivative_budget (h : D.Hyp E)
    (ν : Fin D.W → Measure Trajectory) [∀ w, IsProbabilityMeasure (ν w)]
    (ω : Fin D.W → ℝ) (hω : ∀ w, 0 ≤ ω w) (hωsum : ∑ w, ω w = 1)
    (hEunit : ∀ w, E w ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (hdfl : 0 ≤ D.dfl) (hdflK : D.dfl ≤ (1 / D.κ₀) / 2) :
    (∑ b, ENNReal.ofReal (ω (D.γ b) * (2 : ℝ) ^ D.T) *
      ((ν (D.γ b)).prod (volume.prod volume)) (D.coverageOwnDerivativeBad b)) ≤
        ENNReal.ofReal (4 * D.dfl * D.κ₀) := by
  apply Submission.Obl.k4_homogeneous_native_pair_preparation.native_source_derivative_budget
    D.W D.T ν ω D.γ D.Sb D.coverageOwnDerivativeBad h.Sb_meas
    h.coverageOwnDerivativeBad_meas D.R h.Rdeg D.B h.Bpos
    (fun b => (((coarseIdx (D.j b) : ℕ) : ℝ) / (2 : ℝ) ^ D.T))
    (lt_of_lt_of_le zero_lt_one h.κ₀one) hdfl hdflK
    ?_ ?_ (h.coverage_selected_mass_le_one ν ω hω hωsum hEunit)
  · intro b p hp
    refine ⟨?_, (h.sel b hp.1).2.2.2⟩
    simpa only [add_div] using Ico_subset_Icc_self (h.coverage_Sb_coarse b hp)
  · intro b p hp
    exact ⟨hp.1.1, by simpa only [blk, add_div] using hp.1.2.1, hp.2⟩

/-- Both cross-time failures together cost at most `8*dfl*kappa_old`.
There is no label-count or fine-block multiplicity factor. -/
theorem Hyp.coverage_cross_derivative_budget (h : D.Hyp E)
    (ν : Fin D.W → Measure Trajectory) [∀ w, IsProbabilityMeasure (ν w)]
    (ω : Fin D.W → ℝ) (hω : ∀ w, 0 ≤ ω w) (hωsum : ∑ w, ω w = 1)
    (hEunit : ∀ w, E w ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (hdfl : 0 ≤ D.dfl) (hdflK : D.dfl ≤ (1 / D.κ₀) / 2) :
    (∑ b, ENNReal.ofReal (ω (D.γ b) * (2 : ℝ) ^ D.T) *
      ((ν (D.γ b)).prod (volume.prod volume)) (D.coverageCrossDerivativeBad b)) ≤
        ENNReal.ofReal (8 * D.dfl * D.κ₀) := by
  calc
    _ ≤ ∑ b, (ENNReal.ofReal (ω (D.γ b) * (2 : ℝ) ^ D.T) *
          ((ν (D.γ b)).prod (volume.prod volume)) (D.coverageOwnDerivativeBad b) +
        ENNReal.ofReal (ω (D.γ b) * (2 : ℝ) ^ D.T) *
          ((ν (D.γ b)).prod (volume.prod volume)) (D.coverageSourceDerivativeBad b)) := by
      apply Finset.sum_le_sum
      intro b _
      rw [← mul_add]
      exact mul_le_mul' le_rfl (measure_union_le _ _)
    _ = (∑ b, ENNReal.ofReal (ω (D.γ b) * (2 : ℝ) ^ D.T) *
          ((ν (D.γ b)).prod (volume.prod volume)) (D.coverageOwnDerivativeBad b)) +
        ∑ b, ENNReal.ofReal (ω (D.γ b) * (2 : ℝ) ^ D.T) *
          ((ν (D.γ b)).prod (volume.prod volume)) (D.coverageSourceDerivativeBad b) :=
      Finset.sum_add_distrib
    _ ≤ ENNReal.ofReal (4 * D.dfl * D.κ₀) + ENNReal.ofReal (4 * D.dfl * D.κ₀) :=
      add_le_add (h.coverage_own_derivative_budget ν ω hω hωsum hEunit hdfl hdflK)
        (h.coverage_source_derivative_budget ν ω hω hωsum hEunit hdfl hdflK)
    _ = _ := by
      have h0 : 0 ≤ 4 * D.dfl * D.κ₀ := by have := h.κ₀one; positivity
      rw [← ENNReal.ofReal_add h0 h0]
      congr 1
      ring

end Data
end Submission.Obl.k4_homogeneous_native_pair_preparation.PairAux
