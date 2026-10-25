import Submission.Obl.k4_homogeneous_native_pair_preparation.PairMeasure
-- Adapted from this LOT tree, o206, session x0709, commit 18669b18,
-- Submission/Obl/k4_coarse_pair_frame_preparation/Construction/PrepCoverageBasics.lean. The data hypotheses are specialized to the native source facts.
import Submission.Obl.k4_homogeneous_native_pair_preparation.PairAux.Data
import Submission.Obl.k4_homogeneous_native_pair_preparation.PairAux.JensenCoverage

/-! Original selected incidences of a preparation sample. -/

namespace Submission.Obl.k4_homogeneous_native_pair_preparation.PairAux

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Data

variable {D : Data} {E : Fin D.W → Set (Trajectory × ℝ)}

/-- Trimming fine-block endpoints leaves the original selected mass unchanged. -/
theorem Hyp.coverage_Sb_mass (h : D.Hyp E)
    (ν : Measure Trajectory) (b : Fin D.C) :
    (ν.prod volume) (D.Sb b) = (ν.prod volume) (D.F b) := by
  apply Submission.Obl.k4_quadratic_finite_greedy_cover.measure_trim_right
  intro p hp
  exact (h.sel b hp).2.2.1.2

/-- Selected incidences lie in the half-open coarse block of their fine block. -/
theorem Hyp.coverage_Sb_coarse (h : D.Hyp E)
    (b : Fin D.C) {p : Trajectory × ℝ} (hp : p ∈ D.Sb b) :
    p.2 ∈ Ico (((coarseIdx (D.j b) : ℕ) : ℝ) / (2 : ℝ) ^ D.T)
      ((((coarseIdx (D.j b) : ℕ) : ℝ) + 1) / (2 : ℝ) ^ D.T) := h.Sb_coarse b hp

/-- The selected event in an original world. -/
def selectedIncidences (D : Data) (w : Fin D.W) : Set (Trajectory × ℝ) :=
  {p | ∃ b, D.γ b = w ∧ p ∈ D.Sb b}

theorem Hyp.coverage_selected_meas (h : D.Hyp E) (w : Fin D.W) :
    MeasurableSet (D.selectedIncidences w) := by
  classical
  simp only [selectedIncidences, ofPred_exists]
  apply MeasurableSet.iUnion
  intro b
  by_cases hb : D.γ b = w
  · simpa only [hb, true_and, ofPred_mem_eq] using h.Sb_meas b
  · simp only [hb, false_and, ofPred_false, MeasurableSet.empty]

theorem Hyp.coverage_weighted_Sb_mass (h : D.Hyp E)
    (ν : Fin D.W → Measure Trajectory) (ω : Fin D.W → ℝ≥0∞) :
    (∑ b, ω (D.γ b) * ((ν (D.γ b)).prod volume) (D.Sb b)) =
      ∑ b, ω (D.γ b) * ((ν (D.γ b)).prod volume) (D.F b) := by
  apply Finset.sum_congr rfl
  intro b _
  rw [h.coverage_Sb_mass]

/-- The original witness selections have total weighted mass at most one. -/
theorem Hyp.coverage_selected_mass_le_one (h : D.Hyp E)
    (ν : Fin D.W → Measure Trajectory) [∀ w, IsProbabilityMeasure (ν w)]
    (ω : Fin D.W → ℝ) (hω : ∀ w, 0 ≤ ω w) (hωsum : ∑ w, ω w = 1)
    (hEunit : ∀ w, E w ⊆ univ ×ˢ Icc (0 : ℝ) 1) :
    (∑ b, ENNReal.ofReal (ω (D.γ b)) * ((ν (D.γ b)).prod volume) (D.Sb b)) ≤ 1 := by
  apply Submission.Obl.k4_homogeneous_native_pair_preparation.selected_source_mass_le_one
    D.W ν ω hω hωsum D.γ D.Sb h.Sb_meas (fun b b' hne hγ => h.Sb_disjoint hne hγ)
  intro b p hp
  exact hEunit (D.γ b) (h.sel b hp.1).1

end Data
end Submission.Obl.k4_homogeneous_native_pair_preparation.PairAux
