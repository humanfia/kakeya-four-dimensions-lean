-- Adapted from this LOT tree, o206, session x0709, commit 18669b18,
-- Submission/Obl/k4_coarse_pair_frame_preparation/Construction/PrepCoverageDerivative.lean. The data hypotheses are specialized to the native source facts.
import Submission.Obl.k4_homogeneous_native_pair_preparation.PairAux.KernelBasics
import Submission.Obl.k4_homogeneous_native_pair_preparation.PairMeasure

/-! Opposite-time derivative losses for the actual preparation data. -/

namespace Submission.Obl.k4_homogeneous_native_pair_preparation.PairAux

open MeasureTheory Set MvPolynomial
open scoped ENNReal BigOperators

namespace Data

/-- A witness's equation fails its derivative floor at the sampled source time. -/
def coverageDerivativeBad (D : Data) (b : Fin D.C) : Set PairPoint :=
  {p | p.2.1 ∈ D.blk (coarseIdx (D.j b)) ∧ (p.1, p.2.2) ∈ D.Sb b ∧
    |eval (x p.1 p.2.1) (pderiv (3 : Fin 4) (D.R b))| < D.dfl * D.B (D.γ b)}

/-- Raw pairs indexed by the old source chart. -/
def coverageRawPairs (D : Data) (b : Fin D.C) : Set PairPoint :=
  rawSourcePairs (D.Sb b) (D.blk (coarseIdx (D.j b))) (D.selectedIncidences (D.γ b))

/-- Opposite-derivative failures, charged by their source chart. -/
def coverageSourceDerivativeBad (D : Data) (b : Fin D.C) : Set PairPoint :=
  D.coverageRawPairs b ∩ {p | ∃ b', (D.γ b', coarseIdx (D.j b')) =
    (D.γ b, coarseIdx (D.j b)) ∧ p ∈ D.coverageDerivativeBad b'}

variable {D : Data} {E : Fin D.W → Set Incidence}

theorem Hyp.coverageDerivativeBad_meas (h : D.Hyp E) (b : Fin D.C) :
    MeasurableSet (D.coverageDerivativeBad b) := by
  have hc : Continuous (fun p : PairPoint =>
      eval (x p.1 p.2.1) (pderiv (3 : Fin 4) (D.R b))) := by
    apply (pderiv (3 : Fin 4) (D.R b)).continuous_eval.comp
    apply continuous_pi
    intro i
    fin_cases i <;> simp [x] <;> fun_prop
  exact ((show MeasurableSet (D.blk (coarseIdx (D.j b))) from measurableSet_Icc).preimage
      measurable_snd.fst).inter
    (((h.Sb_meas b).preimage (measurable_fst.prodMk measurable_snd.snd)).inter
      (measurableSet_lt hc.abs.measurable measurable_const))

theorem Hyp.coverageRawPairs_meas (h : D.Hyp E) (b : Fin D.C) :
    MeasurableSet (D.coverageRawPairs b) :=
  measurableSet_rawSourcePairs (h.Sb_meas b) (D.blk_meas _) (h.coverage_selected_meas _)

theorem Hyp.coverageSourceDerivativeBad_meas (h : D.Hyp E) (b : Fin D.C) :
    MeasurableSet (D.coverageSourceDerivativeBad b) := by
  apply (h.coverageRawPairs_meas b).inter
  simp only [ofPred_exists]
  apply MeasurableSet.iUnion
  intro b'
  by_cases hb : (D.γ b', coarseIdx (D.j b')) = (D.γ b, coarseIdx (D.j b))
  · simpa only [hb, true_and, ofPred_mem_eq] using h.coverageDerivativeBad_meas b'
  · simp only [hb, false_and, ofPred_false, MeasurableSet.empty]

/-- Actual opposite-time derivative omissions cost `4*dfl*kappa_old` in total,
with the original world weights and both normalized coarse-block time priors. -/
theorem Hyp.coverage_derivative_budget (h : D.Hyp E)
    (ν : Fin D.W → Measure Trajectory) [∀ w, IsProbabilityMeasure (ν w)]
    (ω : Fin D.W → ℝ) (hω : ∀ w, 0 ≤ ω w) (hωsum : ∑ w, ω w = 1)
    (hEunit : ∀ w, E w ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (hdfl : 0 ≤ D.dfl) (hdflK : D.dfl ≤ (1 / D.κ₀) / 2) :
    (∑ b, ENNReal.ofReal (ω (D.γ b) * (2 : ℝ) ^ D.T) *
      ((ν (D.γ b)).prod (volume.prod volume)) (D.coverageDerivativeBad b)) ≤
        ENNReal.ofReal (4 * D.dfl * D.κ₀) := by
  apply Submission.Obl.k4_homogeneous_native_pair_preparation.native_opposite_derivative_budget
    D.W D.T ν ω D.γ D.Sb D.coverageDerivativeBad h.Sb_meas
    h.coverageDerivativeBad_meas D.R h.Rdeg D.B h.Bpos
    (fun b => (((coarseIdx (D.j b) : ℕ) : ℝ) / (2 : ℝ) ^ D.T))
    (lt_of_lt_of_le zero_lt_one h.κ₀one) hdfl hdflK
    ?_ ?_ (h.coverage_selected_mass_le_one ν ω hω hωsum hEunit)
  · intro b p hp
    refine ⟨?_, (h.sel b hp.1).2.2.2⟩
    simpa only [add_div] using Ico_subset_Icc_self (h.coverage_Sb_coarse b hp)
  · intro b p hp
    refine ⟨?_, hp.2.1, hp.2.2⟩
    simpa only [blk, add_div] using hp.1

/-- The same derivative budget with failures indexed by their source chart.
Disjoint source selections allow relabelling by the actual witness at no cost. -/
theorem Hyp.coverage_source_derivative_budget (h : D.Hyp E)
    (ν : Fin D.W → Measure Trajectory) [∀ w, IsProbabilityMeasure (ν w)]
    (ω : Fin D.W → ℝ) (hω : ∀ w, 0 ≤ ω w) (hωsum : ∑ w, ω w = 1)
    (hEunit : ∀ w, E w ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (hdfl : 0 ≤ D.dfl) (hdflK : D.dfl ≤ (1 / D.κ₀) / 2) :
    (∑ b, ENNReal.ofReal (ω (D.γ b) * (2 : ℝ) ^ D.T) *
      ((ν (D.γ b)).prod (volume.prod volume)) (D.coverageSourceDerivativeBad b)) ≤
        ENNReal.ofReal (4 * D.dfl * D.κ₀) := by
  apply le_trans ?_ (h.coverage_derivative_budget ν ω hω hωsum hEunit hdfl hdflK)
  apply weighted_assignment_cover_le
    (fun g : Fin D.W × Fin (2 ^ D.T) => (ν g.1).prod (volume.prod volume))
    (fun g => ENNReal.ofReal (ω g.1 * (2 : ℝ) ^ D.T))
    (fun b => (D.γ b, coarseIdx (D.j b)))
    (fun b => (D.γ b, coarseIdx (D.j b)))
    D.coverageSourceDerivativeBad D.coverageDerivativeBad h.coverageSourceDerivativeBad_meas
  · intro b b' hne hkey
    apply disjoint_left.mpr
    intro p hp hp'
    exact disjoint_left.mp (h.Sb_disjoint hne (congrArg Prod.fst hkey)) hp.1.1 hp'.1.1
  · intro b p hp
    exact hp.2

end Data
end Submission.Obl.k4_homogeneous_native_pair_preparation.PairAux
