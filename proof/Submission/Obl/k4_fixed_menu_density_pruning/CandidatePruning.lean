-- Adapted from this LOT tree, o194, session x0674, commit 182d9543,
-- Submission/Obl/k4_greedy_cover_graph_atlas/CandidatePruning.lean.
-- Adapted from this LOT tree, o173, session x0598, commit 6ded8016fe11,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/CandidatePruning.lean.

import Submission.Obl.k4_quadratic_atlas_normalization.AssignmentMass
import Submission.Obl.k4_quadratic_atlas_normalization.MassSelection

namespace Submission.Obl.k4_fixed_menu_density_pruning

open MeasureTheory Set Finset

/-- Disjoint candidates charge an exceptional set only once in each original world. -/
theorem weighted_candidate_exception_le {X Γ ι : Type*} [MeasurableSpace X]
    [Fintype Γ] [Fintype ι] (μ : Γ → Measure X) (w : Γ → ENNReal)
    (γ : ι → Γ) (V : ι → Set X) (E : Γ → Set X)
    (hV : ∀ a, MeasurableSet (V a))
    (hdisj : ∀ a b, a ≠ b → γ a = γ b → Disjoint (V a) (V b)) :
    ∑ a, w (γ a) * μ (γ a) (V a ∩ E (γ a)) ≤
      ∑ g, w g * μ g (E g) := by
  classical
  have hfiber (g : Γ) :
      ∑ a ∈ univ.filter (fun a => γ a = g), w (γ a) * μ (γ a) (V a ∩ E (γ a)) ≤
        w g * μ g (E g) := by
    calc
      _ = w g * ∑ a ∈ univ.filter (fun a => γ a = g), (μ g).restrict (E g) (V a) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro a ha
        rw [(mem_filter.mp ha).2, Measure.restrict_apply (hV a)]
      _ ≤ w g * (μ g).restrict (E g) univ := by
        gcongr
        exact Submission.Obl.k4_quadratic_atlas_normalization.sum_measure_assignment_fiber_le
          ((μ g).restrict (E g)) γ V g hV hdisj
      _ = _ := by simp
  calc
    _ = ∑ g, ∑ a ∈ univ.filter (fun a => γ a = g),
        w (γ a) * μ (γ a) (V a ∩ E (γ a)) :=
      (sum_fiberwise univ γ _).symm
    _ ≤ _ := sum_le_sum fun g _ => hfiber g

/-- Retain a candidate exactly when deleting the exceptional event leaves at least
half of its own original witness mass. -/
noncomputable def prunedCandidate {X Γ ι : Type*} [MeasurableSpace X]
    (μ : Γ → Measure X) (γ : ι → Γ) (V : ι → Set X) (E : Γ → Set X) (a : ι) : Set X :=
  if μ (γ a) (V a ∩ E (γ a)) ≤ ENNReal.ofReal ((μ (γ a) (V a)).toReal / 2)
  then V a \ E (γ a) else ∅

theorem prunedCandidate_subset {X Γ ι : Type*} [MeasurableSpace X]
    (μ : Γ → Measure X) (γ : ι → Γ) (V : ι → Set X) (E : Γ → Set X) (a : ι) :
    prunedCandidate μ γ V E a ⊆ V a \ E (γ a) := by
  classical
  unfold prunedCandidate
  split_ifs <;> simp

theorem measurableSet_prunedCandidate {X Γ ι : Type*} [MeasurableSpace X]
    (μ : Γ → Measure X) (γ : ι → Γ) (V : ι → Set X) (E : Γ → Set X) (a : ι)
    (hV : MeasurableSet (V a)) (hE : MeasurableSet (E (γ a))) :
    MeasurableSet (prunedCandidate μ γ V E a) := by
  classical
  unfold prunedCandidate
  split_ifs
  · exact hV.diff hE
  · exact MeasurableSet.empty

/-- Every retained candidate keeps half its original relative mass floor. -/
theorem prunedCandidate_floor {X Γ ι : Type*} [MeasurableSpace X]
    (μ : Γ → Measure X) (γ : ι → Γ) (V : ι → Set X) (E : Γ → Set X) (a : ι)
    (hfin : μ (γ a) (V a) ≠ ⊤)
    (hkeep : μ (γ a) (V a ∩ E (γ a)) ≤ ENNReal.ofReal ((μ (γ a) (V a)).toReal / 2)) :
    ENNReal.ofReal ((μ (γ a) (V a)).toReal / 2) ≤
      μ (γ a) (prunedCandidate μ γ V E a) := by
  rw [prunedCandidate, ite_eq_left hkeep]
  apply Submission.Obl.k4_quadratic_atlas_normalization.retain_half_mass
    (μ (γ a) (V a)) _ _ ((μ (γ a) (V a)).toReal) ENNReal.toReal_nonneg
  · rw [ENNReal.ofReal_toReal hfin]
  · exact (measure_mono (by intro x hx; by_cases h : x ∈ E (γ a) <;> simp_all)).trans
      (measure_union_le (V a \ E (γ a)) (V a ∩ E (γ a)))
  · exact hkeep

theorem prunedCandidate_relative_floor {X Γ ι : Type*} [MeasurableSpace X]
    (μ : Γ → Measure X) (γ : ι → Γ) (V : ι → Set X) (E : Γ → Set X) (a : ι)
    (hfin : μ (γ a) (V a) ≠ ⊤)
    (hkeep : μ (γ a) (V a ∩ E (γ a)) ≤ ENNReal.ofReal ((μ (γ a) (V a)).toReal / 2))
    (m : ENNReal) (hm : m ≤ μ (γ a) (V a)) :
    ENNReal.ofReal (1 / 2 : ℝ) * m ≤ μ (γ a) (prunedCandidate μ γ V E a) := by
  calc
    _ ≤ ENNReal.ofReal (1 / 2 : ℝ) * μ (γ a) (V a) := mul_le_mul' le_rfl hm
    _ = ENNReal.ofReal ((μ (γ a) (V a)).toReal / 2) := by
      conv_lhs => rw [← ENNReal.ofReal_toReal hfin]
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      congr 1
      ring
    _ ≤ _ := prunedCandidate_floor μ γ V E a hfin hkeep

/-- Relative pruning loses at most twice the original weighted exceptional mass,
regardless of the number of candidate labels. -/
theorem weighted_prunedCandidate_cover {X Γ ι : Type*} [MeasurableSpace X]
    [Fintype ι] (μ : Γ → Measure X) (w : Γ → ENNReal)
    (γ : ι → Γ) (V : ι → Set X) (E : Γ → Set X)
    (hfin : ∀ a, μ (γ a) (V a) ≠ ⊤) :
    ∑ a, w (γ a) * μ (γ a) (V a) ≤
      (∑ a, w (γ a) * μ (γ a) (prunedCandidate μ γ V E a)) +
      2 * ∑ a, w (γ a) * μ (γ a) (V a ∩ E (γ a)) := by
  classical
  have hpoint (a : ι) : μ (γ a) (V a) ≤
      μ (γ a) (prunedCandidate μ γ V E a) + 2 * μ (γ a) (V a ∩ E (γ a)) := by
    by_cases hkeep : μ (γ a) (V a ∩ E (γ a)) ≤ ENNReal.ofReal ((μ (γ a) (V a)).toReal / 2)
    · rw [prunedCandidate, ite_eq_left hkeep]
      apply (measure_mono (by intro x hx; by_cases h : x ∈ E (γ a) <;> simp_all)).trans
        ((measure_union_le (V a \ E (γ a)) (V a ∩ E (γ a))).trans ?_)
      gcongr
      exact le_mul_of_one_le_left' (by norm_num : (1 : ENNReal) ≤ 2)
    · rw [prunedCandidate, ite_eq_right hkeep, measure_empty, zero_add]
      have hh := le_of_lt (lt_of_not_ge hkeep)
      calc
        _ = ENNReal.ofReal ((μ (γ a) (V a)).toReal / 2) +
            ENNReal.ofReal ((μ (γ a) (V a)).toReal / 2) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          convert (ENNReal.ofReal_toReal (hfin a)).symm using 1 <;> congr 1 <;> ring
        _ ≤ μ (γ a) (V a ∩ E (γ a)) + μ (γ a) (V a ∩ E (γ a)) := add_le_add hh hh
        _ = _ := (two_mul _).symm
  calc
    _ ≤ ∑ a, w (γ a) *
        (μ (γ a) (prunedCandidate μ γ V E a) + 2 * μ (γ a) (V a ∩ E (γ a))) := by
      gcongr with a
      exact hpoint a
    _ = _ := by
      simp only [mul_add, sum_add_distrib]
      congr 1
      rw [mul_sum]
      apply sum_congr rfl
      intro a _
      ring

/-- A small exceptional mass under the original world laws leaves a half-sized
global floor after relative candidate pruning. -/
theorem weighted_prunedCandidate_floor {X Γ ι : Type*} [MeasurableSpace X]
    [Fintype Γ] [Fintype ι] (μ : Γ → Measure X) (w : Γ → ENNReal)
    (γ : ι → Γ) (V : ι → Set X) (E : Γ → Set X)
    (hV : ∀ a, MeasurableSet (V a))
    (hdisj : ∀ a b, a ≠ b → γ a = γ b → Disjoint (V a) (V b))
    (hfin : ∀ a, μ (γ a) (V a) ≠ ⊤)
    {m : ℝ} (hm : 0 ≤ m)
    (hmass : ENNReal.ofReal m ≤ ∑ a, w (γ a) * μ (γ a) (V a))
    (herr : ∑ g, w g * μ g (E g) ≤ ENNReal.ofReal (m / 4)) :
    ENNReal.ofReal (m / 2) ≤
      ∑ a, w (γ a) * μ (γ a) (prunedCandidate μ γ V E a) := by
  apply Submission.Obl.k4_quadratic_atlas_normalization.retain_half_mass
    _ _ (2 * ∑ a, w (γ a) * μ (γ a) (V a ∩ E (γ a))) m hm hmass
    (weighted_prunedCandidate_cover μ w γ V E hfin)
  calc
    _ ≤ 2 * ENNReal.ofReal (m / 4) := by
      exact mul_le_mul' le_rfl ((weighted_candidate_exception_le μ w γ V E hV hdisj).trans herr)
    _ = ENNReal.ofReal (m / 2) := by
      rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring

end Submission.Obl.k4_fixed_menu_density_pruning
