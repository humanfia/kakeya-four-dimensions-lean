import Submission.Obl.k4_scalar_true_atlas_terminal_lists.Defs
import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.TrueSystem

namespace Submission.Obl.k4_scalar_true_atlas_terminal_lists

open MeasureTheory Set Filter
open scoped ENNReal BigOperators

namespace Exact

variable {p : Data} (hp : Exact p)
include hp

theorem resolution_ge (k : ℕ) : 2 ≤ N p k := hp.1.1 k

theorem resolution_tendsto : Tendsto (N p) atTop atTop := hp.1.2.1

theorem slack_ge (k : ℕ) : 1 ≤ K p k := hp.1.2.2.1.1 k

theorem slack_subpower (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, K p k ≤ N p k ^ ε := hp.1.2.2.1.2 ε hε

theorem length_pos : 0 < L p := hp.1.2.2.2.2.2.1

theorem prior_probability (k : ℕ) (a : Fin (worlds p k)) :
    IsProbabilityMeasure (prior p k a) := (hp.2.1 k).2.2.2.1 a |>.1

theorem prior_coefficients (k : ℕ) (a : Fin (worlds p k)) :
    ∀ᵐ l ∂prior p k a, ∀ e, |l.2 e| ≤ K p k :=
  ((hp.2.1 k).2.2.2.1 a).2.2.1

theorem event_measurable (k : ℕ) (a : Fin (worlds p k)) :
    MeasurableSet (event p k a) := ((hp.2.1 k).2.2.2.1 a).2.2.2.1

theorem event_time (k : ℕ) (a : Fin (worlds p k)) :
    event p k a ⊆ univ ×ˢ Icc (0 : ℝ) 1 :=
  ((hp.2.1 k).2.2.2.1 a).2.2.2.2.1

theorem weight_nonneg (k : ℕ) (a : Fin (worlds p k)) : 0 ≤ weight p k a :=
  (hp.2.1 k).2.1 a

theorem weight_sum (k : ℕ) : ∑ a, weight p k a = 1 :=
  (hp.2.1 k).2.2.1

theorem mass_lower (k : ℕ) :
    ENNReal.ofReal ((K p k)⁻¹) ≤
      ∑ a, ENNReal.ofReal (weight p k a) * mu p k a univ := (hp.2.1 k).2.2.2.2

theorem mu_univ_le (k : ℕ) (a : Fin (worlds p k)) : mu p k a univ ≤ 1 := by
  letI := hp.prior_probability k a
  calc
    _ = ((prior p k a).prod volume) (event p k a) := Measure.restrict_apply_univ _
    _ ≤ ((prior p k a).prod volume) (univ ×ˢ Icc (0 : ℝ) 1) :=
      measure_mono (hp.event_time k a)
    _ = 1 := by simp [Measure.prod_prod]

theorem mu_finite (k : ℕ) (a : Fin (worlds p k)) : IsFiniteMeasure (mu p k a) :=
  ⟨(hp.mu_univ_le k a).trans_lt (by norm_num)⟩

theorem mu_time_null (k : ℕ) (a : Fin (worlds p k)) (t : ℝ) :
    mu p k a (univ ×ˢ {t}) = 0 := by
  letI := hp.prior_probability k a
  apply le_antisymm _ bot_le
  calc
    _ ≤ ((prior p k a).prod volume) (univ ×ˢ {t}) := Measure.restrict_le_self _
    _ = 0 := by simp [Measure.prod_prod]

theorem weighted_mass_le (k : ℕ) :
    ∑ a, ENNReal.ofReal (weight p k a) * mu p k a univ ≤ 1 := by
  calc
    _ ≤ ∑ a, ENNReal.ofReal (weight p k a) * 1 :=
      Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hp.mu_univ_le k a) (by positivity))
    _ = ENNReal.ofReal (∑ a, weight p k a) := by
      simp only [mul_one]
      exact (ENNReal.ofReal_sum_of_nonneg (fun a _ => hp.weight_nonneg k a)).symm
    _ = 1 := by rw [hp.weight_sum]; norm_num

end Exact

noncomputable abbrev observation (p : Data) (k : ℕ) (r : ℝ) : Incidence → Observation :=
  Submission.Obl.k4_scalar_terminal_chart_packet_extraction.obsL (N p k ^ (-r))

theorem observation_measurable (p : Data) (k : ℕ) (r : ℝ) :
    Measurable (observation p k r) :=
  Submission.Obl.k4_scalar_terminal_chart_packet_extraction.measurable_obsL _

theorem Exact.observation_law {p : Data} (hp : Exact p) (k : ℕ)
    (a : Fin (worlds p k)) {r : ℝ} (hr : 0 ≤ r) (hrL : r ≤ L p) :
    Measurable (density p k a r) ∧
      (mu p k a).map (observation p k r) =
        (volume.prod Measure.count).withDensity (density p k a r) :=
  hp.2.2.1 k a r hr hrL

theorem I_subset_unit (T : ℕ) (j : Fin (2 ^ T)) : I T j ⊆ Icc (0 : ℝ) 1 :=
  Submission.Obl.k4_scalar_terminal_chart_packet_extraction.block_subset_unit T j

theorem assigned_incidence_inter_null {p : Data} (hp : Exact p) {k T n : ℕ}
    (γ : Fin n → Fin (worlds p k)) (j : Fin n → Fin (2 ^ T))
    (A : Fin n → Set Trajectory) (C : Fin n → Set Incidence)
    (hdisj : ∀ i i', i ≠ i' → γ i = γ i' → j i = j i' → Disjoint (A i) (A i'))
    (hC : ∀ i, C i ⊆ A i ×ˢ I T (j i)) :
    ∀ i i', i ≠ i' → γ i = γ i' → mu p k (γ i) (C i ∩ C i') = 0 := by
  intro i i' hne hγ
  by_cases hj : j i = j i'
  · have hempty : C i ∩ C i' = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro q hq
      exact Set.disjoint_left.mp (hdisj i i' hne hγ hj) (hC i hq.1).1 (hC i' hq.2).1
    rw [hempty, measure_empty]
  · apply measure_mono_null (inter_subset_inter (hC i) (hC i'))
    exact Submission.Obl.k4_scalar_terminal_chart_packet_extraction.measure_blocks_inter_zero
      (hp.mu_time_null k (γ i)) T hj (A i) (A i')

end Submission.Obl.k4_scalar_true_atlas_terminal_lists
