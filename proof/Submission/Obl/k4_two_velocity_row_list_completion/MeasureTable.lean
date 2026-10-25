import Mathlib

open MeasureTheory Set
open scoped BigOperators ENNReal Classical

namespace Submission.Obl.k4_two_velocity_row_list_completion

/-- A nonzero state has a large set of compatible palette bins, even if its
incidence mass is arbitrarily small. Good incidences alone define compatibility. -/
theorem degree_of_conditional_cap {Ω Q R V : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (position : Ω → Q) (row : Ω → R) (code : Ω → V) (good : Ω → Prop)
    (velocities : Finset V) (weight : V → ℝ) {K : ℝ} (hK : 0 < K)
    (hw : ∀ j ∈ velocities, 0 ≤ weight j)
    (hcode : ∀ p, code p ∈ velocities) (hgood : ∀ᵐ p ∂μ, good p)
    (q : Q) (r : R) (hmass : μ {p | position p = q ∧ row p = r} ≠ 0)
    (hcap : ∀ j ∈ velocities,
      μ {p | position p = q ∧ row p = r ∧ code p = j} ≤
        ENNReal.ofReal K * ENNReal.ofReal (weight j) *
          μ {p | position p = q ∧ row p = r}) :
    1 / K ≤ ∑ j ∈ velocities,
      if (∃ p, good p ∧ position p = q ∧ row p = r ∧ code p = j)
      then weight j else 0 := by
  classical
  let state : Set Ω := {p | position p = q ∧ row p = r}
  let entry (j : V) : Set Ω := {p | position p = q ∧ row p = r ∧ code p = j}
  let compatible (j : V) : Prop :=
    ∃ p, good p ∧ position p = q ∧ row p = r ∧ code p = j
  have hcover : state = ⋃ j ∈ velocities, entry j := by
    ext p
    constructor
    · intro hp
      exact mem_iUnion₂.mpr ⟨code p, hcode p, hp.1, hp.2, rfl⟩
    · intro hp
      obtain ⟨j, hj, hp⟩ := mem_iUnion₂.mp hp
      exact ⟨hp.1, hp.2.1⟩
  have hentry (j : V) (hj : j ∈ velocities) :
      μ.real (entry j) ≤ K * (if compatible j then weight j else 0) * μ.real state := by
    by_cases hjgood : compatible j
    · have h := ENNReal.toReal_mono (by finiteness) (hcap j hj)
      simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_ofReal hK.le,
        ENNReal.toReal_ofReal (hw j hj), ite_eq_left hjgood] using h
    · have hnull : μ (entry j) = 0 := by
        apply measure_mono_null (t := {p | ¬good p}) _ (ae_iff.mp hgood)
        intro p hp hgp
        exact hjgood ⟨p, hgp, hp.1, hp.2.1, hp.2.2⟩
      simp [Measure.real, hnull, hjgood]
  have hmpos : 0 < μ.real state := ENNReal.toReal_pos hmass (by finiteness)
  have hsum : μ.real state ≤ K *
      (∑ j ∈ velocities, if compatible j then weight j else 0) * μ.real state := by
    calc
      μ.real state = μ.real (⋃ j ∈ velocities, entry j) := by rw [hcover]
      _ ≤ ∑ j ∈ velocities, μ.real (entry j) := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ j ∈ velocities,
          K * (if compatible j then weight j else 0) * μ.real state :=
        Finset.sum_le_sum hentry
      _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hdegree : 1 ≤ K *
      (∑ j ∈ velocities, if compatible j then weight j else 0) := by
    apply (mul_le_mul_iff_left₀ hmpos).mp
    nlinarith [hsum]
  apply (div_le_iff₀ hK).mpr
  simpa only [mul_comm] using hdegree

/-- Almost every observation lies in a positive-mass atom of any countable record. -/
theorem ae_record_mass_ne_zero {Ω X : Type*} [MeasurableSpace Ω] [Countable X]
    (μ : Measure Ω) (record : Ω → X) :
    ∀ᵐ p ∂μ, μ {p' | record p' = record p} ≠ 0 := by
  have h (x : X) : ∀ᵐ p ∂μ, record p = x → μ {p' | record p' = x} ≠ 0 := by
    by_cases hx : μ {p' | record p' = x} = 0
    · have hp : ∀ᵐ p ∂μ, record p ≠ x := by simpa [ae_iff] using hx
      exact hp.mono fun p hp heq => (hp heq).elim
    · exact Filter.Eventually.of_forall fun _ _ => hx
  filter_upwards [ae_all_iff.mpr h] with p hp
  exact hp (record p) rfl

/-- The finite list of states with positive mass above one position record. -/
noncomputable def positiveStates {Ω Q R : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (position : Ω → Q) (row : Ω → R) (allowed : Finset R) (q : Q) :
    Finset R :=
  allowed.filter fun r => μ {p | position p = q ∧ row p = r} ≠ 0

theorem ae_mem_positiveStates {Ω Q R : Type*} [MeasurableSpace Ω]
    [Countable Q] [Countable R] (μ : Measure Ω)
    (position : Ω → Q) (row : Ω → R) (allowed : Finset R)
    (hallowed : ∀ᵐ p ∂μ, row p ∈ allowed) :
    ∀ᵐ p ∂μ, row p ∈ positiveStates μ position row allowed (position p) := by
  filter_upwards [hallowed, ae_record_mass_ne_zero μ (fun p => (position p, row p))]
    with p hp hm
  exact Finset.mem_filter.mpr ⟨hp, by simpa only [Prod.mk.injEq] using hm⟩

end Submission.Obl.k4_two_velocity_row_list_completion
