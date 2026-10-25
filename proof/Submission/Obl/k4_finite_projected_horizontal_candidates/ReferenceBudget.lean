import Mathlib
import Submission.Obl.k4_true_forest_own_depth_preparation.IncidenceBudget

/-! The full true assignments provide a reference budget, independently of the
mass retained by a later residual. -/

namespace Submission.Obl.k4_finite_projected_horizontal_candidates

open MeasureTheory Set

noncomputable section

/-- A finite true family at one depth spends at most the unit reference mass.
This is the accepted incidence-budget lemma, applied to the full cylinders. -/
theorem full_assignment_budget {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (ν : Measure α) [IsProbabilityMeasure ν] (T : ℕ) (j : ι → Fin (2 ^ T))
    (A : ι → Set α) (hA : ∀ i, MeasurableSet (A i))
    (hdisj : ∀ i i', i ≠ i' → j i = j i' → Disjoint (A i) (A i')) :
    (∑ i, ENNReal.ofReal (((2 : ℝ) ^ T)⁻¹) * ν (A i)) ≤ 1 := by
  let I : ι → Set ℝ := fun i => Icc ((j i : ℝ) / (2 : ℝ) ^ T)
    (((j i : ℝ) + 1) / (2 : ℝ) ^ T)
  have hI (i) : I i ⊆ Icc (0 : ℝ) 1 := by
    intro t ht
    have htwo : (0 : ℝ) < 2 ^ T := by positivity
    have hj : (j i : ℝ) + 1 ≤ (2 : ℝ) ^ T := by
      exact_mod_cast (j i).isLt
    exact ⟨(div_nonneg (by positivity) htwo.le).trans ht.1,
      ht.2.trans ((div_le_one htwo).mpr hj)⟩
  have hm (i) : (ν.prod volume) (A i ×ˢ I i) =
      ENNReal.ofReal (((2 : ℝ) ^ T)⁻¹) * ν (A i) := by
    rw [Measure.prod_prod, Real.volume_Icc]
    have heq : ((j i : ℝ) + 1) / (2 : ℝ) ^ T - (j i : ℝ) / (2 : ℝ) ^ T =
        ((2 : ℝ) ^ T)⁻¹ := by ring
    rw [heq, mul_comm]
  have hb := Submission.Obl.k4_true_forest_own_depth_preparation.nested_incidence_budget
    ν T (fun i => (j i : ℕ)) A (fun i => A i ×ˢ I i) (univ ×ˢ Icc (0 : ℝ) 1)
    (fun i => (hA i).prod measurableSet_Icc)
    (fun i i' hne heq => hdisj i i' hne (Fin.ext heq))
    (fun i p hp => hp)
    (fun i p hp => ⟨mem_univ _, hI i hp.2⟩)
  simpa only [hm, Measure.prod_prod, measure_univ, one_mul, Real.volume_Icc,
    sub_zero, ENNReal.ofReal_one] using hb

/-- A measure covered by finitely many events has a member heavy relative to
any positive reference weights with total at most one. Neither the measure
nor its events are renormalized. -/
theorem exists_reference_heavy {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (ρ : Measure X) (E : ι → Set X) (w : ι → ENNReal) (m : ENNReal)
    (hm : m ≠ 0) (hmass : m ≤ ρ univ)
    (hcover : ∀ᵐ x ∂ρ, ∃ i, x ∈ E i) (hbudget : ∑ i, w i ≤ 1) :
    ∃ i, m * w i ≤ ρ (E i) := by
  classical
  have hmass' : m ≤ ∑ i, ρ (E i) := by
    calc
      m ≤ ρ univ := hmass
      _ ≤ ρ (⋃ i, E i) := measure_mono_ae (by
        filter_upwards [hcover] with x hx _
        exact mem_iUnion.mpr hx)
      _ ≤ ∑ i, ρ (E i) := by simpa only [tsum_fintype] using measure_iUnion_le E
  have hn : Nonempty ι := by
    by_contra hn
    haveI : IsEmpty ι := not_nonempty_iff.mp hn
    exact hm (by simpa using hmass')
  haveI := hn
  by_contra hno
  push Not at hno
  have hlt : ∑ i, ρ (E i) < ∑ i, m * w i :=
    ENNReal.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => hno i)
  have hup : ∑ i, m * w i ≤ m := by
    rw [← Finset.mul_sum]
    simpa [mul_comm] using mul_le_mul_left hbudget m
  exact (not_lt_of_ge hmass') (hlt.trans_le hup)

/-- Reference-heavy selection for true labels uses their original assignment
weights. It also works after passing to any dominated residual. -/
theorem exists_heavy_true_label {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (ν : Measure α) [IsProbabilityMeasure ν] (ρ : Measure (α × ℝ))
    (T : ℕ) (j : ι → Fin (2 ^ T)) (A B : ι → Set α)
    (hA : ∀ i, MeasurableSet (A i))
    (hdisj : ∀ i i', i ≠ i' → j i = j i' → Disjoint (A i) (A i'))
    {m : ENNReal} (hm : m ≠ 0) (hmass : m ≤ ρ univ)
    (hcover : ∀ᵐ p ∂ρ, ∃ i, p.1 ∈ B i ∧
      p.2 ∈ Icc ((j i : ℝ) / (2 : ℝ) ^ T) (((j i : ℝ) + 1) / (2 : ℝ) ^ T)) :
    ∃ i, m * (ENNReal.ofReal (((2 : ℝ) ^ T)⁻¹) * ν (A i)) ≤
      ρ (B i ×ˢ Icc ((j i : ℝ) / (2 : ℝ) ^ T) (((j i : ℝ) + 1) / (2 : ℝ) ^ T)) := by
  exact exists_reference_heavy ρ _ _ m hm hmass hcover
    (full_assignment_budget ν T j A hA hdisj)

end
end Submission.Obl.k4_finite_projected_horizontal_candidates
