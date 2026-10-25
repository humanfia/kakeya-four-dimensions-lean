import Submission.Obl.k4_balanced_native_packet_transport.Definitions
import Submission.Obl.k4_quadratic_atlas_normalization.AssignmentMass

/-! Disjoint original selections give a global bound before transporting
shared reference probabilities. No number of packets enters this bound. -/
namespace Submission.Obl.k4_balanced_native_packet_transport

open MeasureTheory Set
noncomputable section

/-- Global weighted domination transfers every source null set to every
positive-weight child, including nonmeasurable subsets of null sets. -/
theorem absolutelyContinuous_of_weighted_pullback_domination
    {C C' : ℕ} (parent : Fin C' → Fin C)
    (expand : Fin C' → Inc → Inc) (hexpand : ∀ i, Measurable (expand i))
    (R : Fin C → ENNReal) (μ : Fin C → Measure Inc)
    (R' : Fin C' → ENNReal) (μ' : Fin C' → Measure Inc)
    (hpositive : ∀ i, 0 < R' i)
    (hdom : ∀ A : Fin C → Set Inc, (∀ a, MeasurableSet (A a)) →
      (∑ i, R' i * μ' i (expand i ⁻¹' A (parent i))) ≤
        ∑ a, R a * μ a (A a)) (i : Fin C') :
    Measure.map (expand i) (μ' i) ≪ μ (parent i) := by
  classical
  have hlocal : R' i • Measure.map (expand i) (μ' i) ≤
      R (parent i) • μ (parent i) := by
    apply Measure.le_iff.mpr
    intro S hS
    let A : Fin C → Set Inc := fun a => if a = parent i then S else ∅
    have hA (a : Fin C) : MeasurableSet (A a) := by
      by_cases ha : a = parent i
      · simpa only [A, if_pos ha] using hS
      · simp only [A, if_neg ha, MeasurableSet.empty]
    have hsum := hdom A hA
    have hsingle := Finset.single_le_sum
      (f := fun j => R' j * μ' j (expand j ⁻¹' A (parent j)))
      (fun j _ => bot_le) (Finset.mem_univ i)
    rw [Measure.smul_apply, smul_eq_mul,
      Measure.map_apply (hexpand i) hS, Measure.smul_apply, smul_eq_mul]
    have htotal : (∑ j, R' j * μ' j (expand j ⁻¹' A (parent j))) ≤
        R (parent i) * μ (parent i) S := by
      simpa only [A, apply_ite, measure_empty, mul_ite, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true] using hsum
    have hi : R' i * μ' i (expand i ⁻¹' S) ≤
        ∑ j, R' j * μ' j (expand j ⁻¹' A (parent j)) := by
      simpa only [A, if_pos rfl] using hsingle
    exact hi.trans htotal
  exact (Measure.absolutelyContinuous_smul (hpositive i).ne').trans
    (Measure.absolutelyContinuous_of_le_smul hlocal)

/-- A split of each original law into disjoint selections gives the global
weighted pullback domination used by `WindowCertificate.transport`. -/
theorem weighted_pullback_domination_of_disjoint
    {C C' : ℕ} (parent : Fin C' → Fin C)
    (expand : Fin C' → Inc → Inc) (hexpand : ∀ i, Measurable (expand i))
    (R : Fin C → ENNReal) (μ : Fin C → Measure Inc)
    (R' : Fin C' → ENNReal) (μ' : Fin C' → Measure Inc)
    (B : Fin C' → Set Inc) (hB : ∀ i, MeasurableSet (B i))
    (hdisj : ∀ i i', i ≠ i' → parent i = parent i' → Disjoint (B i) (B i'))
    (hbound : ∀ i, R' i • Measure.map (expand i) (μ' i) ≤
      R (parent i) • (μ (parent i)).restrict (B i)) :
    ∀ A : Fin C → Set Inc, (∀ a, MeasurableSet (A a)) →
      (∑ i, R' i * μ' i (expand i ⁻¹' A (parent i))) ≤
        ∑ a, R a * μ a (A a) := by
  classical
  intro A hA
  rw [← Finset.sum_fiberwise Finset.univ parent]
  apply Finset.sum_le_sum
  intro a _
  calc
    (∑ i ∈ Finset.univ.filter (fun i => parent i = a),
        R' i * μ' i (expand i ⁻¹' A (parent i))) ≤
        ∑ i ∈ Finset.univ.filter (fun i => parent i = a),
          R a * ((μ a).restrict (A a)) (B i) := by
      apply Finset.sum_le_sum
      intro i hi
      have heq := (Finset.mem_filter.mp hi).2
      have hh := hbound i (A a)
      rw [Measure.smul_apply, smul_eq_mul,
        Measure.map_apply (hexpand i) (hA a), Measure.smul_apply, smul_eq_mul,
        Measure.restrict_apply (hA a), heq] at hh
      rw [heq, Measure.restrict_apply (hB i), inter_comm (B i) (A a)]
      exact hh
    _ = R a * ∑ i ∈ Finset.univ.filter (fun i => parent i = a),
        ((μ a).restrict (A a)) (B i) := (Finset.mul_sum _ _ _).symm
    _ ≤ R a * μ a (A a) := by
      apply mul_le_mul' le_rfl
      simpa only [Measure.restrict_apply_univ] using
        Submission.Obl.k4_quadratic_atlas_normalization.sum_measure_assignment_fiber_le
          ((μ a).restrict (A a)) parent B a hB hdisj

end
end Submission.Obl.k4_balanced_native_packet_transport
