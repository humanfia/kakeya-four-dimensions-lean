import Submission.Obl.k4_horizon_light_cell_mass.Anisotropic
import Submission.Obl.k4_horizon_light_cell_mass.Observation

namespace Submission.Obl.k4_horizon_light_cell_mass

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_native_base_flattening

/-- The polynomial Boolean format occurring in the frozen hypotheses. -/
def BooleanFormat (n : ℕ) (H : ℝ) (D : ℕ) (A : Set (Fin n → ℝ)) : Prop :=
  ∃ m : ℕ, (m : ℝ) ≤ H ∧ ∃ p : Fin m → MvPolynomial (Fin n) ℝ,
    (∀ j, (p j).totalDegree ≤ D) ∧ ∃ b : (Fin m → Bool) → Bool,
      ∀ x, x ∈ A ↔ b (fun j => decide (0 ≤ MvPolynomial.eval x (p j))) = true

/-- Only the prior and event format is needed to produce the raw source density. -/
theorem exists_formatted_source (n : ℝ) (M D : ℕ) (hn : 2 ≤ n)
    (ν : Measure (ℕ × (Fin 6 → ℝ))) (E : Set State)
    (hν : ∃ m : ℕ, (m : ℝ) ≤ n ^ M ∧ ∃ (c : Fin m → ℝ)
      (i : Fin m → ℕ) (A : Fin m → Set (Fin 6 → ℝ)),
      (∀ j, 0 ≤ c j ∧ c j ≤ n ^ M ∧ (i j : ℝ) ≤ n ^ M ∧
        BooleanFormat 6 (n ^ M) D (A j) ∧ ∀ x ∈ A j, ∀ b, |x b| ≤ n ^ M) ∧
      ν = ∑ j, ENNReal.ofReal (c j) • Measure.map (fun x => (i j, x)) (volume.restrict (A j)))
    (hE : MeasurableSet E) (hEsub : E ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1)
    (hEf : ∀ i, BooleanFormat 7 (n ^ M) D (eventFiber E i)) :
    ∃ f : Raw → ℝ, NativeMixtureFormat n M D f ∧ Measurable f ∧
      (∀ x, 0 ≤ f x) ∧ (∀ x, |f x| ≤ n ^ (2 * M)) ∧
      ((ν.prod volume).restrict E).map rawChart = volume.withDensity (fun x => ENNReal.ofReal (f x)) := by
  classical
  obtain ⟨m, hm, c, i, A, hj, hν⟩ := hν
  have hA : ∀ j, MeasurableSet (A j) := by
    intro j
    obtain ⟨m, hm, p, hp, b, hb⟩ := (hj j).2.2.2.1
    exact measurableSet_of_polynomial_description _ p b hb
  have hB : ∀ j, MeasurableSet (eventFiber E (i j)) := by
    intro j
    obtain ⟨m, hm, p, hp, b, hb⟩ := hEf (i j)
    exact measurableSet_of_polynomial_description _ p b hb
  let f : Raw → ℝ := fun x => ∑ j, nativeComponentDensity (c j) (A j) (eventFiber E (i j)) x
  have hf0 : ∀ x, 0 ≤ f x := fun x => Finset.sum_nonneg fun j _ =>
    (nativeComponentDensity_bound _ (hj j).1 _ _ x).1
  refine ⟨f, ?_, Finset.measurable_sum _ (fun j _ =>
    nativeComponentDensity_measurable _ _ _ (hA j) (hB j)), hf0, ?_, ?_⟩
  · refine ⟨m, c, A, fun j => eventFiber E (i j), hm,
      fun j => ⟨(hj j).1, (hj j).2.1⟩, fun j => (hj j).2.2.2.1,
      fun j => hEf (i j), fun j => (hj j).2.2.2.2, ?_, rfl⟩
    intro j x hx
    exact (hEsub hx).2
  · intro x
    rw [abs_of_nonneg (hf0 x)]
    calc
      _ ≤ ∑ _j : Fin m, n ^ M := by
        apply Finset.sum_le_sum
        intro j _
        exact ((le_abs_self _).trans (nativeComponentDensity_bound _ (hj j).1 _ _ x).2).trans
          (hj j).2.1
      _ = (m : ℝ) * n ^ M := by simp
      _ ≤ n ^ M * n ^ M := mul_le_mul_of_nonneg_right hm (by positivity)
      _ = n ^ (2 * M) := by rw [← pow_add]; congr 1; omega
  · exact rawChart_law c (fun j => (hj j).1) i A hA ν hν E hE

end Submission.Obl.k4_horizon_light_cell_mass
