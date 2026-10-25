import Submission.Obl.k4_coarsened_outer_horizon_composition.Pruning

namespace Submission.Obl.k4_coarsened_outer_horizon_composition

open MeasureTheory Set
open scoped ENNReal

/-- Disjoint assignments inside each world and time block imply multiplicity
at most two, with both closed-interval boundary incidences counted. -/
theorem chart_selected_multiplicity {C W T : ℕ}
    (γ : Fin C → Fin W) (j : Fin C → Fin (2 ^ T))
    (A : Fin C → Set Line) (F : Fin C → Set Inc)
    (hdisj : ∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b'))
    (hsel : ∀ b p, p ∈ F b → p.1 ∈ A b ∧
      p.2 ∈ Icc (((j b : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T))
    (w : Fin W) (p : Inc) :
    (∑ b ∈ Finset.univ.filter (fun b => γ b = w), (F b).indicator (1 : Inc → ℝ≥0∞) p) ≤ 2 := by
  classical
  let s := (Finset.univ.filter (fun b => γ b = w)).filter (fun b => p ∈ F b)
  let t := Finset.univ.filter (fun i : Fin (2 ^ T) =>
    p.2 ∈ Icc ((i : ℕ) / (2 : ℝ) ^ T) (((i : ℕ) + 1) / (2 : ℝ) ^ T))
  have hmap : Set.MapsTo j (s : Set (Fin C)) t := by
    intro b hb
    have hbF := (Finset.mem_filter.mp hb).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hsel b p hbF).2⟩
  have hinj : (s : Set (Fin C)).InjOn j := by
    intro b hb b' hb' hj
    by_contra hne
    have hbγ := (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).2
    have hb'γ := (Finset.mem_filter.mp (Finset.mem_filter.mp hb').1).2
    have hbA := (hsel b p (Finset.mem_filter.mp hb).2).1
    have hb'A := (hsel b' p (Finset.mem_filter.mp hb').2).1
    exact Set.disjoint_left.mp (hdisj b b' hne (hbγ.trans hb'γ.symm) hj) hbA hb'A
  have hcard : s.card ≤ 2 :=
    (Finset.card_le_card_of_injOn j hmap hinj).trans (card_dyadic_intervals_le_two T p.2)
  have heq : (∑ b ∈ Finset.univ.filter (fun b => γ b = w),
      (F b).indicator (1 : Inc → ℝ≥0∞) p) = (s.card : ℝ≥0∞) := by
    simp only [Set.indicator_apply, Pi.one_apply]
    rw [← Finset.sum_filter]
    simp [s]
  rw [heq]
  exact_mod_cast hcard

end Submission.Obl.k4_coarsened_outer_horizon_composition
