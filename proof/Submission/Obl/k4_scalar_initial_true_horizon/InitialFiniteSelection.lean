import Submission.Obl.k4_scalar_initial_true_horizon.InitialCellCount
import Submission.Obl.k4_scalar_initial_true_horizon.FiniteCardBound

/-! Finite enumeration of initial cells from their original mass floor. -/

namespace Submission.Obl.k4_scalar_initial_true_horizon

open MeasureTheory Set
open scoped ENNReal BigOperators

theorem initial_cell_count_fintype {p : Data} (hp : Exact p) {k T : ℕ}
    {ι : Type*} [Fintype ι] (γ : ι → Fin (worlds p k)) (j : ι → Fin (2 ^ T))
    (A : ι → Set Trajectory) (hA : ∀ i, MeasurableSet (A i))
    (hdisj : ∀ i i', i ≠ i' → γ i = γ i' → j i = j i' → Disjoint (A i) (A i'))
    {η : ℝ} (hη : 0 < η)
    (hfloor : ∀ i, ENNReal.ofReal η ≤ mu p k (γ i) (A i ×ˢ I T (j i))) :
    (Fintype.card ι : ℝ) ≤ (worlds p k : ℝ) / η := by
  classical
  let e := Fintype.equivFin ι
  exact initial_cell_count_le hp (fun i => γ (e.symm i)) (fun i => j (e.symm i))
    (fun i => A (e.symm i)) (fun i => hA (e.symm i))
    (fun i i' hne hγ hj => hdisj _ _ (fun he => hne (e.symm.injective he)) hγ hj)
    hη (fun i => hfloor (e.symm i))

/-- A family of maximal good cells is finite as soon as all its members have
one positive original mass floor. No coordinate box needs to be enumerated. -/
theorem finite_initial_assignment_family {p : Data} (hp : Exact p) {k T : ℕ}
    {ι : Type*} (S : Set ι) (γ : ι → Fin (worlds p k)) (j : ι → Fin (2 ^ T))
    (A : ι → Set Trajectory) (hA : ∀ i ∈ S, MeasurableSet (A i))
    (hdisj : ∀ i ∈ S, ∀ i' ∈ S, i ≠ i' → γ i = γ i' → j i = j i' → Disjoint (A i) (A i'))
    {η : ℝ} (hη : 0 < η)
    (hfloor : ∀ i ∈ S, ENNReal.ofReal η ≤ mu p k (γ i) (A i ×ˢ I T (j i))) : S.Finite := by
  classical
  apply finite_of_uniform_finset_card_bound S ((worlds p k : ℝ) / η)
  intro F hFS
  have hbound := initial_cell_count_fintype hp
    (fun i : F => γ i) (fun i : F => j i) (fun i : F => A i)
    (fun i => hA i (hFS i.property)) (by
      intro i i' hne hγ hj
      exact hdisj i (hFS i.property) i' (hFS i'.property)
        (fun he => hne (Subtype.ext he)) hγ hj)
    hη (fun i => hfloor i (hFS i.property))
  simpa only [Fintype.card_coe] using hbound

end Submission.Obl.k4_scalar_initial_true_horizon
