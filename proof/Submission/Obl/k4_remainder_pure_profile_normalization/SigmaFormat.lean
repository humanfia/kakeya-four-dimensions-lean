/-
Adapted from this LOT tree, o118, session x0400, commit bd322ee595fd,
Submission/Obl/k4_extremal_profile_setup/SigmaFormat.lean.
-/
import Submission.Obl.k4_remainder_pure_profile_normalization.Definitions

namespace Submission.Obl.k4_remainder_pure_profile_normalization

open Set

theorem sigmaCompact_inter_closed {X : Type*} [TopologicalSpace X] {s t : Set X}
    (hs : IsSigmaCompact s) (ht : IsClosed t) : IsSigmaCompact (s ∩ t) := by
  obtain ⟨K, hK, hKs⟩ := hs
  rw [← hKs, iUnion_inter]
  exact isSigmaCompact_iUnion_of_isCompact _ (fun n => (hK n).inter_right ht)

theorem sigmaCompact_inter {X : Type*} [TopologicalSpace X] [T2Space X] {s t : Set X}
    (hs : IsSigmaCompact s) (ht : IsSigmaCompact t) : IsSigmaCompact (s ∩ t) := by
  obtain ⟨K, hK, hKs⟩ := hs
  obtain ⟨L, hL, hLt⟩ := ht
  rw [← hKs, ← hLt, iUnion_inter]
  apply isSigmaCompact_iUnion
  intro n
  rw [inter_iUnion]
  exact isSigmaCompact_iUnion_of_isCompact _ (fun m => (hK n).inter_right (hL m).isClosed)

/-- Open cuts preserve sigma compactness in a perfectly normal space. -/
theorem sigmaCompact_inter_open {X : Type*} [TopologicalSpace X] [PerfectlyNormalSpace X]
    {s t : Set X} (hs : IsSigmaCompact s) (ht : IsOpen t) : IsSigmaCompact (s ∩ t) := by
  obtain ⟨U, hU, htU⟩ := isGδ_iff_eq_iInter_nat.mp ht.isClosed_compl.isGδ
  have heq : t = ⋃ n, (U n)ᶜ := by rw [← compl_iInter, ← htU, compl_compl]
  rw [heq, inter_iUnion]
  exact isSigmaCompact_iUnion _ (fun n => sigmaCompact_inter_closed hs (hU n).isClosed_compl)

/-- A finite Boolean combination of signs of continuous real functions is a
countable union of compact sets.  This uses no quantifier elimination.
-/
theorem sigmaCompact_bool_signs {X ι : Type*} [TopologicalSpace X] [T2Space X]
    [PerfectlyNormalSpace X] [SigmaCompactSpace X] [Fintype ι]
    (p : ι → X → ℝ) (hp : ∀ i, Continuous (p i)) (b : (ι → Bool) → Bool) :
    IsSigmaCompact {x | b (fun i => decide (0 ≤ p i x)) = true} := by
  classical
  let cell (c : ι → Bool) : Set X := {x | ∀ i, decide (0 ≤ p i x) = c i}
  have hcoord (c : ι → Bool) (i : ι) : IsSigmaCompact {x | decide (0 ≤ p i x) = c i} := by
    cases hc : c i
    · have heq : {x | decide (0 ≤ p i x) = false} = {x | p i x < 0} := by
        ext x
        simp [not_le]
      rw [heq]
      simpa only [univ_inter] using
        sigmaCompact_inter_open (isSigmaCompact_univ (X := X)) (isOpen_lt (hp i) continuous_const)
    · have heq : {x | decide (0 ≤ p i x) = true} = {x | 0 ≤ p i x} := by
        ext x
        simp
      rw [heq]
      exact isSigmaCompact_univ.of_isClosed_subset
        (isClosed_le continuous_const (hp i)) (subset_univ _)
  have hcell (c : ι → Bool) : IsSigmaCompact (cell c) := by
    have hfin (s : Finset ι) : IsSigmaCompact {x | ∀ i ∈ s, decide (0 ≤ p i x) = c i} := by
      induction s using Finset.induction_on with
      | empty => simpa using (isSigmaCompact_univ (X := X))
      | @insert i s hi ih =>
        have heq : {x | ∀ j ∈ insert i s, decide (0 ≤ p j x) = c j} =
            {x | decide (0 ≤ p i x) = c i} ∩ {x | ∀ j ∈ s, decide (0 ≤ p j x) = c j} := by
          ext x
          simp
        rw [heq]
        exact sigmaCompact_inter (hcoord c i) ih
    simpa only [Finset.mem_univ, forall_const, cell] using hfin Finset.univ
  let C := {c : ι → Bool // b c = true}
  have heq : {x | b (fun i => decide (0 ≤ p i x)) = true} = ⋃ c : C, cell c.1 := by
    ext x
    constructor
    · intro hx
      exact mem_iUnion.mpr ⟨⟨fun i => decide (0 ≤ p i x), hx⟩, fun _ => rfl⟩
    · intro hx
      obtain ⟨c, hc⟩ := mem_iUnion.mp hx
      have hc' : (fun i => decide (0 ≤ p i x)) = c.1 := funext hc
      change b (fun i => decide (0 ≤ p i x)) = true
      rw [hc']
      exact c.2
  rw [heq]
  exact isSigmaCompact_iUnion _ (fun c : C => hcell c.1)

theorem fmt_sigmaCompact {n D : ℕ} {H : ℝ} {A : Set (Fin n → ℝ)} (hA : fmt n H D A) :
    IsSigmaCompact A := by
  obtain ⟨m, _, p, _, b, hb⟩ := hA
  have heq : A = {x | b (fun i => decide (0 ≤ MvPolynomial.eval x (p i))) = true} := Set.ext hb
  rw [heq]
  exact sigmaCompact_bool_signs (fun i x => MvPolynomial.eval x (p i))
    (fun i => MvPolynomial.continuous_eval (p i)) b

theorem measurableSet_of_sigmaCompact {X : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] {s : Set X} (hs : IsSigmaCompact s) : MeasurableSet s := by
  obtain ⟨K, hK, hKs⟩ := hs
  rw [← hKs]
  exact MeasurableSet.iUnion (fun n => (hK n).isClosed.measurableSet)

end Submission.Obl.k4_remainder_pure_profile_normalization
