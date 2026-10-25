import Submission.Lib.K4RepresentativeAssembly.FiniteFormat

/-!
Adapted from: here:o114 (session x0383).

Geometric assignments obtained from a fixed source-to-bin table. Their
disjointness comes from the original source sections, and their polynomial
format comes from finite lookup and geometric intersection.
-/

namespace Submission.Lib.K4RepresentativeAssembly

open Set MeasureTheory

def mergedSources {X β : Type*} [DecidableEq β] {m : ℕ}
    (S : Fin m → Set X) (tag : Fin m → β) (G : β → Set X) (b : β) : Set X :=
  (⋃ s, if tag s = b then S s else ∅) ∩ G b

theorem mem_mergedSources {X β : Type*} [DecidableEq β] {m : ℕ}
    (S : Fin m → Set X) (tag : Fin m → β) (G : β → Set X) (b : β) (x : X) :
    x ∈ mergedSources S tag G b ↔
      (∃ s, tag s = b ∧ x ∈ S s) ∧ x ∈ G b := by
  simp [mergedSources]

/-- A frozen analytic success belongs to the geometrically defined assignment
once its selected source bin and geometric conditions agree. -/
theorem source_mem_mergedSources {X β : Type*} [DecidableEq β] {m : ℕ}
    (S : Fin m → Set X) (tag : Fin m → β) (G : β → Set X)
    {s : Fin m} {x : X} (hx : x ∈ S s) (hG : x ∈ G (tag s)) :
    x ∈ mergedSources S tag G (tag s) :=
  (mem_mergedSources S tag G (tag s) x).mpr ⟨⟨s, rfl, hx⟩, hG⟩

/-- Merging source identities into bin labels preserves disjointness of the
trajectory assignments within a world and a coarse time block. -/
theorem mergedSources_pairwise {X β : Type*} [DecidableEq β] {m : ℕ}
    (S : Fin m → Set X) (tag : Fin m → β) (G : β → Set X)
    (hS : Pairwise (fun s t => Disjoint (S s) (S t))) :
    Pairwise (fun b c => Disjoint (mergedSources S tag G b) (mergedSources S tag G c)) := by
  intro b c hbc
  apply Set.disjoint_left.mpr
  intro x hxb hxc
  obtain ⟨⟨s, hsb, hxs⟩, _⟩ := (mem_mergedSources S tag G b x).mp hxb
  obtain ⟨⟨t, htc, hxt⟩, _⟩ := (mem_mergedSources S tag G c x).mp hxc
  by_cases hst : s = t
  · subst t
    exact hbc (hsb.symm.trans htc)
  · exact Set.disjoint_left.mp (hS hst) hxs hxt

theorem measurableSet_mergedSources {X β : Type*} [MeasurableSpace X]
    [DecidableEq β] {m : ℕ} (S : Fin m → Set X) (tag : Fin m → β) (G : β → Set X)
    (hS : ∀ s, MeasurableSet (S s)) (hG : ∀ b, MeasurableSet (G b)) (b : β) :
    MeasurableSet (mergedSources S tag G b) := by
  unfold mergedSources
  apply MeasurableSet.inter _ (hG b)
  apply MeasurableSet.iUnion
  intro s
  split_ifs
  · exact hS s
  · exact MeasurableSet.empty

/-- All analytical masks have been discarded from the assignment predicate.
Only original finite-format source sections and the geometric tests remain. -/
theorem fmt_mergedSources {β : Type*} [DecidableEq β] {n m D D' : ℕ}
    {H H' : ℝ} (S : Fin m → Set (Fin n → ℝ)) (tag : Fin m → β)
    (G : β → Set (Fin n → ℝ)) (hH : 0 ≤ H)
    (hS : ∀ s, fmt n H D (S s)) (hG : ∀ b, fmt n H' D' (G b)) (b : β) :
    fmt n ((m : ℝ) * H + H') (max D D') (mergedSources S tag G b) :=
  fmt_inter (fmt_selected_iUnion S tag b hH hS) (hG b)

end Submission.Lib.K4RepresentativeAssembly
