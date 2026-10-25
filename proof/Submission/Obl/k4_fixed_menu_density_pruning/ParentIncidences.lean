-- Adapted from this LOT tree, o194, session x0674, commit 182d9543,
-- Submission/Obl/k4_greedy_cover_graph_atlas/ParentIncidences.lean.

import Submission.Obl.k4_fixed_menu_density_pruning.Interface
import Submission.Obl.k4_finite_forest_width_selection.ForestCombinatorics
import Submission.Obl.k4_scalar_pair_atlas_assembly.Dyadic

namespace Submission.Obl.k4_fixed_menu_density_pruning

open Set Submission.Obl.k4_finite_forest_width_selection

/-- Incidences and their original world persist up the actual path forest. -/
theorem forestAncestor_incidence_subset {C : ℕ} {X Γ : Type*}
    (lev : Fin C → ℕ) (par : Fin C → Fin C) (γ : Fin C → Γ) (F : Fin C → Set X)
    (hlev : ∀ b, 0 < lev b → lev (par b) + 1 = lev b)
    (hγ : ∀ b, 0 < lev b → γ (par b) = γ b)
    (hF : ∀ b, 0 < lev b → F b ⊆ F (par b))
    (b : Fin C) (i : ℕ) (hi : i ≤ lev b) :
    γ (forestAncestor lev par b i) = γ b ∧ F b ⊆ F (forestAncestor lev par b i) := by
  have aux : ∀ n (b : Fin C), lev b = n → i ≤ n →
      γ (forestAncestor lev par b i) = γ b ∧ F b ⊆ F (forestAncestor lev par b i) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro b hbn hin
      by_cases heq : i = lev b
      · rw [heq, forestAncestor_self]
        exact ⟨rfl, subset_rfl⟩
      · have hb : 0 < lev b := by omega
        have hp := hlev b hb
        have hpl : lev (par b) < n := by omega
        have hip : i ≤ lev (par b) := by omega
        obtain ⟨hworld, hsub⟩ := ih (lev (par b)) hpl (par b) rfl hip
        rw [forestAncestor_parent hlev b hb i hip] at hworld hsub
        exact ⟨hworld.trans (hγ b hb), (hF b hb).trans hsub⟩
  exact aux (lev b) b rfl hi

/-- An interior point of a uniform time cell belongs to no other closed time cell. -/
theorem time_cell_unique {a b : ℕ} {q t : ℝ} (hq : 0 < q)
    (ha : t ∈ Ioo ((a : ℝ) / q) (((a : ℝ) + 1) / q))
    (hb : t ∈ Icc ((b : ℝ) / q) (((b : ℝ) + 1) / q)) : a = b := by
  rcases lt_trichotomy a b with h | h | h
  · have hcast : (a : ℝ) + 1 ≤ b := by exact_mod_cast h
    have hcut := div_le_div_of_nonneg_right hcast hq.le
    linarith [ha.2, hb.1]
  · exact h
  · have hcast : (b : ℝ) + 1 ≤ a := by exact_mod_cast h
    have hcut := div_le_div_of_nonneg_right hcast hq.le
    linarith [hb.2, ha.1]

/-- A terminal incidence assigned to an old packet's lines in the interior of that
packet's time block is an incidence of the old packet itself. -/
theorem incidence_mem_old_packet {C : ℕ} {X Γ : Type*}
    (lev : Fin C → ℕ) (par : Fin C → Fin C) (γ : Fin C → Γ) (j : Fin C → ℕ)
    (T : ℕ → ℕ) (A : Fin C → Set X) (F : Fin C → Set (X × ℝ))
    (hlev : ∀ b, 0 < lev b → lev (par b) + 1 = lev b)
    (hγ : ∀ b, 0 < lev b → γ (par b) = γ b)
    (hFpar : ∀ b, 0 < lev b → F b ⊆ F (par b))
    (hF : ∀ b, ∀ p ∈ F b, p.1 ∈ A b ∧
      p.2 ∈ Icc ((j b : ℝ) / (2 : ℝ) ^ T (lev b))
        (((j b : ℝ) + 1) / (2 : ℝ) ^ T (lev b)))
    (hAdisj : ∀ b b', b ≠ b' → lev b = lev b' → γ b = γ b' → j b = j b' →
      Disjoint (A b) (A b'))
    {b old : Fin C} {p : X × ℝ}
    (hi : lev old ≤ lev b) (hworld : γ b = γ old) (hp : p ∈ F b)
    (hpA : p.1 ∈ A old)
    (hpt : p.2 ∈ Ioo ((j old : ℝ) / (2 : ℝ) ^ T (lev old))
      (((j old : ℝ) + 1) / (2 : ℝ) ^ T (lev old))) : p ∈ F old := by
  let a := forestAncestor lev par b (lev old)
  have halev : lev a = lev old := forestAncestor_level hlev b (lev old) hi
  obtain ⟨haγ, hsub⟩ := forestAncestor_incidence_subset lev par γ F hlev hγ hFpar b (lev old) hi
  have hpa : p ∈ F a := hsub hp
  obtain ⟨hpaA, hpat⟩ := hF a p hpa
  rw [halev] at hpat
  have haj : j old = j a := time_cell_unique (by positivity) hpt hpat
  have hae : a = old := by
    by_contra hne
    exact Set.disjoint_left.mp (hAdisj a old hne halev (haγ.trans hworld) haj.symm) hpaA hpA
  simpa only [hae] using hpa


/-- The time coordinate avoids each fixed endpoint under the original product law. -/
theorem ae_time_ne {X : Type*} [MeasurableSpace X] (ν : MeasureTheory.Measure X) (t : ℝ) :
    ∀ᵐ p : X × ℝ ∂ν.prod MeasureTheory.volume, p.2 ≠ t := by
  rw [MeasureTheory.ae_iff]
  simpa only [not_not] using
    Submission.Obl.k4_scalar_pair_atlas_assembly.time_singleton_null ν t

/-- Restricting a supported incidence set to the interior of its time block preserves mass. -/
theorem measure_trim_to_interior {X : Type*} [MeasurableSpace X]
    (ν : MeasureTheory.Measure X) (V : Set (X × ℝ)) (ta tb : ℝ)
    (hV : ∀ p ∈ V, p.2 ∈ Icc ta tb) :
    (ν.prod MeasureTheory.volume) (V ∩ {p | p.2 ∈ Ioo ta tb}) =
      (ν.prod MeasureTheory.volume) V := by
  apply MeasureTheory.measure_congr
  filter_upwards [ae_time_ne ν ta, ae_time_ne ν tb] with p hpa hpb
  apply propext
  constructor
  · exact fun h => h.1
  · intro hp
    obtain ⟨hlo, hhi⟩ := hV p hp
    exact ⟨hp, lt_of_le_of_ne hlo hpa.symm, lt_of_le_of_ne hhi hpb⟩

end Submission.Obl.k4_fixed_menu_density_pruning
