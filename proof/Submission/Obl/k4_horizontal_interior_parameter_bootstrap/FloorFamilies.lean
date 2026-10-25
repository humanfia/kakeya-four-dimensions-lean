/- Adapted from this LOT tree, obligation o217, session x0759, commit
   d88f8140fd7bca1d67d8c8d75c99e651c40b587f, file
   Submission/Obl/k4_horizontal_endpoint_parameter_bootstrap/EndpointFloors.lean.
   The simultaneous-floor kernel is imported from its accepted library version. -/
import Submission.Lib.K4FullTimeLayers.Floors
import Submission.Obl.k4_scalar_normalized_exact_refinement.PositiveWorlds

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap

open MeasureTheory Set
open Submission.Lib.K4FullTimeLayers
open scoped ENNReal
open Submission.Obl.k4_scalar_normalized_exact_refinement.WorldSelection

/-- Deleting null labels from a finite covering family preserves its full support. -/
theorem positive_family_cover {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (A : ι → Set Ω)
    (hcover : μ {p | ∃ i, p ∈ A i}ᶜ = 0) :
    μ {p | ∃ j : Fin (positiveCount (fun i => μ (A i))),
      p ∈ A (positiveEmbedding (fun i => μ (A i)) j)}ᶜ = 0 := by
  classical
  let e := positiveEmbedding (fun i => μ (A i))
  let Bad : Set Ω := ⋃ i : ι, if i ∉ range e then A i else ∅
  have hbad : μ Bad = 0 := by
    apply measure_iUnion_null
    intro i
    by_cases hi : i ∉ range e
    · rw [ite_eq_left hi]
      exact mass_zero_off_positive (fun i => μ (A i)) i hi
    · rw [ite_eq_right hi]
      exact measure_empty
  have hsub : {p | ∃ j, p ∈ A (e j)}ᶜ ⊆ {p | ∃ i, p ∈ A i}ᶜ ∪ Bad := by
    intro p hp
    by_cases ho : ∃ i, p ∈ A i
    · right
      obtain ⟨i, hi⟩ := ho
      have hir : i ∉ range e := by
        rintro ⟨j, rfl⟩
        exact hp ⟨j, hi⟩
      exact mem_iUnion.mpr ⟨i, by simp only [ite_eq_left hir]; exact hi⟩
    · exact Or.inl ho
  apply measure_mono_null hsub
  exact measure_union_null hcover hbad

/-- One common restriction and one finite subfamily per layer have all floors
and all coverages at once. Labels are retained only when their final mass is positive. -/
theorem exists_common_floored_families {Ω J : Type*} [MeasurableSpace Ω] [Fintype J]
    {ι : J → Type*} [∀ j, Fintype (ι j)]
    (μ : Measure Ω) (A : (j : J) → ι j → Set Ω)
    (hA : ∀ j i, MeasurableSet (A j i))
    (w : (j : J) → ι j → ℝ≥0∞) (m : ℝ≥0∞)
    (hcover : ∀ j, μ {p | ∃ i, p ∈ A j i}ᶜ = 0)
    (hbudget : m + ∑ j, ∑ i, w j i < μ univ) :
    ∃ (ρ : Measure Ω) (n : J → ℕ) (e : (j : J) → Fin (n j) ↪ ι j),
      ρ ≤ μ ∧ m ≤ ρ univ ∧
      (∀ j i, 0 < ρ (A j (e j i)) ∧ w j (e j i) ≤ ρ (A j (e j i))) ∧
      ∀ j, ρ {p | ∃ i, p ∈ A j (e j i)}ᶜ = 0 := by
  classical
  obtain ⟨ρ, hρ, hmass, hfloors⟩ := exists_common_floor_submeasure μ
    (fun z : Sigma ι => A z.1 z.2) (fun z => hA z.1 z.2)
    (fun z => w z.1 z.2)
  rw [Fintype.sum_sigma] at hmass
  have hlower : m ≤ ρ univ := by
    by_contra hm
    have hsmall : ρ univ ≤ m := (lt_of_not_ge hm).le
    have hcontra : μ univ < μ univ :=
      hmass.trans_lt ((add_le_add hsmall le_rfl).trans_lt hbudget)
    exact (lt_irrefl _ hcontra)
  let n : J → ℕ := fun j => positiveCount (fun i => ρ (A j i))
  let e : (j : J) → Fin (n j) ↪ ι j :=
    fun j => positiveEmbedding (fun i => ρ (A j i))
  refine ⟨ρ, n, e, hρ, hlower, ?_, ?_⟩
  · intro j i
    have hpos : 0 < ρ (A j (e j i)) := positiveEmbedding_pos (fun i => ρ (A j i)) i
    refine ⟨hpos, ?_⟩
    rcases hfloors ⟨j, e j i⟩ with hz | hw
    · exact (hpos.ne' hz).elim
    · exact hw
  · intro j
    apply positive_family_cover
    exact le_antisymm ((hρ _).trans_eq (hcover j)) bot_le

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap
