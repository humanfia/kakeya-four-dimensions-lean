/- Adapted from this LOT tree, o078, session x0260, commit 34c7136a25cd.
   Original file: Submission/Lib/K4ExactMeasureTools/SparseEntryPruning.lean -/
/-
Adapted from: here:o078
-/
import Submission.Obl.k4_scalar_grid_parameter_preparation.StrongPruning

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

open MeasureTheory

/-- The entry-threshold budget counts physical cells separately in each
original prior block, rather than using the global physical cell count. -/
theorem sparse_prior_entry_threshold_sum {α κ ι : Type*}
    [MeasurableSpace α] [Fintype κ] [DecidableEq ι]
    (ν : Measure α) (A : κ → Set α) (hA : ∀ j, MeasurableSet (A j))
    (hdisj : Pairwise fun j j' => Disjoint (A j) (A j'))
    (Q : κ → Finset ι) (a B : ENNReal) (hQ : ∀ j, ((Q j).card : ENNReal) ≤ B) :
    (∑ x : (j : κ) × ↥(Q j), a * ν (A x.1)) ≤ a * B * ν Set.univ := by
  classical
  have hprior : (∑ j, ν (A j)) ≤ ν Set.univ := by
    calc
      _ = ν (⋃ j, A j) := by rw [measure_iUnion hdisj hA, tsum_fintype]
      _ ≤ _ := measure_mono (Set.subset_univ _)
  rw [Fintype.sum_sigma]
  calc
    _ = ∑ j, ((Q j).card : ENNReal) * (a * ν (A j)) := by simp
    _ ≤ ∑ j, B * (a * ν (A j)) := Finset.sum_le_sum (fun j _ => by
      simpa only [mul_comm] using mul_le_mul_right (hQ j) (a * ν (A j)))
    _ = (a * B) * ∑ j, ν (A j) := by
      simp_rw [show ∀ j, B * (a * ν (A j)) = (a * B) * ν (A j) by intro j; ring]
      exact (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_right hprior (a * B)

/-- Simultaneous entry floors are charged to the original prior and to a
sparse cover for each prior block. Entries may overlap arbitrarily. -/
theorem sparse_prior_entry_pruning {Ω α κ ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [Fintype κ] [DecidableEq ι]
    (μ : Measure Ω) (ν : Measure α) (A : κ → Set α)
    (hA : ∀ j, MeasurableSet (A j))
    (hdisj : Pairwise fun j j' => Disjoint (A j) (A j'))
    (Q : κ → Finset ι) (C : κ → ι → Set Ω)
    (hC : ∀ j, ∀ i ∈ Q j, MeasurableSet (C j i))
    (a B : ENNReal) (hQ : ∀ j, ((Q j).card : ENNReal) ≤ B)
    {E : Set Ω} (hE : MeasurableSet E) :
    ∃ R : Set Ω, MeasurableSet R ∧ R ⊆ E ∧
      μ (E \ R) ≤ a * B * ν Set.univ ∧
      ∀ j, ∀ i ∈ Q j, R ∩ C j i = ∅ ∨ a * ν (A j) < μ (R ∩ C j i) := by
  classical
  let T := (j : κ) × ↥(Q j)
  have hsum := sparse_prior_entry_threshold_sum ν A hA hdisj Q a B hQ
  obtain ⟨R, hR, hsub, hloss, hfloor⟩ := exists_measurable_current_floor_pruning μ
    (fun x : T => C x.1 x.2.val) (fun x : T => a * ν (A x.1))
    (fun x : T => hC x.1 x.2.val x.2.property) hE
  refine ⟨R, hR, hsub, hloss.trans hsum, ?_⟩
  intro j i hi
  exact hfloor ⟨j, ⟨i, hi⟩⟩

/-- One restriction restores entry floors at every width of a finite grid.
The original prior is unchanged, and all floors refer to the same FINAL law. -/
theorem multiscale_sparse_prior_entry_pruning {Ω α σ ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [Fintype σ] [DecidableEq ι]
    (κ : σ → Type*) [∀ s, Fintype (κ s)]
    (μ : Measure Ω) (ν : Measure α) (A : (s : σ) → κ s → Set α)
    (hA : ∀ s j, MeasurableSet (A s j))
    (hdisj : ∀ s, Pairwise fun j j' => Disjoint (A s j) (A s j'))
    (Q : (s : σ) → κ s → Finset ι) (C : (s : σ) → κ s → ι → Set Ω)
    (hC : ∀ s j, ∀ i ∈ Q s j, MeasurableSet (C s j i))
    (a B : σ → ENNReal) (hQ : ∀ s j, ((Q s j).card : ENNReal) ≤ B s)
    {E : Set Ω} (hE : MeasurableSet E) :
    ∃ R : Set Ω, MeasurableSet R ∧ R ⊆ E ∧
      μ (E \ R) ≤ (∑ s, a s * B s) * ν Set.univ ∧
      ∀ s j, ∀ i ∈ Q s j, R ∩ C s j i = ∅ ∨
        a s * ν (A s j) < μ (R ∩ C s j i) := by
  classical
  let T := (s : σ) × (j : κ s) × ↥(Q s j)
  have hsum : (∑ x : T, a x.1 * ν (A x.1 x.2.1)) ≤
      (∑ s, a s * B s) * ν Set.univ := by
    rw [Fintype.sum_sigma]
    calc
      _ ≤ ∑ s, (a s * B s) * ν Set.univ := Finset.sum_le_sum (fun s _ =>
        sparse_prior_entry_threshold_sum ν (A s) (hA s) (hdisj s) (Q s) (a s) (B s) (hQ s))
      _ = _ := (Finset.sum_mul _ _ _).symm
  obtain ⟨R, hR, hsub, hloss, hfloor⟩ := exists_measurable_current_floor_pruning μ
    (fun x : T => C x.1 x.2.1 x.2.2.val)
    (fun x : T => a x.1 * ν (A x.1 x.2.1))
    (fun x : T => hC x.1 x.2.1 x.2.2.val x.2.2.property) hE
  refine ⟨R, hR, hsub, hloss.trans hsum, ?_⟩
  intro s j i hi
  exact hfloor ⟨s, j, ⟨i, hi⟩⟩

/-- Extra fine-cell floors and every finite-grid entry floor are restored
simultaneously, so renewal of either family cannot invalidate the other. -/
theorem multiscale_sparse_prior_entry_pruning_with_floors {Ω α σ ι ζ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [Fintype σ] [DecidableEq ι] [Fintype ζ]
    (κ : σ → Type*) [∀ s, Fintype (κ s)]
    (μ : Measure Ω) (ν : Measure α) (A : (s : σ) → κ s → Set α)
    (hA : ∀ s j, MeasurableSet (A s j))
    (hdisj : ∀ s, Pairwise fun j j' => Disjoint (A s j) (A s j'))
    (Q : (s : σ) → κ s → Finset ι) (C : (s : σ) → κ s → ι → Set Ω)
    (hC : ∀ s j, ∀ i ∈ Q s j, MeasurableSet (C s j i))
    (a B : σ → ENNReal) (hQ : ∀ s j, ((Q s j).card : ENNReal) ≤ B s)
    (F : ζ → Set Ω) (hF : ∀ i, MeasurableSet (F i)) (θ : ζ → ENNReal)
    {E : Set Ω} (hE : MeasurableSet E) :
    ∃ R : Set Ω, MeasurableSet R ∧ R ⊆ E ∧
      μ (E \ R) ≤ (∑ i, θ i) + (∑ s, a s * B s) * ν Set.univ ∧
      (∀ i, R ∩ F i = ∅ ∨ θ i < μ (R ∩ F i)) ∧
      ∀ s j, ∀ i ∈ Q s j, R ∩ C s j i = ∅ ∨
        a s * ν (A s j) < μ (R ∩ C s j i) := by
  classical
  let T := (s : σ) × (j : κ s) × ↥(Q s j)
  have hsum : (∑ x : T, a x.1 * ν (A x.1 x.2.1)) ≤
      (∑ s, a s * B s) * ν Set.univ := by
    rw [Fintype.sum_sigma]
    calc
      _ ≤ ∑ s, (a s * B s) * ν Set.univ := Finset.sum_le_sum (fun s _ =>
        sparse_prior_entry_threshold_sum ν (A s) (hA s) (hdisj s) (Q s) (a s) (B s) (hQ s))
      _ = _ := (Finset.sum_mul _ _ _).symm
  obtain ⟨R, hR, hsub, hloss, hfloor⟩ := exists_measurable_current_floor_pruning μ
    (Sum.elim F (fun x : T => C x.1 x.2.1 x.2.2.val))
    (Sum.elim θ (fun x : T => a x.1 * ν (A x.1 x.2.1)))
    (by
      intro x
      rcases x with i | x
      · exact hF i
      · exact hC x.1 x.2.1 x.2.2.val x.2.2.property) hE
  refine ⟨R, hR, hsub, ?_, ?_, ?_⟩
  · rw [Fintype.sum_sum_type] at hloss
    exact hloss.trans (add_le_add le_rfl hsum)
  · intro i
    exact hfloor (Sum.inl i)
  · intro s j i hi
    exact hfloor (Sum.inr ⟨s, j, ⟨i, hi⟩⟩)

end Submission.Obl.k4_scalar_grid_parameter_preparation
