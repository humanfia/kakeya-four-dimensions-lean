-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_two_scale_flat_box_estimate.Fibers.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.BalancedAssignments
import Submission.WZ.Obl.wz_tower_balanced_refinement.Reindex

namespace WangZahlLot.Obl.wz_two_scale_flat_box_estimate

open Set
open WangZahlLot.Obl.wz_tower_balanced_refinement
  (enumerate enumerate_mem enumerate_injective exists_enumerate)

noncomputable def fiberSet {n N : ℕ} (f : Fin n → Fin N) (k : Fin N) : Finset (Fin n) :=
  Finset.univ.filter (fun i => f i = k)

noncomputable def fiberSize {n N : ℕ} (f : Fin n → Fin N) (k : Fin N) : ℕ :=
  (fiberSet f k).card

noncomputable def fiberIndex {n N : ℕ} (f : Fin n → Fin N) (k : Fin N) : Fin (fiberSize f k) → Fin n :=
  enumerate (fiberSet f k)

lemma fiberIndex_injective {n N : ℕ} (f : Fin n → Fin N) (k : Fin N) :
    Function.Injective (fiberIndex f k) := enumerate_injective _

@[simp] lemma fiberIndex_spec {n N : ℕ} (f : Fin n → Fin N) (k : Fin N)
    (i : Fin (fiberSize f k)) : f (fiberIndex f k i) = k := by
  exact (Finset.mem_filter.mp (enumerate_mem (fiberSet f k) i)).2

lemma exists_fiberIndex {n N : ℕ} (f : Fin n → Fin N) {k : Fin N} {i : Fin n} (hi : f i = k) :
    ∃ j, fiberIndex f k j = i :=
  exists_enumerate (fiberSet f k) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)

lemma fiberIndex_count {n N : ℕ} (f : Fin n → Fin N) (k : Fin N) (P : Fin n → Prop) :
    Set.ncard {i | P (fiberIndex f k i)} = Set.ncard {i | f i = k ∧ P i} := by
  have he : fiberIndex f k '' {i | P (fiberIndex f k i)} = {i | f i = k ∧ P i} := by
    ext i
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨fiberIndex_spec f k j, hj⟩
    · intro hi
      obtain ⟨j, rfl⟩ := exists_fiberIndex f hi.1
      exact ⟨j, hi.2, rfl⟩
  rw [← he, Set.ncard_image_of_injective _ (fiberIndex_injective f k)]

lemma fiberSize_eq {n N : ℕ} (f : Fin n → Fin N) (k : Fin N) :
    fiberSize f k = Set.ncard {i | f i = k} := by
  simp [fiberSize, fiberSet, Set.ncard_eq_toFinset_card']

/-- Reindexing a composite fiber gives a canonical map to its parent fiber. -/
noncomputable def fiberParent {n N L : ℕ} (f : Fin n → Fin N) (g : Fin N → Fin L)
    (k : Fin L) (i : Fin (fiberSize (g ∘ f) k)) : Fin (fiberSize g k) :=
  (fiberSet g k).equivFin ⟨f (fiberIndex (g ∘ f) k i),
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, fiberIndex_spec (g ∘ f) k i⟩⟩

@[simp] lemma fiberParent_spec {n N L : ℕ} (f : Fin n → Fin N) (g : Fin N → Fin L)
    (k : Fin L) (i : Fin (fiberSize (g ∘ f) k)) :
    fiberIndex g k (fiberParent f g k i) = f (fiberIndex (g ∘ f) k i) := by
  simp [fiberIndex, fiberParent, WangZahlLot.Obl.wz_tower_balanced_refinement.enumerate]

lemma parent_fiber_budget {n N L : ℕ} (hN : 0 < N) (f : Fin n → Fin N) (g : Fin N → Fin L)
    {D F : ℝ} (hD : 0 ≤ D)
    (hf : ∀ k k', (Set.ncard {i | f i = k} : ℝ) ≤ D * Set.ncard {i | f i = k'})
    (hg : ∀ k, (Set.ncard {i | g (f i) = k} : ℝ) ≤ D ^ 3 * F) :
    (∀ k, (Set.ncard {i | f i = k} : ℝ) ≤ D * n / N) ∧
      ∀ k, (D * n / N) * Set.ncard {j | g j = k} ≤ D ^ 5 * F := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  constructor
  · intro k
    apply (le_div_iff₀ hN').mpr
    simpa only [mul_comm (Set.ncard {i | f i = k} : ℝ) (N : ℝ)] using
      (balanced_assignment_bounds f hf k).1
  · intro k
    have hh := (composition_fiber_bounds f g hf k).2
    have hh' := mul_le_mul_of_nonneg_left hh hD
    have htop := mul_le_mul_of_nonneg_left (hg k) (by positivity : 0 ≤ D ^ 2 * N)
    apply (mul_le_mul_iff_left₀ hN').mp
    have he : (D * n / N) * (Set.ncard {j | g j = k} : ℝ) * N =
        D * ((n : ℝ) * Set.ncard {j | g j = k}) := by field_simp
    rw [he]
    nlinarith only [hh', htop]

end WangZahlLot.Obl.wz_two_scale_flat_box_estimate
