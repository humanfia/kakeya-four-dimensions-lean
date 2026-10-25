/- Adapted from this LOT tree, obligation o260, session x0919, commit 57638ddd7c07709143f61bbedd02efd72974929b,
   Submission/Obl/k4_contact_shifted_quadratic_candidates/UniformPalette.lean. Original attribution comments are retained below. -/
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.AffinePalette

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open Set MeasureTheory

noncomputable section

/-- Pad variable entry counts to one positive count. The loss is at most a
factor two in the palette bound, and every original entry is retained exactly. -/
theorem exists_uniform_palette_count
    {H : Type*} (n M : H → ℕ) (L : (h : H) → Fin (n h) → Fin (M h) → Fin 4 → ℝ)
    {C : ℝ} (hC : 1 ≤ C) (hM : ∀ h, (M h : ℝ) ≤ C) :
    ∃ (M' : ℕ) (L' : (h : H) → Fin (n h) → Fin M' → Fin 4 → ℝ),
      1 ≤ M' ∧ (M' : ℝ) ≤ 2 * C ∧
      ∀ h i u, ∃ u', L' h i u' = L h i u := by
  classical
  let M' : ℕ := max 1 ⌈C⌉₊
  have hle (h : H) : M h ≤ M' := by
    have hh : (M h : ℝ) ≤ (⌈C⌉₊ : ℝ) := (hM h).trans (Nat.le_ceil C)
    exact (by exact_mod_cast hh : M h ≤ ⌈C⌉₊).trans (le_max_right _ _)
  let L' : (h : H) → Fin (n h) → Fin M' → Fin 4 → ℝ := fun h i u =>
    if hu : u.val < M h then L h i ⟨u.val, hu⟩ else 0
  refine ⟨M', L', le_max_left _ _, ?_, ?_⟩
  · dsimp only [M']
    rw [Nat.cast_max, Nat.cast_one]
    apply max_le
    · linarith
    · have hh := Nat.ceil_lt_add_one (show 0 ≤ C by linarith)
      linarith
  · intro h i u
    refine ⟨u.castLE (hle h), ?_⟩
    simp only [L', Fin.val_castLE, dite_eq_left u.isLt]

/-- The common success set of a finite list of affine palettes. -/
def finitePaletteSource {α H : Type*} [Fintype H]
    (b : α → Fin 6 → ℝ) (n M : H → ℕ)
    (B : (h : H) → Fin (n h) → Set α)
    (L : (h : H) → Fin (n h) → Fin (M h) → Fin 4 → ℝ)
    (left right : (h : H) → Fin (n h) → ℝ) (error : H → ℝ) : Set (α × ℝ) :=
  ⋂ h, ⋃ i, ⋃ u, (B h i ∩ affineBlockFit b (L h i u) (left h i) (right h i) (error h)) ×ˢ
    Icc (left h i) (right h i)

theorem measurableSet_finitePaletteSource {α H : Type*} [MeasurableSpace α] [Fintype H]
    (b : α → Fin 6 → ℝ) (hb : Measurable b) (n M : H → ℕ)
    (B : (h : H) → Fin (n h) → Set α) (hB : ∀ h i, MeasurableSet (B h i))
    (L : (h : H) → Fin (n h) → Fin (M h) → Fin 4 → ℝ)
    (left right : (h : H) → Fin (n h) → ℝ) (error : H → ℝ)
    (hlr : ∀ h i, left h i ≤ right h i) :
    MeasurableSet (finitePaletteSource b n M B L left right error) := by
  apply MeasurableSet.iInter
  intro h
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.iUnion
  intro u
  exact ((hB h i).inter (measurableSet_affineBlockFit b hb (L h i u) (hlr h i))).prod
    measurableSet_Icc

/-- Padding the entry tables can only enlarge their common success set. -/
theorem finitePaletteSource_mono_entries {α H : Type*} [Fintype H]
    (b : α → Fin 6 → ℝ) (n M M' : H → ℕ)
    (B : (h : H) → Fin (n h) → Set α)
    (L : (h : H) → Fin (n h) → Fin (M h) → Fin 4 → ℝ)
    (L' : (h : H) → Fin (n h) → Fin (M' h) → Fin 4 → ℝ)
    (left right : (h : H) → Fin (n h) → ℝ) (error : H → ℝ)
    (hentries : ∀ h i u, ∃ u', L' h i u' = L h i u) :
    finitePaletteSource b n M B L left right error ⊆
      finitePaletteSource b n M' B L' left right error := by
  intro p hp
  apply mem_iInter.mpr
  intro h
  obtain ⟨i, hi⟩ := mem_iUnion.mp (mem_iInter.mp hp h)
  obtain ⟨u, hu⟩ := mem_iUnion.mp hi
  obtain ⟨u', heq⟩ := hentries h i u
  exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨u', by simpa only [heq] using hu⟩⟩

end

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
