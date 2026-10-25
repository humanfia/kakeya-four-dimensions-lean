import Submission.Obl.k4_scalar_candidate_original_return.Fits

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

open Set MeasureTheory
open Submission.Lib.K4FinitePlankAtlases

noncomputable section

def fitAssignment {w : ℕ} (a : Layer w) (ε : ℝ) (m : Fin a.n → ℕ)
    (P : (i : Fin a.n) → Fin (m i) → Poly) (i : Fin a.n) (j : Fin (m i)) : Set Line :=
  a.prior i ∩ firstAssignment (fun h => Fit (P i h)
    (((a.time i : ℕ) : ℝ) / (2 : ℝ) ^ a.T)
    ((((a.time i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ a.T) ε) j

def mergedFitAssignment {w n : ℕ} (a : Layer w) (ε : ℝ) (m : Fin a.n → ℕ)
    (P : (i : Fin a.n) → Fin (m i) → Poly)
    (bin : (i : Fin a.n) → Fin (m i) → Fin n) (j : Fin n) : Set Line :=
  {l | ∃ i h, bin i h = j ∧ l ∈ fitAssignment a ε m P i h}

lemma mergedFitAssignment_subset {w n : ℕ} (a : Layer w) (ε : ℝ) (m : Fin a.n → ℕ)
    (P : (i : Fin a.n) → Fin (m i) → Poly)
    (parent : Fin n → Fin a.n) (bin : (i : Fin a.n) → Fin (m i) → Fin n)
    (hparent : ∀ i h, parent (bin i h) = i) (j : Fin n) :
    mergedFitAssignment a ε m P bin j ⊆ a.prior (parent j) := by
  rintro l ⟨i, h, hbin, hl⟩
  have hi : parent j = i := by simpa only [hbin] using hparent i h
  simpa only [hi] using hl.1

lemma mergedFitAssignment_siblings_disjoint {w n : ℕ} (a : Layer w) (ε : ℝ)
    (m : Fin a.n → ℕ) (P : (i : Fin a.n) → Fin (m i) → Poly)
    (parent : Fin n → Fin a.n) (bin : (i : Fin a.n) → Fin (m i) → Fin n)
    (hparent : ∀ i h, parent (bin i h) = i) (j j' : Fin n)
    (hne : j ≠ j') (hsame : parent j = parent j') :
    Disjoint (mergedFitAssignment a ε m P bin j)
      (mergedFitAssignment a ε m P bin j') := by
  apply Set.disjoint_left.mpr
  rintro l ⟨i, h, hbin, hl⟩ ⟨i', h', hbin', hl'⟩
  have hi : parent j = i := by simpa only [hbin] using hparent i h
  have hi' : parent j' = i' := by simpa only [hbin'] using hparent i' h'
  have hii' : i = i' := hi.symm.trans (hsame.trans hi')
  cases hii'
  have hhh : h ≠ h' := by
    intro hh
    apply hne
    exact hbin.symm.trans (hh ▸ hbin')
  exact Set.disjoint_left.mp (firstAssignment_disjoint
    (fun u => Fit (P i u) (((a.time i : ℕ) : ℝ) / (2 : ℝ) ^ a.T)
      ((((a.time i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ a.T) ε) hhh) hl.2 hl'.2

lemma mergedFitAssignment_measurable {w n : ℕ} (a : Layer w) (ε : ℝ)
    (m : Fin a.n → ℕ) (P : (i : Fin a.n) → Fin (m i) → Poly)
    (bin : (i : Fin a.n) → Fin (m i) → Fin n)
    (hA : ∀ i, MeasurableSet (a.prior i)) (j : Fin n) :
    MeasurableSet (mergedFitAssignment a ε m P bin j) := by
  have heq : mergedFitAssignment a ε m P bin j = ⋃ i, ⋃ h : Fin (m i),
      if bin i h = j then fitAssignment a ε m P i h else ∅ := by
    ext l
    simp [mergedFitAssignment]
  rw [heq]
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.iUnion
  intro h
  split
  · exact (hA i).inter (measurableSet_firstAssignment _
      (fun h => (Fit_closed _ _ _ _).measurableSet) h)
  · exact MeasurableSet.empty

/-- Merging any subset of sibling priority fits has a quadratic atom-count
bound and degree four, independent of every analytic list selector. -/
lemma mergedFitAssignment_format {w n : ℕ} (a : Layer w) (ε : ℝ)
    (m : Fin a.n → ℕ) (P : (i : Fin a.n) → Fin (m i) → Poly)
    (parent : Fin n → Fin a.n) (bin : (i : Fin a.n) → Fin (m i) → Fin n)
    (hparent : ∀ i h, parent (bin i h) = i)
    (hP : ∀ i h, (P i h).totalDegree ≤ 2)
    {B : ℝ} {D : ℕ} (hB : 1 ≤ B)
    (hA : ∀ i z, Format 5 B D {v | (z, v) ∈ a.prior i}) (j : Fin n) (z : ℕ) :
    Format 5 (B + (m (parent j) : ℝ) * (12 * ((m (parent j) : ℝ) + 1))) (max D 4)
      {v | (z, v) ∈ mergedFitAssignment a ε m P bin j} := by
  classical
  let i := parent j
  let U : Fin (m i) → Set (Fin 5 → ℝ) := fun h => if bin i h = j then
    {v | (z, v) ∈ firstAssignment (fun u => Fit (P i u)
      (((a.time i : ℕ) : ℝ) / (2 : ℝ) ^ a.T)
      ((((a.time i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ a.T) ε) h} else ∅
  have hsize : 1 ≤ 12 * ((m i : ℝ) + 1) := by
    have hm : 0 ≤ (m i : ℝ) := Nat.cast_nonneg _
    linarith
  have hU (h : Fin (m i)) : Format 5 (12 * ((m i : ℝ) + 1)) 4 (U h) := by
    dsimp only [U]
    split
    · apply priority_Fit_format (P i) (hP i)
      exact (div_le_div_iff_of_pos_right (by positivity)).mpr (by linarith)
    · exact k4_scalar_conditional_crop_worlds.Format.empty 5 (by positivity) 4
  have hUnion := k4_scalar_conditional_crop_worlds.Format.iUnion_fin
    (by linarith : 0 ≤ 12 * ((m i : ℝ) + 1)) (m i) U hU
  have hf := k4_scalar_conditional_crop_worlds.Format.inter
    (k4_scalar_conditional_crop_worlds.Format.mono (hA i z) le_rfl (le_max_left D 4))
    (k4_scalar_conditional_crop_worlds.Format.mono hUnion le_rfl (le_max_right D 4))
  have heq : {v | (z, v) ∈ mergedFitAssignment a ε m P bin j} =
      {v | (z, v) ∈ a.prior i} ∩ ⋃ h, U h := by
    ext v
    constructor
    · rintro ⟨i', h, hbin, hl⟩
      have hi : i = i' := by simpa only [i, hbin] using hparent i' h
      subst i'
      exact ⟨hl.1, mem_iUnion.mpr ⟨h, by simpa [U, hbin] using hl.2⟩⟩
    · rintro ⟨hA, hU⟩
      obtain ⟨h, hh⟩ := mem_iUnion.mp hU
      by_cases hb : bin i h = j
      · exact ⟨i, h, hb, hA, by simpa [U, hb] using hh⟩
      · simpa [U, hb] using hh
  rw [heq]
  exact hf

end

end Submission.Obl.k4_scalar_candidate_original_return
