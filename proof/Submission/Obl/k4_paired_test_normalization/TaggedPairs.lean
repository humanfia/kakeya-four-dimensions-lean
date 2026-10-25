-- Adapted from this LOT tree, o156, session x0524, commit86ade225;
-- Submission/Obl/k4_terminal_local_sheet_pairing/TaggedPairs.lean. Existing attribution comments are retained below.

import Mathlib

/-! The finite tagged-law formula generalizes this tree's accepted o165
`Selection.taggedLaw_apply` to arbitrary original world measures and pair masks.
The row, column and marginal identities below are developed here. -/

namespace Submission.Obl.k4_paired_test_normalization

open MeasureTheory Set

variable {Γ Ω ι : Type*} [Fintype Γ] [MeasurableSpace Γ]
  [MeasurableSingletonClass Γ] [MeasurableSpace Ω]

/-- A finite sum of the unchanged world laws, each carrying its own world tag. -/
noncomputable def taggedPairMeasure (μ : Γ → Measure Ω) (a : Γ → ℝ) : Measure (Γ × Ω) :=
  ∑ γ, ENNReal.ofReal (a γ) • (μ γ).map (fun p => (γ, p))

theorem taggedPairMeasure_apply (μ : Γ → Measure Ω) (a : Γ → ℝ)
    {A : Set (Γ × Ω)} (hA : MeasurableSet A) :
    taggedPairMeasure μ a A =
      ∑ γ, ENNReal.ofReal (a γ) * μ γ ((fun p => (γ, p)) ⁻¹' A) := by
  simp only [taggedPairMeasure, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro γ _
  rw [Measure.map_apply
    (show Measurable (fun p : Ω => (γ, p)) from measurable_const.prodMk measurable_id) hA]

theorem taggedPairMeasure_slice (μ : Γ → Measure Ω) (a : Γ → ℝ)
    (γ : Γ) {A : Set Ω} (hA : MeasurableSet A) :
    taggedPairMeasure μ a ({γ} ×ˢ A) = ENNReal.ofReal (a γ) * μ γ A := by
  classical
  rw [taggedPairMeasure_apply μ a ((measurableSet_singleton γ).prod hA)]
  have hpre (γ' : Γ) : (fun p : Ω => (γ', p)) ⁻¹' ({γ} ×ˢ A) =
      if γ' = γ then A else ∅ := by
    ext p
    simp only [mem_preimage, mem_prod, mem_singleton_iff]
    split_ifs <;> simp_all
  simp only [hpre]
  rw [Finset.sum_eq_single γ]
  · simp
  · intro γ' _ hne
    simp [hne]
  · simp

/-- Pair masks use the source entry's world; nonempty masks have a common world. -/
def tagPair (world : ι → Γ) (H : ι → ι → Set Ω) (i j : ι) : Set (Γ × Ω) :=
  {world i} ×ˢ H i j

theorem measurableSet_tagPair (world : ι → Γ) (H : ι → ι → Set Ω)
    (hH : ∀ i j, MeasurableSet (H i j)) (i j : ι) :
    MeasurableSet (tagPair world H i j) :=
  (measurableSet_singleton _).prod (hH i j)

theorem tagPair_row (world : ι → Γ) (H : ι → ι → Set Ω) (i : ι) :
    (⋃ j, tagPair world H i j) = {world i} ×ˢ (⋃ j, H i j) := by
  ext p
  simp only [tagPair, mem_iUnion, mem_prod, mem_singleton_iff]
  aesop

theorem tagPair_column (world : ι → Γ) (H : ι → ι → Set Ω)
    (hworld : ∀ i j p, p ∈ H i j → world i = world j) (j : ι) :
    (⋃ i, tagPair world H i j) = {world j} ×ˢ (⋃ i, H i j) := by
  ext p
  simp only [tagPair, mem_iUnion, mem_prod, mem_singleton_iff]
  constructor
  · rintro ⟨i, hγ, hi⟩
    exact ⟨hγ.trans (hworld i j p.2 hi), i, hi⟩
  · rintro ⟨hγ, i, hi⟩
    exact ⟨i, hγ.trans (hworld i j p.2 hi).symm, hi⟩

theorem tagPair_active (world : ι → Γ) (H : ι → ι → Set Ω)
    (hworld : ∀ i j p, p ∈ H i j → world i = world j) (i : ι) :
    ((⋃ j, tagPair world H i j) ∪ (⋃ j, tagPair world H j i)) =
      {world i} ×ˢ ((⋃ j, H i j) ∪ (⋃ j, H j i)) := by
  rw [tagPair_row, tagPair_column world H hworld]
  ext p
  simp only [mem_union, mem_prod]
  tauto

theorem tagPair_disjoint_columns (world : ι → Γ) (H : ι → ι → Set Ω)
    (hdisj : ∀ j i k, i ≠ k → world i = world k → Disjoint (H i j) (H k j)) :
    ∀ j, Pairwise fun i k => Disjoint (tagPair world H i j) (tagPair world H k j) := by
  intro j i k hik
  apply Set.disjoint_left.mpr
  rintro p ⟨hγi, hi⟩ ⟨hγk, hk⟩
  have heq : world i = world k := hγi.symm.trans hγk
  exact Set.disjoint_left.mp (hdisj j i k hik heq) hi hk

theorem tagPair_row_mass [Fintype ι] (μ : Γ → Measure Ω) (a : Γ → ℝ)
    (world : ι → Γ) (H : ι → ι → Set Ω) (hH : ∀ i j, MeasurableSet (H i j)) (i : ι) :
    taggedPairMeasure μ a (⋃ j, tagPair world H i j) =
      ENNReal.ofReal (a (world i)) * μ (world i) (⋃ j, H i j) := by
  rw [tagPair_row, taggedPairMeasure_slice μ a _ (MeasurableSet.iUnion (hH i))]

/-- Both roles obey the same original-world base-density rule. -/
theorem taggedPairMeasure_base_density (μ : Γ → Measure Ω) (a : Γ → ℝ)
    (ha : ∀ γ, 0 ≤ a γ) {X : Type*} [MeasurableSpace X]
    (m : Measure X) (γ : Γ) (S : Set Ω) (hS : MeasurableSet S)
    (z : Ω → X) (hz : Measurable z) (β : ℝ)
    (hden : ∀ A : Set X, MeasurableSet A →
      μ γ (S ∩ z ⁻¹' A) ≤ ENNReal.ofReal β * m A)
    {A : Set X} (hA : MeasurableSet A) :
    taggedPairMeasure μ a (({γ} ×ˢ S) ∩ (fun p : Γ × Ω => z p.2) ⁻¹' A) ≤
      ENNReal.ofReal (a γ * β) * m A := by
  have heq : (({γ} ×ˢ S) ∩ (fun p : Γ × Ω => z p.2) ⁻¹' A) =
      {γ} ×ˢ (S ∩ z ⁻¹' A) := by
    ext p
    simp only [mem_inter_iff, mem_prod, mem_preimage]
    exact and_assoc
  rw [heq, taggedPairMeasure_slice μ a γ (hS.inter (hA.preimage hz)),
    ENNReal.ofReal_mul (ha γ), mul_assoc]
  gcongr
  exact hden A hA

/-- Pulling retained masks back to their source world exactly reverses tagging
whenever they are subsets of the original tagged masks. -/
theorem tagPair_pullback (world : ι → Γ) (H : ι → ι → Set Ω)
    (K : ι → ι → Set (Γ × Ω)) (hK : ∀ i j, K i j ⊆ tagPair world H i j) :
    ∀ i j, tagPair world (fun i j => (fun p => (world i, p)) ⁻¹' K i j) i j = K i j := by
  intro i j
  ext p
  constructor
  · rintro ⟨hγ, hp⟩
    have hγ' : p.1 = world i := hγ
    have heq : (world i, p.2) = p := Prod.ext hγ'.symm rfl
    exact heq ▸ hp
  · intro hp
    have hγ : p.1 = world i := (hK i j hp).1
    refine ⟨hγ, ?_⟩
    have heq : (world i, p.2) = p := Prod.ext hγ.symm rfl
    exact heq.symm ▸ hp

theorem tagPair_pullback_row_mass [Fintype ι] (μ : Γ → Measure Ω) (a : Γ → ℝ)
    (world : ι → Γ) (H : ι → ι → Set Ω) (K : ι → ι → Set (Γ × Ω))
    (hKm : ∀ i j, MeasurableSet (K i j))
    (hK : ∀ i j, K i j ⊆ tagPair world H i j) (i : ι) :
    taggedPairMeasure μ a (⋃ j, K i j) = ENNReal.ofReal (a (world i)) *
      μ (world i) (⋃ j, (fun p => (world i, p)) ⁻¹' K i j) := by
  have hmeas (i j : ι) : MeasurableSet ((fun p => (world i, p)) ⁻¹' K i j) :=
    (hKm i j).preimage (measurable_const.prodMk measurable_id)
  have hmass := tagPair_row_mass μ a world
    (fun i j => (fun p => (world i, p)) ⁻¹' K i j) hmeas i
  simpa only [tagPair_pullback world H K hK] using hmass

end Submission.Obl.k4_paired_test_normalization
