-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.ShadingAtoms.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open MeasureTheory Set
open scoped Classical

noncomputable section

/-- The finite measurable partition determined by shading membership. The empty
pattern is excluded by restricting every atom to the original union. -/
def shadingAtom {X ι : Type*} [Fintype ι] (Y : ι → Set X) (A : Finset ι) : Set X :=
  (⋃ i, Y i) ∩ {p | ∀ i, p ∈ Y i ↔ i ∈ A}

def shadingPattern {X ι : Type*} [Fintype ι] (Y : ι → Set X) (p : X) : Finset ι :=
  Finset.univ.filter fun i => p ∈ Y i

theorem mem_shadingPattern {X ι : Type*} [Fintype ι] (Y : ι → Set X) (p : X) (i : ι) :
    i ∈ shadingPattern Y p ↔ p ∈ Y i := by simp [shadingPattern]

theorem mem_shadingAtom_pattern {X ι : Type*} [Fintype ι] {Y : ι → Set X} {p : X}
    (hp : p ∈ ⋃ i, Y i) : p ∈ shadingAtom Y (shadingPattern Y p) :=
  ⟨hp, fun i => (mem_shadingPattern Y p i).symm⟩

theorem shadingAtom_eq_pattern {X ι : Type*} [Fintype ι] {Y : ι → Set X}
    {A : Finset ι} {p : X} (hp : p ∈ shadingAtom Y A) : A = shadingPattern Y p := by
  ext i
  exact (hp.2 i).symm.trans (mem_shadingPattern Y p i).symm

theorem shadingAtom_measurable {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    {Y : ι → Set X} (hY : ∀ i, MeasurableSet (Y i)) (A : Finset ι) :
    MeasurableSet (shadingAtom Y A) := by
  apply (MeasurableSet.iUnion hY).inter
  have he : {p | ∀ i, p ∈ Y i ↔ i ∈ A} = ⋂ i, if i ∈ A then Y i else (Y i)ᶜ := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    apply forall_congr'
    intro i
    split_ifs <;> simp_all
  rw [he]
  apply MeasurableSet.iInter
  intro i
  split_ifs
  · exact hY i
  · exact (hY i).compl

theorem shadingAtom_disjoint {X ι : Type*} [Fintype ι] (Y : ι → Set X) :
    Pairwise (fun A B => Disjoint (shadingAtom Y A) (shadingAtom Y B)) := by
  intro A B hAB
  apply Set.disjoint_left.mpr
  intro p hpA hpB
  exact hAB ((shadingAtom_eq_pattern hpA).trans (shadingAtom_eq_pattern hpB).symm)

theorem shadingAtom_iUnion {X ι : Type*} [Fintype ι] (Y : ι → Set X) :
    (⋃ A, shadingAtom Y A) = ⋃ i, Y i := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset fun _ => Set.inter_subset_left
  · intro p hp
    exact Set.mem_iUnion.mpr ⟨shadingPattern Y p, mem_shadingAtom_pattern hp⟩

theorem shadingAtom_finite_volume {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) {Y : ι → Set X} (hfin : ∀ i, μ (Y i) ≠ ⊤) (A : Finset ι) :
    μ (shadingAtom Y A) ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (measure_mono Set.inter_subset_left)
  simpa using
    measure_biUnion_ne_top (Set.toFinite (Set.univ : Set ι)) (fun i _ => hfin i)

theorem sum_shadingAtom_volume {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) {Y : ι → Set X} (hY : ∀ i, MeasurableSet (Y i)) :
    (∑ A, μ (shadingAtom Y A)) = μ (⋃ i, Y i) := by
  simpa only [shadingAtom_iUnion, tsum_fintype] using
    (measure_iUnion (μ := μ) (shadingAtom_disjoint Y) (shadingAtom_measurable hY)).symm

/-- Keeping a finite list of incidence edges reconstructs measurable subshadings. -/
def atomicShading {X ι : Type*} [Fintype ι] (Y : ι → Set X)
    (T : Finset (ι × Finset ι)) (i : ι) : Set X :=
  ⋃ A ∈ Finset.univ.filter (fun A => (i, A) ∈ T), shadingAtom Y A

theorem atomicShading_measurable {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    {Y : ι → Set X} (hY : ∀ i, MeasurableSet (Y i)) (T : Finset (ι × Finset ι)) (i : ι) :
    MeasurableSet (atomicShading Y T i) :=
  Finset.measurableSet_biUnion _ (fun _ _ => shadingAtom_measurable hY _)

theorem mem_atomicShading {X ι : Type*} [Fintype ι] {Y : ι → Set X}
    {T : Finset (ι × Finset ι)} {i : ι} {p : X} :
    p ∈ atomicShading Y T i ↔ p ∈ ⋃ j, Y j ∧ (i, shadingPattern Y p) ∈ T := by
  constructor
  · intro hp
    obtain ⟨A, hA, hp⟩ := Set.mem_iUnion₂.mp hp
    exact ⟨hp.1, shadingAtom_eq_pattern hp ▸ (Finset.mem_filter.mp hA).2⟩
  · rintro ⟨hp, hi⟩
    exact Set.mem_iUnion₂.mpr ⟨shadingPattern Y p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩,
      mem_shadingAtom_pattern hp⟩

theorem atomicShading_subset {X ι : Type*} [Fintype ι] {Y : ι → Set X}
    {T : Finset (ι × Finset ι)} (hT : ∀ e ∈ T, e.1 ∈ e.2) (i : ι) :
    atomicShading Y T i ⊆ Y i := by
  intro p hp
  exact (mem_shadingPattern Y p i).mp (hT _ (mem_atomicShading.mp hp).2)

theorem atomicShading_volume {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) {Y : ι → Set X} (hY : ∀ i, MeasurableSet (Y i))
    (T : Finset (ι × Finset ι)) (i : ι) :
    μ (atomicShading Y T i) = ∑ A ∈ Finset.univ.filter (fun A => (i, A) ∈ T), μ (shadingAtom Y A) := by
  apply measure_biUnion_finset
  · exact fun _ _ _ _ hAB => shadingAtom_disjoint Y hAB
  · exact fun _ _ => shadingAtom_measurable hY _

theorem atomicShading_mass {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) {Y : ι → Set X} (hY : ∀ i, MeasurableSet (Y i))
    (T : Finset (ι × Finset ι)) :
    (∑ i, μ (atomicShading Y T i)) = ∑ a ∈ T, μ (shadingAtom Y a.2) := by
  have he : T = Finset.univ.filter (fun a => a ∈ T) := by ext a; simp
  conv_rhs => rw [he, Finset.sum_filter, Fintype.sum_prod_type]
  simp_rw [atomicShading_volume μ hY, Finset.sum_filter]

theorem atomicShading_row_mass {X ι κ : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) {Y : ι → Set X} (hY : ∀ i, MeasurableSet (Y i))
    (T : Finset (ι × Finset ι)) (row : ι → κ) (k : κ) :
    (∑ i ∈ Finset.univ.filter (fun i => row i = k), μ (atomicShading Y T i)) =
      ∑ a ∈ T.filter (fun a => row a.1 = k), μ (shadingAtom Y a.2) := by
  have he (i : ι) : atomicShading Y (T.filter fun a => row a.1 = k) i =
      if row i = k then atomicShading Y T i else ∅ := by
    ext p
    simp only [mem_atomicShading, Finset.mem_filter]
    by_cases hi : row i = k <;> simp [hi, mem_atomicShading]
  rw [← atomicShading_mass μ hY]
  simp_rw [he]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : row i = k <;> simp [hi]

theorem atomicShading_full {X ι : Type*} [Fintype ι] (Y : ι → Set X) (i : ι) :
    atomicShading Y (Finset.univ.filter fun a : ι × Finset ι => a.1 ∈ a.2) i = Y i := by
  ext p
  rw [mem_atomicShading]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_shadingPattern]
  exact and_iff_right_of_imp (fun hp => Set.mem_iUnion.mpr ⟨i, hp⟩)

theorem atomicShading_remove_null_mass {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) {Y : ι → Set X} (hY : ∀ i, MeasurableSet (Y i))
    (T : Finset (ι × Finset ι)) (i : ι) :
    μ (atomicShading Y (T.filter fun a => μ (shadingAtom Y a.2) ≠ 0) i) =
      μ (atomicShading Y T i) := by
  simp_rw [atomicShading_volume μ hY, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro A _
  by_cases hA : μ (shadingAtom Y A) = 0 <;> by_cases hi : (i, A) ∈ T <;> simp [hA, hi]

end

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
