-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.LocalCells.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.LipschitzTools

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_extremal_lipschitz_grains
open scoped Classical

/-- A bounded cell has a finite disjoint grid refinement into radius-`r` balls.
The count depends only on the ratio of the old and new radii. -/
theorem bounded_cell_localization {R r : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (E : Set Space) (c : Space) (hE : E ⊆ closedBall c R) :
    ∃ (F : Finset (Fin 3 → ℤ)) (q : (Fin 3 → ℤ) → Space),
      (F.card : ℝ) ≤ (12 * R / r) ^ 3 ∧
      (∀ k, E ∩ gridCube (r / 4) k ⊆ ball (q k) r) ∧
      (⋃ k ∈ F, E ∩ gridCube (r / 4) k) = E := by
  have hR : 0 < R := hr.trans_le hrR
  have hs : 0 < r / 4 := by positivity
  obtain ⟨F, hFcard, hF⟩ := exists_cells_cover c hR.le hs
  let q := fun k => if h : (E ∩ gridCube (r / 4) k).Nonempty then h.choose else c
  refine ⟨F, q, ?_, ?_, ?_⟩
  · have hh : (F.card : ℝ) ≤ ((⌊2 * R / (r / 4)⌋₊ : ℝ) + 3) ^ 3 := by
      exact_mod_cast hFcard
    have hfloor : (⌊2 * R / (r / 4)⌋₊ : ℝ) ≤ 8 * R / r := by
      convert Nat.floor_le (by positivity : 0 ≤ 2 * R / (r / 4)) using 1 <;> ring
    have hratio : 1 ≤ R / r := (le_div_iff₀ hr).mpr (by simpa using hrR)
    apply hh.trans (pow_le_pow_left₀ (by positivity) ?_ 3)
    rw [show 8 * R / r = 8 * (R / r) by ring] at hfloor
    rw [show 12 * R / r = 12 * (R / r) by ring]
    linarith
  · intro k p hp
    have hne : (E ∩ gridCube (r / 4) k).Nonempty := ⟨p, hp⟩
    have hq : q k ∈ E ∩ gridCube (r / 4) k := by
      dsimp [q]
      rw [dif_pos hne]
      exact hne.choose_spec
    have hd := diam_le_of_mem_gridCube hs hp.2 hq.2
    change dist p (q k) < r
    linarith
  · apply subset_antisymm
    · exact iUnion₂_subset fun _ _ => inter_subset_left
    · intro p hp
      refine mem_iUnion₂.mpr ⟨cubeIndex (r / 4) p, hF p (hE hp), hp, ?_⟩
      exact mem_gridCube_cubeIndex hs p

/-- Localize a finite disjoint family of bounded cells. The union is unchanged,
all new pieces lie in radius-`r` balls, and the tube-piece crossing count grows
by at most the same explicit cubic factor as the number of pieces. -/
theorem bounded_partition_localization {R r : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    {G : ℕ} (E : Fin G → Set Space) (c : Fin G → Space)
    (hE : ∀ j, MeasurableSet (E j)) (hbound : ∀ j, E j ⊆ closedBall (c j) R)
    (hdisj : Pairwise fun j k => Disjoint (E j) (E k)) :
    ∃ (N : ℕ) (D : Fin N → Set Space) (q : Fin N → Space) (parent : Fin N → Fin G),
      (∀ i, MeasurableSet (D i) ∧ D i ⊆ E (parent i) ∧ D i ⊆ ball (q i) r) ∧
      (Pairwise fun i k => Disjoint (D i) (D k)) ∧
      (⋃ i, D i) = ⋃ j, E j ∧
      (N : ℝ) ≤ G * (12 * R / r) ^ 3 ∧
      ∀ W : Set Space,
        ({i | (W ∩ D i).Nonempty}.ncard : ℝ) ≤
          (12 * R / r) ^ 3 * ({j | (W ∩ E j).Nonempty}.ncard : ℝ) := by
  choose F q hFcard hFball hFcover using fun j =>
    bounded_cell_localization hr hrR (E j) (c j) (hbound j)
  let S : Finset ((j : Fin G) × (Fin 3 → ℤ)) := Finset.univ.sigma F
  let e : Fin S.card → (j : Fin G) × (Fin 3 → ℤ) := fun i => (S.equivFin.symm i).val
  have heinj : Function.Injective e := Subtype.val_injective.comp S.equivFin.symm.injective
  have hemem (i : Fin S.card) : e i ∈ S := (S.equivFin.symm i).property
  have heF (i : Fin S.card) : (e i).2 ∈ F (e i).1 := (Finset.mem_sigma.mp (hemem i)).2
  have hesurj (s) (hs : s ∈ S) : ∃ i, e i = s :=
    ⟨S.equivFin ⟨s, hs⟩, by simp [e]⟩
  let D := fun i => E (e i).1 ∩ gridCube (r / 4) (e i).2
  refine ⟨S.card, D, (fun i => q (e i).1 (e i).2), (fun i => (e i).1), ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨(hE _).inter (measurableSet_gridCube _ _), inter_subset_left, hFball _ _⟩
  · intro i k hik
    by_cases hj : (e i).1 = (e k).1
    · have hgrid : (e i).2 ≠ (e k).2 := by
        intro hh
        apply hik
        apply heinj
        exact Sigma.ext hj (heq_of_eq hh)
      exact (gridCube_disjoint (by positivity : 0 < r / 4) hgrid).mono
        inter_subset_right inter_subset_right
    · exact (hdisj hj).mono inter_subset_left inter_subset_left
  · apply subset_antisymm
    · intro p hp
      obtain ⟨i, hi⟩ := mem_iUnion.mp hp
      exact mem_iUnion.mpr ⟨(e i).1, hi.1⟩
    · intro p hp
      obtain ⟨j, hj⟩ := mem_iUnion.mp hp
      rw [← hFcover j] at hj
      obtain ⟨k, hk, hpk⟩ := mem_iUnion₂.mp hj
      have hmem : (⟨j, k⟩ : (j : Fin G) × (Fin 3 → ℤ)) ∈ S :=
        Finset.mem_sigma.mpr ⟨Finset.mem_univ _, hk⟩
      obtain ⟨i, hi⟩ := hesurj ⟨j, k⟩ hmem
      apply mem_iUnion.mpr
      exact ⟨i, by simpa only [D, hi] using hpk⟩
  · have hcard : (S.card : ℝ) = ∑ j : Fin G, ((F j).card : ℝ) := by
      dsimp only [S]
      rw [Finset.card_sigma, Nat.cast_sum]
    rw [hcard]
    calc
      _ ≤ ∑ _j : Fin G, (12 * R / r) ^ 3 := Finset.sum_le_sum fun j _ => hFcard j
      _ = _ := by simp
  · intro W
    let A : Finset (Fin G) := Finset.univ.filter fun j => (W ∩ E j).Nonempty
    let B : Finset (Fin S.card) := Finset.univ.filter fun i => (W ∩ D i).Nonempty
    have hBA : B.image e ⊆ A.sigma F := by
      intro s hs
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hs
      refine Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, heF i⟩
      obtain ⟨p, hpW, hpD⟩ := (Finset.mem_filter.mp hi).2
      exact ⟨p, hpW, hpD.1⟩
    have hcard : B.card ≤ (A.sigma F).card := by
      rw [← Finset.card_image_of_injective B heinj]
      exact Finset.card_le_card hBA
    have hB : {i | (W ∩ D i).Nonempty} = (B : Set (Fin S.card)) := by ext i; simp [B]
    have hA : {j | (W ∩ E j).Nonempty} = (A : Set (Fin G)) := by ext j; simp [A]
    rw [hB, hA, ncard_coe_finset, ncard_coe_finset]
    calc
      _ ≤ ((A.sigma F).card : ℝ) := Nat.cast_le.mpr hcard
      _ = ∑ j ∈ A, ((F j).card : ℝ) := by rw [Finset.card_sigma, Nat.cast_sum]
      _ ≤ ∑ _j ∈ A, (12 * R / r) ^ 3 := Finset.sum_le_sum fun j _ => hFcard j
      _ = _ := by simp [mul_comm]

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
