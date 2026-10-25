-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.SeparatedCellGlue.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open Set Metric
open scoped Classical

/-- A set inside one cell sees only the corresponding component of a union
whose components lie in pairwise disjoint cells. -/
theorem disjoint_cells_union_inter {X ι : Type*} (C W : ι → Set X)
    (hdisj : Pairwise fun j k => Disjoint (C j) (C k))
    (hWC : ∀ j, W j ⊆ C j) (j : ι) {H : Set X} (hHC : H ⊆ C j) :
    (⋃ k, W k) ∩ H = W j ∩ H := by
  ext p
  constructor
  · rintro ⟨hp, hpH⟩
    obtain ⟨k, hpk⟩ := mem_iUnion.mp hp
    by_cases hkj : k = j
    · exact ⟨hkj ▸ hpk, hpH⟩
    · exact False.elim ((Set.disjoint_left.mp (hdisj hkj)) (hWC k hpk) (hHC hpH))
  · exact fun hp => ⟨mem_iUnion.mpr ⟨j, hp.1⟩, hp.2⟩

/-- At a point of one cell, the global incidence equals that cell's incidence. -/
theorem disjoint_cells_union_card {X : Type*} {n N : ℕ}
    (C : Fin N → Set X) (W : Fin N → Fin n → Set X)
    (hdisj : Pairwise fun j k => Disjoint (C j) (C k))
    (hWC : ∀ j i, W j i ⊆ C j) (j : Fin N) {p : X} (hp : p ∈ C j) :
    (Finset.univ.filter fun i => p ∈ ⋃ k, W k i).card =
      (Finset.univ.filter fun i => p ∈ W j i).card := by
  classical
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hi
    have hh : p ∈ (⋃ k, W k i) ∩ C j := ⟨hi, hp⟩
    rw [disjoint_cells_union_inter C (fun k => W k i) hdisj
      (fun k => hWC k i) j subset_rfl] at hh
    exact hh.1
  · exact fun hi => mem_iUnion.mpr ⟨j, hi⟩

/-- A common local multiplicity level is also the global level when the
shading pieces lie in disjoint cells. -/
theorem disjoint_cells_common_level {X : Type*} {n N m : ℕ}
    (C : Fin N → Set X) (W : Fin N → Fin n → Set X)
    (hdisj : Pairwise fun j k => Disjoint (C j) (C k))
    (hWC : ∀ j i, W j i ⊆ C j)
    (hlevel : ∀ j p, p ∈ ⋃ i, W j i →
      2 ^ m ≤ (Finset.univ.filter fun i => p ∈ W j i).card ∧
        (Finset.univ.filter fun i => p ∈ W j i).card < 2 ^ (m + 1)) :
    ∀ p ∈ ⋃ i, ⋃ j, W j i,
      2 ^ m ≤ (Finset.univ.filter fun i => p ∈ ⋃ j, W j i).card ∧
        (Finset.univ.filter fun i => p ∈ ⋃ j, W j i).card < 2 ^ (m + 1) := by
  classical
  intro p hp
  obtain ⟨i, hi⟩ := mem_iUnion.mp hp
  obtain ⟨j, hj⟩ := mem_iUnion.mp hi
  rw [disjoint_cells_union_card C W hdisj hWC j (hWC j i hj)]
  exact hlevel j p (mem_iUnion.mpr ⟨i, hj⟩)

/-- Tube-wise separation suffices to preserve a local triggered containment
after uniting all cell shadings. The enlarged carriers themselves may overlap. -/
theorem separated_cells_triggered_containment {X : Type*} [PseudoMetricSpace X]
    {r : ℝ} (hr : 0 < r) {n N : ℕ}
    (C : Fin N → Set X) (q : Fin N → X) (W : Fin N → Fin n → Set X)
    (hdisj : Pairwise fun j k => Disjoint (C j) (C k))
    (hWC : ∀ j i, W j i ⊆ C j)
    (hWball : ∀ j i, W j i ⊆ ball (q j) r)
    (hsep : ∀ i j k, j ≠ k → (W j i).Nonempty → (W k i).Nonempty →
      10 * r < dist (q j) (q k))
    (j : Fin N) (H P : Set X) (hHC : H ⊆ C j) (hP : P ⊆ ball (q j) (3 * r))
    (hlocal : ∀ i, (W j i ∩ H).Nonempty → W j i ∩ P ⊆ H) :
    ∀ i, ((⋃ k, W k i) ∩ H).Nonempty → (⋃ k, W k i) ∩ P ⊆ H := by
  intro i hi
  obtain ⟨z, hzW, hzH⟩ := hi
  obtain ⟨k, hzk⟩ := mem_iUnion.mp hzW
  have hkj : k = j := by
    by_contra hne
    exact (Set.disjoint_left.mp (hdisj hne)) (hWC k i hzk) (hHC hzH)
  subst k
  have hj : (W j i).Nonempty := ⟨z, hzk⟩
  have hinside := hlocal i ⟨z, hzk, hzH⟩
  intro p hp
  obtain ⟨k, hpk⟩ := mem_iUnion.mp hp.1
  by_cases hkj : k = j
  · exact hinside ⟨hkj ▸ hpk, hp.2⟩
  · have hfar := hsep i j k (fun h => hkj h.symm) hj ⟨p, hpk⟩
    have hpk' : dist p (q k) < r := hWball k i hpk
    have hpj : dist p (q j) < 3 * r := hP hp.2
    have ht := dist_triangle (q j) p (q k)
    rw [dist_comm (q j) p] at ht
    linarith

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
