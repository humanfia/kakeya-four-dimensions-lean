-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.GrainComponents.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/GrainComponents.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from this workspace's o169/x0641, WangZahlLot/Obl/wz_move_three_wide_grains_core/GrainComponents.lean
   (7d05c80, sessions x0450/x0641/x0670). Namespace and grain-witness interface adjusted. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.GrainWitnesses

noncomputable section
namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
open Set MeasureTheory Classical

/-- Fine incidences assigned to one original grain. -/
def grainComponent {n N L : ℕ} (S : Finset (Fin n)) (Z : Fin n → Set V)
    (f : Fin n → Fin N) (H : Fin L → Set V) (γ : Fin L → Fin N)
    (j : Fin L) (i : Fin n) : Set V :=
  {p | i ∈ S ∧ f i = γ j ∧ p ∈ Z i ∩ H j}

theorem measurable_grainComponent {n N L : ℕ} (S : Finset (Fin n))
    (Z : Fin n → Set V) (f : Fin n → Fin N) (H : Fin L → Set V) (γ : Fin L → Fin N)
    (hZ : ∀ i, MeasurableSet (Z i)) (hH : ∀ j, MeasurableSet (H j)) (j i) :
    MeasurableSet (grainComponent S Z f H γ j i) := by
  classical
  by_cases hi : i ∈ S ∧ f i = γ j
  · have he : grainComponent S Z f H γ j i = Z i ∩ H j := by
      ext p
      simp only [grainComponent, mem_ofPred_eq, hi.1, hi.2, true_and]
    rw [he]
    exact (hZ i).inter (hH j)
  · have he : grainComponent S Z f H γ j i = ∅ := by
      ext p
      simp only [grainComponent, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact fun h => hi ⟨h.1, h.2.1⟩
    rw [he]
    exact MeasurableSet.empty

/-- The original fibrewise saturation protects every component against
any other old grain used by the same fine tube. -/
theorem grainComponent_self {n N L : ℕ} (S : Finset (Fin n)) (Z : Fin n → Set V)
    (f : Fin n → Fin N) (H U : Fin L → Set V) (γ : Fin L → Fin N)
    (hdis : ∀ j k, j ≠ k → γ j = γ k → Disjoint (H j) (H k))
    (hsat : ∀ i ∈ S, ∀ j, f i = γ j → (Z i ∩ H j).Nonempty → Z i ∩ U j ⊆ H j) :
    ∀ j k i, j ≠ k → (grainComponent S Z f H γ k i).Nonempty →
      Disjoint (grainComponent S Z f H γ j i) (U k) := by
  rintro j k i hjk ⟨p, hp⟩
  rw [Set.disjoint_left]
  intro q hq hqU
  have he : γ j = γ k := hq.2.1.symm.trans hp.2.1
  exact Set.disjoint_left.mp (hdis j k hjk he) hq.2.2.2
    (hsat i hp.1 k hp.2.1 ⟨p, hp.2.2⟩ ⟨hq.2.2.1, hqU⟩)

/-- A grain component has the full fibre count at each shaded point of
that grain, and zero count outside its shading. -/
theorem grainComponent_count {n N L : ℕ} (S : Finset (Fin n)) (Z : Fin n → Set V)
    (f : Fin n → Fin N) (H : Fin L → Set V) (γ : Fin L → Fin N) (j) (p : V) :
    q n {i | p ∈ grainComponent S Z f H γ j i} =
      if p ∈ H j then q n {i | i ∈ S ∧ f i = γ j ∧ p ∈ Z i} else 0 := by
  classical
  by_cases hp : p ∈ H j
  · rw [ite_eq_left hp]
    congr 2
    ext i
    simp [grainComponent, hp]
  · rw [ite_eq_right hp]
    simp [grainComponent, hp, q]

/-- The old grain components split each fine shading without changing
its total mass. -/
theorem grainComponent_mass_eq {n N L : ℕ} (S : Finset (Fin n)) (Z : Fin n → Set V)
    (f : Fin n → Fin N) (H : Fin L → Set V) (γ : Fin L → Fin N)
    (hZ : ∀ i, MeasurableSet (Z i)) (hH : ∀ j, MeasurableSet (H j))
    (hout : ∀ i, i ∉ S → Z i = ∅)
    (hdis : ∀ j k, j ≠ k → γ j = γ k → Disjoint (H j) (H k))
    (hcover : ∀ k, {p | ∃ j, γ j = k ∧ p ∈ H j} =
      {p | ∃ i ∈ S, f i = k ∧ p ∈ Z i}) :
    (∑ j, ∑ i, μ (grainComponent S Z f H γ j i)) = ∑ i, μ (Z i) := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have hUnion : (⋃ j, grainComponent S Z f H γ j i) = Z i := by
    ext p
    constructor
    · rintro ⟨_, ⟨j, rfl⟩, hp⟩
      exact hp.2.2.1
    · intro hp
      have hi : i ∈ S := by
        by_contra hi
        rw [hout i hi] at hp
        exact hp
      have hp' : p ∈ {p | ∃ j, γ j = f i ∧ p ∈ H j} := by
        rw [hcover]
        exact ⟨i, hi, rfl, hp⟩
      obtain ⟨j, hj, hpj⟩ := hp'
      exact mem_iUnion.mpr ⟨j, hi, hj.symm, hp, hpj⟩
  have hpair : Pairwise (fun j k => Disjoint (grainComponent S Z f H γ j i)
      (grainComponent S Z f H γ k i)) := by
    intro j k hjk
    rw [Set.disjoint_left]
    intro p hpj hpk
    exact Set.disjoint_left.mp (hdis j k hjk (hpj.2.1.symm.trans hpk.2.1)) hpj.2.2.2 hpk.2.2.2
  have heq := measure_iUnion (μ := volume) hpair (fun j => measurable_grainComponent S Z f H γ hZ hH j i)
  rw [hUnion] at heq
  simpa only [tsum_fintype] using heq.symm

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
