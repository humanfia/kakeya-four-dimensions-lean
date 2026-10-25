-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.CellDensity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.RegularPruning
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.BroadPieceCount

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open MeasureTheory Set
open scoped Classical ENNReal

/-- Pruning sparse spatial cells with total shading measure preserves a common
spatial cut. Thus pointwise angular broadness survives, while every occupied
cell acquires average density relative to all its original tube indices. -/
theorem common_cell_density_refinement {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {n N : ℕ} (Y : Fin n → Set X) (E : Fin N → Set X)
    (hY : ∀ i, MeasurableSet (Y i)) (hE : ∀ j, MeasurableSet (E j))
    (hfin : ∀ i, μ (Y i) ≠ ⊤) {τ L : ℝ} (hτ : 0 ≤ τ)
    (hcross : ∀ i, ({j | (Y i ∩ E j).Nonempty}.ncard : ℝ) ≤ L)
    (hbudget : ENNReal.ofReal (τ * (n : ℝ) * L) ≤ (1 / 2 : ENNReal) * ∑ i, μ (Y i)) :
    ∃ A : Set X, MeasurableSet A ∧
      (1 / 2 : ENNReal) * (∑ i, μ (Y i)) ≤ ∑ i, μ (Y i ∩ A) ∧
      ∀ j, ((⋃ i, Y i ∩ A) ∩ E j).Nonempty →
        ENNReal.ofReal (τ * ({i | (Y i ∩ E j).Nonempty}.ncard : ℝ)) ≤
          ∑ i, μ ((Y i ∩ A) ∩ E j) := by
  let ν : Measure X := ∑ i, μ.restrict (Y i)
  have hν (S : Set X) (hS : MeasurableSet S) : ν S = ∑ i, μ (Y i ∩ S) := by
    simp only [ν, Measure.finsetSum_apply, Measure.restrict_apply hS]
    apply Finset.sum_congr rfl
    intro i _
    rw [inter_comm]
  have hνuniv : ν univ = ∑ i, μ (Y i) := by
    rw [hν univ MeasurableSet.univ]
    simp only [inter_univ]
  have hνfin : ν univ ≠ ⊤ := by
    rw [hνuniv]
    exact ENNReal.sum_ne_top.mpr fun i _ => hfin i
  let t := fun j => ENNReal.ofReal (τ * ({i | (Y i ∩ E j).Nonempty}.ncard : ℝ))
  have hcost : ∑ j, t j ≤ (1 / 2 : ENNReal) * ν univ := by
    rw [hνuniv]
    apply le_trans ?_ hbudget
    dsimp [t]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j (_ : j ∈ Finset.univ) =>
      mul_nonneg hτ (Nat.cast_nonneg _))]
    apply ENNReal.ofReal_le_ofReal
    rw [← Finset.mul_sum, BrushPlanarity.piece_incidence_sum (fun j i => (Y i ∩ E j).Nonempty)]
    calc
      _ ≤ τ * ∑ _i : Fin n, L := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun i _ => hcross i) hτ
      _ = _ := by simp [mul_assoc]
  obtain ⟨A, hA, _, hkeep, hreg⟩ := regular_subshading_half ν Finset.univ E t
    (fun j _ => hE j) univ MeasurableSet.univ hνfin hcost
  refine ⟨A, hA, ?_, ?_⟩
  · simpa only [hνuniv, hν A hA] using hkeep
  · intro j hj
    obtain ⟨p, hp, hpE⟩ := hj
    obtain ⟨i, hpi⟩ := mem_iUnion.mp hp
    have hne : A ∩ E j ≠ ∅ := nonempty_iff_ne_empty.mp ⟨p, hpi.2, hpE⟩
    have hh := (hreg j (Finset.mem_univ _)).resolve_left hne
    apply hh.le.trans_eq
    rw [hν _ (hA.inter (hE j))]
    apply Finset.sum_congr rfl
    intro k _
    rw [inter_assoc]

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
