-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.CellPigeonhole.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.GridCube

/-!
# Pigeonholing the values of a map into small cells
-/

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal

/-- Values in one grid cell of side `r` are within `2 r`. -/
theorem dist_lt_of_cubeIndex_eq {r : ℝ} (hr : 0 < r) {a b : Space}
    (h : cubeIndex r a = cubeIndex r b) : dist a b < 2 * r :=
  diam_le_of_mem_gridCube hr (mem_gridCube_cubeIndex hr a)
    ((mem_gridCube_iff hr).2 h.symm)

/-- Pigeonhole on a finite set of cells: some cell carries at least the average mass. -/
theorem exists_heavy_cell {α : Type*} [MeasurableSpace α] (ν : Measure α) {A : Set α}
    (V : α → Space) (hV : Measurable V) (hA : MeasurableSet A) {r : ℝ} (hr : 0 < r)
    (S : Finset (Fin 3 → ℤ)) (hS : ∀ p ∈ A, cubeIndex r (V p) ∈ S) (hSne : S.Nonempty) :
    ∃ k ∈ S, ν A ≤ S.card * ν (A ∩ V ⁻¹' gridCube r k) := by
  classical
  have hcover : A = ⋃ k ∈ S, A ∩ V ⁻¹' gridCube r k := by
    ext p
    simp only [mem_iUnion, mem_inter_iff, mem_preimage, exists_prop]
    constructor
    · intro hp; exact ⟨_, hS p hp, hp, mem_gridCube_cubeIndex hr _⟩
    · rintro ⟨k, _, hp, _⟩; exact hp
  have hle : ν A ≤ ∑ k ∈ S, ν (A ∩ V ⁻¹' gridCube r k) := by
    conv_lhs => rw [hcover]
    exact measure_biUnion_finset_le S _
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image S (fun k => ν (A ∩ V ⁻¹' gridCube r k)) hSne
  refine ⟨k, hk, hle.trans ?_⟩
  calc ∑ k ∈ S, ν (A ∩ V ⁻¹' gridCube r k) ≤ ∑ _j ∈ S, ν (A ∩ V ⁻¹' gridCube r k) :=
        Finset.sum_le_sum fun j hj => hmax j hj
    _ = S.card * ν (A ∩ V ⁻¹' gridCube r k) := by rw [Finset.sum_const, nsmul_eq_mul]

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
