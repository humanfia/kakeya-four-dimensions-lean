-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.GridCube.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.TSInterface

/-!
# Grid cubes in space

Half-open grid cubes of side `s` in `Space` (`gridCube`, defined in `TSInterface`), indexed by
`Fin 3 → ℤ`, with the floor index map.
-/

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal

/-- The index of the grid cube containing `p`. -/
noncomputable def cubeIndex (s : ℝ) (p : Space) : Fin 3 → ℤ := fun j => ⌊p j / s⌋

theorem mem_gridCube_cubeIndex {s : ℝ} (hs : 0 < s) (p : Space) :
    p ∈ gridCube s (cubeIndex s p) := by
  intro j
  have h1 := Int.floor_le (p j / s)
  have h2 := Int.lt_floor_add_one (p j / s)
  constructor
  · have := mul_le_mul_of_nonneg_left h1 hs.le
    rwa [mul_div_cancel₀ _ hs.ne'] at this
  · have := mul_lt_mul_of_pos_left h2 hs
    rwa [mul_div_cancel₀ _ hs.ne'] at this

theorem cubeIndex_eq_of_mem {s : ℝ} (hs : 0 < s) {p : Space} {k : Fin 3 → ℤ}
    (hp : p ∈ gridCube s k) : cubeIndex s p = k := by
  funext j
  obtain ⟨h1, h2⟩ := hp j
  rw [cubeIndex, Int.floor_eq_iff]
  constructor
  · rw [le_div_iff₀ hs]; linarith
  · rw [div_lt_iff₀ hs]; linarith

theorem mem_gridCube_iff {s : ℝ} (hs : 0 < s) {p : Space} {k : Fin 3 → ℤ} :
    p ∈ gridCube s k ↔ cubeIndex s p = k :=
  ⟨cubeIndex_eq_of_mem hs, fun h => h ▸ mem_gridCube_cubeIndex hs p⟩

theorem gridCube_disjoint {s : ℝ} (hs : 0 < s) {k k' : Fin 3 → ℤ} (hkk : k ≠ k') :
    Disjoint (gridCube s k) (gridCube s k') := by
  rw [Set.disjoint_left]
  intro p hp hp'
  exact hkk ((cubeIndex_eq_of_mem hs hp).symm.trans (cubeIndex_eq_of_mem hs hp'))

theorem measurableSet_gridCube (s : ℝ) (k : Fin 3 → ℤ) : MeasurableSet (gridCube s k) := by
  have : gridCube s k = ⋂ j, ({p : Space | s * k j ≤ p j} ∩ {p : Space | p j < s * (k j + 1)}) := by
    ext p; simp [gridCube]
  rw [this]
  refine MeasurableSet.iInter fun j => ?_
  have hm : Measurable fun p : Space => p j := by fun_prop
  exact (measurableSet_le measurable_const hm).inter (measurableSet_lt hm measurable_const)

theorem diam_le_of_mem_gridCube {s : ℝ} (hs : 0 < s) {k : Fin 3 → ℤ} {p q : Space}
    (hp : p ∈ gridCube s k) (hq : q ∈ gridCube s k) : dist p q < 2 * s := by
  have hcoord : ∀ j, |p j - q j| < s := by
    intro j
    obtain ⟨h1, h2⟩ := hp j
    obtain ⟨h3, h4⟩ := hq j
    rw [abs_lt]; constructor <;> linarith
  rw [EuclideanSpace.dist_eq]
  have hsum : ∑ j, dist (p j) (q j) ^ 2 < 3 * s ^ 2 := by
    rw [Fin.sum_univ_three]
    have := fun j => (sq_lt_sq' (by linarith [abs_lt.1 (hcoord j)]) (abs_lt.1 (hcoord j)).2)
    simp only [Real.dist_eq]
    have h0 := hcoord 0; have h1 := hcoord 1; have h2 := hcoord 2
    have e0 : |p 0 - q 0| ^ 2 < s ^ 2 := by
      exact sq_lt_sq' (by linarith [abs_nonneg (p 0 - q 0)]) h0
    have e1 : |p 1 - q 1| ^ 2 < s ^ 2 := by
      exact sq_lt_sq' (by linarith [abs_nonneg (p 1 - q 1)]) h1
    have e2 : |p 2 - q 2| ^ 2 < s ^ 2 := by
      exact sq_lt_sq' (by linarith [abs_nonneg (p 2 - q 2)]) h2
    linarith
  calc Real.sqrt (∑ j, dist (p j) (q j) ^ 2) < Real.sqrt (4 * s ^ 2) := by
        apply Real.sqrt_lt_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
        nlinarith [sq_nonneg s]
    _ = 2 * s := by
        rw [show (4 : ℝ) * s ^ 2 = (2 * s) ^ 2 by ring, Real.sqrt_sq (by linarith)]


theorem volume_gridCube {s : ℝ} (hs : 0 < s) (k : Fin 3 → ℤ) :
    volume (gridCube s k) = ENNReal.ofReal s ^ 3 := by
  have hpre : gridCube s k = WithLp.ofLp ⁻¹' (Set.pi Set.univ fun j =>
      Set.Ico (s * k j) (s * (k j + 1))) := by
    ext p; simp [gridCube]
  rw [hpre, (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
    (MeasurableSet.univ_pi fun _ => measurableSet_Ico).nullMeasurableSet, volume_pi_pi]
  simp only [Real.volume_Ico]
  rw [show (fun j : Fin 3 => ENNReal.ofReal (s * (↑(k j) + 1) - s * ↑(k j))) =
      fun _ => ENNReal.ofReal s by funext j; congr 1; ring]
  simp [Finset.prod_const]

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
