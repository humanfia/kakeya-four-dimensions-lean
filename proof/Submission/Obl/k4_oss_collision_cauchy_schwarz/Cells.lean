import Submission.Obl.k4_oss_collision_cauchy_schwarz.Arithmetic

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Obl.k4_oss_collision_cauchy_schwarz

/-- Half-open cells of length `r`, including all boundary points exactly once. -/
def cell (r : ℝ) (k : ℤ) : Set ℝ := {x | ⌊x / r⌋ = k}

theorem measurableSet_cell (r : ℝ) (k : ℤ) : MeasurableSet (cell r k) := by
  apply measurableSet_eq_fun _ measurable_const
  fun_prop

theorem abs_sub_le_of_same_cell {r x y : ℝ} (hr : 0 < r)
    (h : ⌊x / r⌋ = ⌊y / r⌋) : |x - y| ≤ r := by
  have hx := Int.floor_le (x / r)
  have hx' := Int.lt_floor_add_one (x / r)
  have hy := Int.floor_le (y / r)
  have hy' := Int.lt_floor_add_one (y / r)
  rw [h] at hx hx'
  have hxy : |x / r - y / r| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  rw [← sub_div, abs_div, abs_of_pos hr, div_lt_one hr] at hxy
  exact hxy.le

theorem floor_neighbors_of_abs_sub_le {r x y : ℝ} (hr : 0 < r)
    (h : |x - y| ≤ r) :
    ⌊y / r⌋ = ⌊x / r⌋ + (-1) ∨ ⌊y / r⌋ = ⌊x / r⌋ ∨
      ⌊y / r⌋ = ⌊x / r⌋ + 1 := by
  have hxy : |x / r - y / r| ≤ 1 := by
    rw [← sub_div, abs_div, abs_of_pos hr, div_le_one hr]
    exact h
  rw [abs_le] at hxy
  have h₁ := Int.floor_mono (show x / r ≤ y / r + 1 by linarith)
  have h₂ := Int.floor_mono (show y / r ≤ x / r + 1 by linarith)
  rw [Int.floor_add_one] at h₁ h₂
  omega

/-- Decompose an integer-valued pair event into disjoint product fibers. -/
theorem shift_event_measure {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [SFinite μ] (φ : A → ℤ) (hφ : Measurable φ) (j : ℤ) :
    (μ.prod μ) {p | φ p.2 = φ p.1 + j} =
      ∑' k : ℤ, μ {x | φ x = k} * μ {x | φ x = k + j} := by
  have hset : {p : A × A | φ p.2 = φ p.1 + j} =
      ⋃ k : ℤ, {x | φ x = k} ×ˢ {x | φ x = k + j} := by
    ext p
    simp only [mem_ofPred_eq, mem_iUnion, mem_prod]
    constructor
    · intro h
      exact ⟨φ p.1, rfl, h⟩
    · rintro ⟨k, hk, h⟩
      simpa only [hk] using h
  have hd : Pairwise (fun k l : ℤ => Disjoint
      ({x | φ x = k} ×ˢ {x | φ x = k + j})
      ({x | φ x = l} ×ˢ {x | φ x = l + j})) := by
    intro k l hkl
    apply disjoint_left.mpr
    rintro p ⟨hk, _⟩ ⟨hl, _⟩
    exact hkl (hk.symm.trans hl)
  rw [hset, measure_iUnion hd]
  · simp_rw [Measure.prod_prod]
  · intro k
    exact (measurableSet_eq_fun hφ measurable_const).prod
      (measurableSet_eq_fun hφ measurable_const)

/-- The square sum of cell masses is bounded by the collision probability. -/
theorem cell_energy_le_collision (μ : Measure ℝ) [SFinite μ] {r : ℝ} (hr : 0 < r) :
    (∑' k : ℤ, μ (cell r k) * μ (cell r k)) ≤
      (μ.prod μ) {p | |p.1 - p.2| ≤ r} := by
  have h := shift_event_measure μ (fun x => ⌊x / r⌋) (by fun_prop) 0
  simp only [add_zero] at h
  unfold cell
  rw [← h]
  exact measure_mono fun p hp => abs_sub_le_of_same_cell hr hp.symm

/-- At distance at most one cell, there are just three possible cell offsets. -/
theorem collision_le_three_cell_energy (μ : Measure ℝ) [SFinite μ]
    {r : ℝ} (hr : 0 < r) :
    (μ.prod μ) {p | |p.1 - p.2| ≤ r} ≤
      3 * ∑' k : ℤ, μ (cell r k) * μ (cell r k) := by
  let E (j : ℤ) : Set (ℝ × ℝ) := {p | ⌊p.2 / r⌋ = ⌊p.1 / r⌋ + j}
  have hsub : {p : ℝ × ℝ | |p.1 - p.2| ≤ r} ⊆ E (-1) ∪ E 0 ∪ E 1 := by
    intro p hp
    rcases floor_neighbors_of_abs_sub_le hr hp with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (by simpa [E] using h))
    · exact Or.inr h
  have hE (j : ℤ) : (μ.prod μ) (E j) =
      ∑' k : ℤ, μ (cell r k) * μ (cell r (k + j)) :=
    shift_event_measure μ (fun x => ⌊x / r⌋) (by fun_prop) j
  calc
    _ ≤ (μ.prod μ) (E (-1) ∪ E 0 ∪ E 1) := measure_mono hsub
    _ ≤ (μ.prod μ) (E (-1)) + (μ.prod μ) (E 0) + (μ.prod μ) (E 1) :=
      (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ = (∑' k : ℤ, μ (cell r k) * μ (cell r (k + (-1)))) +
        (∑' k : ℤ, μ (cell r k) * μ (cell r (k + 0))) +
        (∑' k : ℤ, μ (cell r k) * μ (cell r (k + 1))) := by
      rw [hE, hE, hE]
    _ ≤ (∑' k : ℤ, μ (cell r k) * μ (cell r k)) +
        (∑' k : ℤ, μ (cell r k) * μ (cell r k)) +
        (∑' k : ℤ, μ (cell r k) * μ (cell r k)) := by
      exact add_le_add (add_le_add (tsum_mul_shift_le _ _) (tsum_mul_shift_le _ _))
        (tsum_mul_shift_le _ _)
    _ = _ := by rw [show (3 : ℝ≥0∞) = 1 + 1 + 1 by norm_num]; simp [add_mul]

end Submission.Obl.k4_oss_collision_cauchy_schwarz
