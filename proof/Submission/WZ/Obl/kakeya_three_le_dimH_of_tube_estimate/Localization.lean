-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.kakeya_three_le_dimH_of_tube_estimate.Localization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.kakeya_three_le_dimH_of_tube_estimate.Packing
import Submission.WZ.Obl.kakeya_three_le_dimH_of_tube_estimate.Directions

open Set Metric MeasureTheory
open scoped ENNReal NNReal

namespace WangZahlLot.Obl.kakeya_three_le_dimH_of_tube_estimate

open LeanEval.Analysis.WangZahlKakeya

/-- A positive-area family of Kakeya segments has its midpoints near one fixed point. -/
theorem exists_localized_directions {K : Set Space} (hK : IsKakeya K) :
    ∃ (A : Set Plane) (x : Plane → Space) (p : Space),
      A ⊆ closedBall (0 : Plane) (1 / 4) ∧ volume A ≠ 0 ∧ volume A ≠ ⊤ ∧
      ∀ u ∈ A, (∀ t ∈ Icc (0 : ℝ) 1, x u + t • capDirection u ∈ K) ∧
        dist (x u + (1 / 2 : ℝ) • capDirection u) p ≤ 1 / 8 := by
  classical
  have hex : ∀ u : Plane, ∃ x : Space, ‖u‖ ≤ 1 / 4 →
      ∀ t ∈ Icc (0 : ℝ) 1, x + t • capDirection u ∈ K := by
    intro u
    by_cases hu : ‖u‖ ≤ 1 / 4
    · obtain ⟨x, hx⟩ := hK.2 (capDirection u) (norm_capDirection hu)
      exact ⟨x, fun _ => hx⟩
    · exact ⟨0, fun h => (hu h).elim⟩
  choose x hx using hex
  obtain ⟨P, hPK, _, hcover⟩ := exists_finset_separated_cover hK.1.totallyBounded
    (by norm_num : (0 : ℝ) < 1 / 8)
  let B : Set Plane := closedBall 0 (1 / 4)
  let D : Space → Set Plane := fun p =>
    {u | u ∈ B ∧ dist (x u + (1 / 2 : ℝ) • capDirection u) p ≤ 1 / 8}
  have hBcov : B ⊆ ⋃ p ∈ P, D p := by
    intro u hu
    have hu' : ‖u‖ ≤ 1 / 4 := by simpa [B, mem_closedBall, dist_zero_right] using hu
    have hm := hx u hu' (1 / 2) (by constructor <;> norm_num)
    obtain ⟨p, hp⟩ := mem_iUnion.mp (hcover hm)
    obtain ⟨hpP, hmp⟩ := mem_iUnion.mp hp
    exact mem_iUnion.mpr ⟨p, mem_iUnion.mpr ⟨hpP, hu, hmp⟩⟩
  have hBpos : volume B ≠ 0 := by
    dsimp [B]
    rw [EuclideanSpace.volume_closedBall_fin_two]
    positivity
  obtain ⟨p, hpP, hp⟩ : ∃ p ∈ P, volume (D p) ≠ 0 := by
    by_contra! H
    have hle := (measure_mono (μ := volume) hBcov).trans (measure_biUnion_finset_le P D)
    have hzero : ∑ p ∈ P, volume (D p) = 0 := Finset.sum_eq_zero H
    rw [hzero] at hle
    exact hBpos (le_zero_iff.mp hle)
  refine ⟨D p, x, p, fun u hu => hu.1, hp, ?_, ?_⟩
  · have hBfin : volume B ≠ ⊤ := by
      dsimp [B]
      rw [EuclideanSpace.volume_closedBall_fin_two]
      finiteness
    exact ne_top_of_le_ne_top hBfin (measure_mono (show D p ⊆ B from fun _ h => h.1))
  · intro u hu
    refine ⟨hx u ?_, hu.2⟩
    simpa [B, mem_closedBall, dist_zero_right] using hu.1

/-- A unit segment whose midpoint is close to the origin has a small tube inside
the unit ball. -/
theorem tube_subset_unit_ball {x v : Space} (hv : ‖v‖ = 1)
    (hx : ‖x + (1 / 2 : ℝ) • v‖ ≤ 1 / 8) {r : ℝ} (hr : r ≤ 1 / 8) :
    thickening r (segment ℝ x (x + v)) ⊆ ball (0 : Space) 1 := by
  intro y hy
  obtain ⟨z, hz, hyz⟩ := mem_thickening_iff.mp hy
  rw [segment_eq_image'] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  simp only [add_sub_cancel_left] at hyz
  have hparam : ‖x + t • v‖ ≤ 1 / 8 + 1 / 2 := by
    have heq : x + t • v = (x + (1 / 2 : ℝ) • v) + (t - 1 / 2) • v := by module
    rw [heq]
    calc
      ‖x + (1 / 2 : ℝ) • v + (t - 1 / 2) • v‖ ≤
          ‖x + (1 / 2 : ℝ) • v‖ + ‖(t - 1 / 2) • v‖ := norm_add_le _ _
      _ ≤ 1 / 8 + 1 / 2 := by
        rw [norm_smul, hv, mul_one, Real.norm_eq_abs]
        have : |t - 1 / 2| ≤ 1 / 2 := by
          rw [abs_le]
          constructor <;> linarith [ht.1, ht.2]
        linarith
  have htri := dist_triangle y (x + t • v) 0
  rw [mem_ball, dist_zero_right]
  rw [dist_zero_right, dist_zero_right] at htri
  linarith

end WangZahlLot.Obl.kakeya_three_le_dimH_of_tube_estimate
