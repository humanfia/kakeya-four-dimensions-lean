-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.PrismLocality.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.PrismNeighborhood

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric

/-- Every point of a prism with all sides at most c lies within c of its center. -/
theorem prism_norm_sub_center_le {a b c : ℝ} {z p : V}
    (ha : a ≤ c) (hb : b ≤ c) (hc : 0 ≤ c) (e : V ≃ₗᵢ[ℝ] V)
    (hp : p ∈ P a b c z e) : ‖p - z‖ ≤ c := by
  have hcoord (i : Fin 3) : |e (p - z) i| ≤ c / 2 := by
    fin_cases i
    · exact (show |e (p - z) 0| ≤ a / 2 from hp.1).trans (by linarith)
    · exact (show |e (p - z) 1| ≤ b / 2 from hp.2.1).trans (by linarith)
    · exact hp.2.2
  have hs (i : Fin 3) : (e (p - z) i) ^ 2 ≤ (c / 2) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ c / 2)).mpr (hcoord i)
  have hnorm := EuclideanSpace.real_norm_sq_eq (e (p - z))
  rw [Fin.sum_univ_three] at hnorm
  have hh : ‖e (p - z)‖ ≤ c := by
    nlinarith [hs 0, hs 1, hs 2, norm_nonneg (e (p - z))]
  simpa only [e.norm_map] using hh

/-- A nonempty prism touching a local ball remains inside its triple enlargement. -/
theorem prism_subset_triple_ball {a b c r : ℝ} {z p₀ : V}
    (ha : a ≤ c) (hb : b ≤ c) (hc : 0 ≤ c) (hcr : c ≤ r) (e : V ≃ₗᵢ[ℝ] V)
    (hmeet : (P a b c z e ∩ ball p₀ r).Nonempty) :
    P a b c z e ⊆ ball p₀ (3 * r) := by
  obtain ⟨q, hqP, hqball⟩ := hmeet
  intro p hp
  have hpz : dist p z ≤ c := by
    simpa only [dist_eq_norm] using prism_norm_sub_center_le ha hb hc e hp
  have hzq : dist z q ≤ c := by
    simpa only [dist_eq_norm, norm_sub_rev] using prism_norm_sub_center_le ha hb hc e hqP
  have hpq : dist p q ≤ 2 * c := by
    calc
      _ ≤ dist p z + dist z q := dist_triangle _ _ _
      _ ≤ c + c := add_le_add hpz hzq
      _ = _ := by ring
  apply mem_ball.mpr
  calc
    _ ≤ dist p q + dist q p₀ := dist_triangle _ _ _
    _ < 2 * c + r := add_lt_add_of_le_of_lt hpq (mem_ball.mp hqball)
    _ ≤ 3 * r := by linarith

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces
