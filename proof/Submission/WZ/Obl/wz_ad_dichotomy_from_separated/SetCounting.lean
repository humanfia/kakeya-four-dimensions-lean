-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_ad_dichotomy_from_separated.SetCounting.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_ad_dichotomy_from_separated.Frostman

namespace WangZahlLot.Obl.wz_ad_dichotomy_from_separated

open Set Metric

theorem ncard_inter_ball (S : Finset Plane) (x : Plane) (r : ℝ) :
    ((↑S : Set Plane) ∩ Metric.ball x r).ncard = ballCount S x r := by
  classical
  have h : (↑S : Set Plane) ∩ Metric.ball x r =
      (↑(S.filter (fun y => y ∈ Metric.ball x r)) : Set Plane) := by
    ext y
    simp
  rw [h, Set.ncard_coe_finset]
  rfl

/-- The finite counting Frostman condition gives the closed-ball `Set.ncard`
form at a cost of two, by increasing the radius. -/
theorem FiniteFrostman.to_ncard_closed {δ C : ℝ} {S : Finset Plane}
    (h : FiniteFrostman δ C S) (hδ : 0 < δ) :
    ∀ (x : Plane) (r : ℝ), δ ≤ r →
      (((↑S : Set Plane) ∩ Metric.closedBall x r).ncard : ℝ) ≤
        (2 * C) * r * ((↑S : Set Plane).ncard : ℝ) := by
  intro x r hδr
  have hr : 0 < r := hδ.trans_le hδr
  have hsub : (↑S : Set Plane) ∩ Metric.closedBall x r ⊆
      (↑S : Set Plane) ∩ Metric.ball x (2 * r) := by
    intro y hy
    refine ⟨hy.1, ?_⟩
    change dist y x < 2 * r
    exact (show dist y x ≤ r from hy.2).trans_lt (by linarith)
  have hcard := Set.ncard_le_ncard hsub (S.finite_toSet.inter_of_left _)
  calc (((↑S : Set Plane) ∩ Metric.closedBall x r).ncard : ℝ) ≤
        (((↑S : Set Plane) ∩ Metric.ball x (2 * r)).ncard : ℝ) := by exact_mod_cast hcard
    _ = (ballCount S x (2 * r) : ℝ) := by rw [ncard_inter_ball]
    _ ≤ C * (2 * r) * (S.card : ℝ) := h x (2 * r) (by linarith)
    _ = (2 * C) * r * ((↑S : Set Plane).ncard : ℝ) := by
      rw [Set.ncard_coe_finset]
      ring

theorem finiteFrostman_of_ncard_closed {δ C : ℝ} {F : Set Plane} (hF : F.Finite)
    (h : ∀ (x : Plane) (r : ℝ), δ ≤ r →
      ((F ∩ Metric.closedBall x r).ncard : ℝ) ≤ C * r * (F.ncard : ℝ)) :
    FiniteFrostman δ C hF.toFinset := by
  intro x r hδr
  rw [← ncard_inter_ball, hF.coe_toFinset, ← Set.ncard_eq_toFinset_card F hF]
  have hsub : F ∩ Metric.ball x r ⊆ F ∩ Metric.closedBall x r :=
    Set.inter_subset_inter_right F Metric.ball_subset_closedBall
  have hcard := Set.ncard_le_ncard hsub (hF.inter_of_left _)
  have hcard' : ((F ∩ Metric.ball x r).ncard : ℝ) ≤
      ((F ∩ Metric.closedBall x r).ncard : ℝ) := by exact_mod_cast hcard
  exact hcard'.trans (h x r hδr)

end WangZahlLot.Obl.wz_ad_dichotomy_from_separated
