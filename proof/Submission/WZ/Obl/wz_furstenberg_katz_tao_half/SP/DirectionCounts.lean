-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.DirectionCounts.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.CircleGeometry
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.TruncatedEnergy

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

open Set Metric

attribute [local instance] Classical.propDecidable

theorem ClosedFiniteFrostman.circle_strip_count {δ C r s : ℝ} {Λ : Finset Plane}
    (hF : ClosedFiniteFrostman δ C Λ) (hunit : ∀ e ∈ Λ, ‖e‖ = 1)
    {v : Plane} (hv : v ≠ 0) (hδr : δ ≤ r) (hsr : 2 * s / ‖v‖ ≤ r) :
    ((Λ.filter (fun e => |inner ℝ e v| ≤ s)).card : ℝ) ≤ 2 * C * r * (Λ.card : ℝ) := by
  classical
  obtain ⟨e, he, hballs⟩ := unit_circle_strip_two_balls (s := s) hv
  have hsub : Λ.filter (fun u => |inner ℝ u v| ≤ s) ⊆
      Λ.filter (fun u => dist u e ≤ r) ∪ Λ.filter (fun u => dist u (-e) ≤ r) := by
    intro u hu
    obtain ⟨huΛ, hu⟩ := Finset.mem_filter.mp hu
    rcases hballs u (hunit u huΛ) hu with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨huΛ, h.trans hsr⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨huΛ, h.trans hsr⟩)
  have hcard : ((Λ.filter (fun u => |inner ℝ u v| ≤ s)).card : ℝ) ≤
      ((Λ.filter (fun u => dist u e ≤ r)).card : ℝ) +
      ((Λ.filter (fun u => dist u (-e) ≤ r)).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  nlinarith [hF.filter_closedBall e r hδr, hF.filter_closedBall (-e) r hδr]

theorem ClosedFiniteFrostman.direction_collision_count {δ C : ℝ} {Λ : Finset Plane}
    (hF : ClosedFiniteFrostman δ C Λ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 1 ≤ C)
    (hunit : ∀ e ∈ Λ, ‖e‖ = 1) (x y : Plane) :
    ((Λ.filter (fun e => |inner ℝ e (x - y)| ≤ 2 * δ)).card : ℝ) ≤
      8 * C * (δ / truncatedDistance δ x y) * (Λ.card : ℝ) := by
  classical
  have hbounds := truncatedDistance_bounds hδ1 x y
  have ht : 0 < truncatedDistance δ x y := hδ.trans_le hbounds.1
  by_cases hnear : ‖x - y‖ ≤ δ
  · have htrunc : truncatedDistance δ x y = δ := by
      apply max_eq_left
      exact (min_le_right 1 (dist x y)).trans (by rwa [dist_eq_norm])
    rw [htrunc, div_self hδ.ne', mul_one]
    have hc : ((Λ.filter (fun e => |inner ℝ e (x - y)| ≤ 2 * δ)).card : ℝ) ≤
        (Λ.card : ℝ) := by exact_mod_cast Finset.card_filter_le Λ _
    nlinarith [Nat.cast_nonneg (α := ℝ) Λ.card]
  · have hvp : 0 < ‖x - y‖ := hδ.trans (lt_of_not_ge hnear)
    have htnorm : truncatedDistance δ x y ≤ ‖x - y‖ := by
      apply max_le (le_of_not_ge hnear)
      simpa only [dist_eq_norm] using min_le_right 1 (dist x y)
    have hδr : δ ≤ 4 * δ / truncatedDistance δ x y := by
      apply (le_div_iff₀ ht).mpr
      nlinarith [mul_le_mul_of_nonneg_left hbounds.2 hδ.le]
    have hsr : 2 * (2 * δ) / ‖x - y‖ ≤ 4 * δ / truncatedDistance δ x y := by
      calc 2 * (2 * δ) / ‖x - y‖ = 4 * δ / ‖x - y‖ := by ring
        _ ≤ 4 * δ / truncatedDistance δ x y := div_le_div_of_nonneg_left (by positivity) ht htnorm
    exact (hF.circle_strip_count hunit (norm_pos_iff.mp hvp) hδr hsr).trans_eq (by ring)

theorem ClosedFiniteFrostman.direction_collision_power {δ C γ : ℝ} {Λ : Finset Plane}
    (hF : ClosedFiniteFrostman δ C Λ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 1 ≤ C)
    (hunit : ∀ e ∈ Λ, ‖e‖ = 1) (hγ : γ ≤ 1) (x y : Plane) :
    ((Λ.filter (fun e => |inner ℝ e (x - y)| ≤ 2 * δ)).card : ℝ) ≤
      8 * C * δ ^ γ * (truncatedDistance δ x y) ^ (-γ) * (Λ.card : ℝ) := by
  have hbounds := truncatedDistance_bounds hδ1 x y
  have ht : 0 < truncatedDistance δ x y := hδ.trans_le hbounds.1
  have hratio : δ / truncatedDistance δ x y ≤ 1 := (div_le_one ht).mpr hbounds.1
  have hpow : δ / truncatedDistance δ x y ≤ (δ / truncatedDistance δ x y) ^ γ := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge (div_pos hδ ht) hratio hγ
  have hid : (δ / truncatedDistance δ x y) ^ γ =
      δ ^ γ * (truncatedDistance δ x y) ^ (-γ) := by
    rw [Real.div_rpow hδ.le ht.le, Real.rpow_neg ht.le, div_eq_mul_inv]
  calc ((Λ.filter (fun e => |inner ℝ e (x - y)| ≤ 2 * δ)).card : ℝ) ≤
        8 * C * (δ / truncatedDistance δ x y) * (Λ.card : ℝ) :=
          hF.direction_collision_count hδ hδ1 hC hunit x y
    _ ≤ 8 * C * (δ / truncatedDistance δ x y) ^ γ * (Λ.card : ℝ) := by gcongr
    _ = _ := by rw [hid]; ring

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
