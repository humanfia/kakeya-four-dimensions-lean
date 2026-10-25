-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.IndexedDirections.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.DirectionCounts

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

attribute [local instance] Classical.propDecidable

/-- Counting Frostman condition on an indexed family; repetitions are allowed. -/
def IndexedFrostman {I : Type*} [Fintype I] (δ C : ℝ) (f : I → Plane) : Prop :=
  ∀ (x : Plane) (r : ℝ), δ ≤ r →
    ((Finset.univ.filter (fun i => dist (f i) x ≤ r)).card : ℝ) ≤ C * r * (Fintype.card I : ℝ)

theorem IndexedFrostman.circle_strip_count {I : Type*} [Fintype I] {f : I → Plane}
    {δ C r s : ℝ} (hF : IndexedFrostman δ C f) (hunit : ∀ i, ‖f i‖ = 1)
    {v : Plane} (hv : v ≠ 0) (hδr : δ ≤ r) (hsr : 2 * s / ‖v‖ ≤ r) :
    ((Finset.univ.filter (fun i => |inner ℝ (f i) v| ≤ s)).card : ℝ) ≤
      2 * C * r * (Fintype.card I : ℝ) := by
  classical
  obtain ⟨e, he, hballs⟩ := unit_circle_strip_two_balls (s := s) hv
  have hsub : Finset.univ.filter (fun i => |inner ℝ (f i) v| ≤ s) ⊆
      Finset.univ.filter (fun i => dist (f i) e ≤ r) ∪
      Finset.univ.filter (fun i => dist (f i) (-e) ≤ r) := by
    intro i hi
    rcases hballs (f i) (hunit i) (Finset.mem_filter.mp hi).2 with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.trans hsr⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.trans hsr⟩)
  have hcard : ((Finset.univ.filter (fun i => |inner ℝ (f i) v| ≤ s)).card : ℝ) ≤
      ((Finset.univ.filter (fun i => dist (f i) e ≤ r)).card : ℝ) +
      ((Finset.univ.filter (fun i => dist (f i) (-e) ≤ r)).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  nlinarith [hF e r hδr, hF (-e) r hδr]

theorem IndexedFrostman.direction_collision_count {I : Type*} [Fintype I]
    {f : I → Plane} {δ C : ℝ} (hF : IndexedFrostman δ C f)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 1 ≤ C) (hunit : ∀ i, ‖f i‖ = 1) (x y : Plane) :
    ((Finset.univ.filter (fun i => |inner ℝ (f i) (x - y)| ≤ 2 * δ)).card : ℝ) ≤
      8 * C * (δ / truncatedDistance δ x y) * (Fintype.card I : ℝ) := by
  classical
  have hbounds := truncatedDistance_bounds hδ1 x y
  have ht : 0 < truncatedDistance δ x y := hδ.trans_le hbounds.1
  by_cases hnear : ‖x - y‖ ≤ δ
  · have htrunc : truncatedDistance δ x y = δ := by
      apply max_eq_left
      exact (min_le_right 1 (dist x y)).trans (by rwa [dist_eq_norm])
    rw [htrunc, div_self hδ.ne', mul_one]
    have hc : ((Finset.univ.filter (fun i => |inner ℝ (f i) (x - y)| ≤ 2 * δ)).card : ℝ) ≤
        (Fintype.card I : ℝ) := by
      exact_mod_cast (Finset.card_filter_le Finset.univ _).trans_eq Finset.card_univ
    nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card I)]
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

theorem IndexedFrostman.direction_collision_power {I : Type*} [Fintype I]
    {f : I → Plane} {δ C γ : ℝ} (hF : IndexedFrostman δ C f)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 1 ≤ C) (hunit : ∀ i, ‖f i‖ = 1)
    (hγ : γ ≤ 1) (x y : Plane) :
    ((Finset.univ.filter (fun i => |inner ℝ (f i) (x - y)| ≤ 2 * δ)).card : ℝ) ≤
      8 * C * δ ^ γ * (truncatedDistance δ x y) ^ (-γ) * (Fintype.card I : ℝ) := by
  have hbounds := truncatedDistance_bounds hδ1 x y
  have ht : 0 < truncatedDistance δ x y := hδ.trans_le hbounds.1
  have hratio : δ / truncatedDistance δ x y ≤ 1 := (div_le_one ht).mpr hbounds.1
  have hpow : δ / truncatedDistance δ x y ≤ (δ / truncatedDistance δ x y) ^ γ := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge (div_pos hδ ht) hratio hγ
  have hid : (δ / truncatedDistance δ x y) ^ γ =
      δ ^ γ * (truncatedDistance δ x y) ^ (-γ) := by
    rw [Real.div_rpow hδ.le ht.le, Real.rpow_neg ht.le, div_eq_mul_inv]
  calc ((Finset.univ.filter (fun i => |inner ℝ (f i) (x - y)| ≤ 2 * δ)).card : ℝ) ≤
        8 * C * (δ / truncatedDistance δ x y) * (Fintype.card I : ℝ) :=
          hF.direction_collision_count hδ hδ1 hC hunit x y
    _ ≤ 8 * C * (δ / truncatedDistance δ x y) ^ γ * (Fintype.card I : ℝ) := by gcongr
    _ = _ := by rw [hid]; ring

end WangZahlLot.Obl.wz_separated_projection_dichotomy
