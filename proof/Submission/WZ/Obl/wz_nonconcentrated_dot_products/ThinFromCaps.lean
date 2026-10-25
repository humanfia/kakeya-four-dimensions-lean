-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonconcentrated_dot_products.ThinFromCaps.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.QuarterScale
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.DyadicDepth

namespace WangZahlLot.Obl.wz_nonconcentrated_dot_products

open Set Metric

attribute [local instance] Classical.propDecidable

theorem four_rpow_quarter_le : (4 : ℝ) ^ (1 / 4 : ℝ) ≤ 4 := by
  calc (4 : ℝ) ^ (1 / 4 : ℝ) ≤ 4 ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = 4 := Real.rpow_one _

/-- Avoiding heavy caps at the finitely many dyadic scales controls every
angular ball, even when the angular map has repetitions. -/
theorem good_caps_ball_count {J : Type*} [Fintype J] (f : J → Plane) (R : J → Prop)
    {δ K : ℝ} {n : ℕ} (hδ : 0 < δ) (hK : 1 ≤ K)
    (hlast : dyadicRadius (n + 1) < δ)
    (hgood : ∀ j, R j → ∀ k ∈ Finset.range (n + 1),
      ((Finset.univ.filter (fun j' => dist (f j') (f j) ≤ dyadicRadius k)).card : ℝ) <
        K * (dyadicRadius k) ^ (1 / 4 : ℝ) * (Fintype.card J : ℝ))
    (u : Plane) (r : ℝ) (hr : δ ≤ r) :
    ((Finset.univ.filter (fun j => R j ∧ dist (f j) u ≤ r)).card : ℝ) ≤
      4 * K * r ^ (1 / 4 : ℝ) * (Fintype.card J : ℝ) := by
  classical
  let E := Finset.univ.filter (fun j => R j ∧ dist (f j) u ≤ r)
  change (E.card : ℝ) ≤ _
  have hrpos : 0 < r := hδ.trans_le hr
  by_cases hlarge : 32 < 2 * r
  · have hr1 : 1 ≤ r := by linarith
    have hp : 1 ≤ r ^ (1 / 4 : ℝ) := Real.one_le_rpow hr1 (by norm_num)
    have hfac : 1 ≤ 4 * K * r ^ (1 / 4 : ℝ) := by
      have hmul := mul_le_mul hK hp (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 0 ≤ K)
      nlinarith
    have hc : (E.card : ℝ) ≤ (Fintype.card J : ℝ) := by
      exact_mod_cast (Finset.card_filter_le (Finset.univ : Finset J) _).trans_eq Finset.card_univ
    exact hc.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card J)])
  · by_cases hE : E.Nonempty
    · obtain ⟨j, hj⟩ := hE
      have hj' := (Finset.mem_filter.mp hj).2
      obtain ⟨k, hk, hkr, hk2⟩ := dyadicRadius_cover hδ hlast
        (by linarith : δ ≤ 2 * r) (le_of_not_gt hlarge)
      have hsub : E ⊆ Finset.univ.filter (fun j' => dist (f j') (f j) ≤ dyadicRadius k) := by
        intro j' hj'
        have hj'' := (Finset.mem_filter.mp hj').2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        have hh := dist_triangle (f j') u (f j)
        rw [dist_comm u (f j)] at hh
        linarith
      have hcard : (E.card : ℝ) ≤
          ((Finset.univ.filter (fun j' => dist (f j') (f j) ≤ dyadicRadius k)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      have hp : (dyadicRadius k) ^ (1 / 4 : ℝ) ≤ 4 * r ^ (1 / 4 : ℝ) := by
        calc (dyadicRadius k) ^ (1 / 4 : ℝ) ≤ (4 * r) ^ (1 / 4 : ℝ) :=
            Real.rpow_le_rpow (dyadicRadius_pos k).le (by linarith) (by norm_num)
          _ = (4 : ℝ) ^ (1 / 4 : ℝ) * r ^ (1 / 4 : ℝ) := Real.mul_rpow (by norm_num) hrpos.le
          _ ≤ _ := mul_le_mul_of_nonneg_right four_rpow_quarter_le (by positivity)
      calc (E.card : ℝ) ≤ K * (dyadicRadius k) ^ (1 / 4 : ℝ) * (Fintype.card J : ℝ) :=
            hcard.trans (hgood j hj'.1 k hk).le
        _ ≤ K * (4 * r ^ (1 / 4 : ℝ)) * (Fintype.card J : ℝ) := by gcongr
        _ = _ := by ring
    · rw [Finset.not_nonempty_iff_eq_empty.mp hE, Finset.card_empty, Nat.cast_zero]
      positivity

theorem eight_rpow_quarter_le : (8 : ℝ) ^ (1 / 4 : ℝ) ≤ 4 := by
  have hp := quarter_power_four (by norm_num : (0 : ℝ) ≤ 8)
  by_contra h
  have hlt : (4 : ℝ) < 8 ^ (1 / 4 : ℝ) := lt_of_not_ge h
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hlt.le 4
  norm_num at hpow
  linarith

/-- Angular ball counting gives the corresponding thin-tube bound about
the pin, with a fixed absolute loss. -/
theorem radial_thin_of_good_caps {J : Type*} [Fintype J] (g : J → Plane)
    (R : J → Prop) (b : Plane) {δ K : ℝ} {n : ℕ} (hδ : 0 < δ) (hK : 1 ≤ K)
    (hlast : dyadicRadius (n + 1) < δ) (hsep : ∀ j, 1 / 4 ≤ ‖b - g j‖)
    (hgood : ∀ j, R j → ∀ k ∈ Finset.range (n + 1),
      ((Finset.univ.filter (fun j' => dist (radialDirection b (g j'))
        (radialDirection b (g j)) ≤ dyadicRadius k)).card : ℝ) <
        K * (dyadicRadius k) ^ (1 / 4 : ℝ) * (Fintype.card J : ℝ)) :
    ∀ (u : Plane) (r : ℝ), ‖u‖ = 1 → δ ≤ r →
      ((Finset.univ.filter (fun j => R j ∧ |inner ℝ (g j - b) u| < r)).card : ℝ) ≤
        32 * K * r ^ (1 / 4 : ℝ) * (Fintype.card J : ℝ) := by
  classical
  intro u r hu hr
  have hrpos := hδ.trans_le hr
  have hneq (j : J) : b ≠ g j := by
    intro h
    have hh := hsep j
    rw [h, sub_self, norm_zero] at hh
    norm_num at hh
  have hangle (j : J) (hj : |inner ℝ (g j - b) u| < r) :
      |inner ℝ (radialDirection b (g j)) u| ≤ 4 * r := by
    have hn : 0 < ‖b - g j‖ := by linarith [hsep j]
    have hid : |inner ℝ (g j - b) u| =
        ‖b - g j‖ * |inner ℝ (radialDirection b (g j)) u| := by
      rw [show g j - b = -(b - g j) by abel, inner_neg_left, abs_neg,
        ← radialDirection_scale (hneq j), real_inner_smul_left, abs_mul,
        abs_of_pos hn]
      rw [radialDirection_scale (hneq j)]
    rw [hid] at hj
    nlinarith [hsep j, abs_nonneg (inner ℝ (radialDirection b (g j)) u)]
  let A := Finset.univ.filter (fun j => R j ∧ |inner ℝ (g j - b) u| < r)
  let B (e : Plane) := Finset.univ.filter (fun j => R j ∧ dist (radialDirection b (g j)) e ≤ 8 * r)
  have hsub : A ⊆ B (perp u) ∪ B (-perp u) := by
    intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    have hang := hangle j hj'.2
    rcases unit_circle_near_perpendicular (radialDirection_norm (hneq j)) hu with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'.1, by linarith⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'.1, by linarith⟩)
  have hc : (A.card : ℝ) ≤ ((B (perp u)).card : ℝ) + ((B (-perp u)).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hb (e : Plane) : ((B e).card : ℝ) ≤
      4 * K * (8 * r) ^ (1 / 4 : ℝ) * (Fintype.card J : ℝ) :=
    good_caps_ball_count (fun j => radialDirection b (g j)) R hδ hK hlast hgood e (8 * r) (by linarith)
  have hp : (8 * r) ^ (1 / 4 : ℝ) ≤ 4 * r ^ (1 / 4 : ℝ) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) hrpos.le]
    exact mul_le_mul_of_nonneg_right eight_rpow_quarter_le (by positivity)
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 8 * K))
    (Nat.cast_nonneg (α := ℝ) (Fintype.card J))
  nlinarith [hb (perp u), hb (-perp u)]

end WangZahlLot.Obl.wz_nonconcentrated_dot_products
