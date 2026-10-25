-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.GGGlue.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.GGGrainSlab
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.GGSlices

/-!
# Geometric glue for the global grains

* rescaled directions of a fibre stay near the fibre axis;
* two points of one unit tube are controlled by their heights;
* the normalized orthogonal component of a plane map is Lipschitz;
* slopes `a₁ / a₀` of unit vectors with `a₀ ≥ 1/2` are Lipschitz.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open Set Metric MeasureTheory
open scoped ENNReal Pointwise RealInnerProductSpace
open WangZahlLot.Obl.wz_separated_cover_refinement (Tube Dilate)

theorem orDir_sub_le {v w : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) {θ : ℝ} (hθ : θ < 1)
    (h : min ‖v - w‖ ‖v + w‖ ≤ θ) : ‖orDir w v - w‖ ≤ θ := by
  have hww : ⟪w, w⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hw]; norm_num
  have hin : ∀ u : Space, ⟪u, w⟫ ≤ ‖u‖ := fun u => by
    have := real_inner_le_norm u w
    rwa [hw, mul_one] at this
  rw [orDir]
  split_ifs with hvw
  · rcases min_le_iff.mp h with h1 | h1
    · exact h1
    · exfalso
      have e1 : ⟪v + w, w⟫ = ⟪v, w⟫ + 1 := by rw [inner_add_left, hww]
      have := hin (v + w)
      linarith
  · push Not at hvw
    rw [show -v - w = -(v + w) by abel, norm_neg]
    rcases min_le_iff.mp h with h1 | h1
    · exfalso
      have e1 : ⟪w - v, w⟫ = 1 - ⟪v, w⟫ := by rw [inner_sub_left, hww]
      have := hin (w - v)
      rw [norm_sub_rev] at h1
      linarith
    · exact h1

theorem ndir_self {w : Space} (hw : ‖w‖ = 1) (a : ℝ) : ndir w a w = w := by
  rw [ndir, aniso_self hw, hw, inv_one, one_smul]

/-- The rescaled direction of a fine tube in a coarse tube makes a small angle with the axis. -/
theorem inner_ndir_ge {τ ρ0 : ℝ} (hτ : 0 < τ) (hρ0 : 0 < ρ0) (hρ01 : ρ0 ≤ 1 / 100)
    {x v z0 w0 : Space} (hv : ‖v‖ = 1) (hw0 : ‖w0‖ = 1)
    (hT : tube τ x v ⊆ tube ρ0 z0 w0) :
    1 / 2 ≤ |⟪ndir w0 (1 / 100 / ρ0) (orDir w0 v), w0⟫| := by
  have hd := dir_close_of_subset hτ hv hw0 hT
  have ho := orDir_sub_le hv hw0 (by linarith) hd
  have ha : 1 ≤ 1 / 100 / ρ0 := by rw [le_div_iff₀ hρ0]; linarith
  have hov : ‖orDir w0 v‖ = 1 := by rw [norm_orDir, hv]
  have h1 := ndir_sub_le hw0 ha hov hw0
  rw [ndir_self hw0] at h1
  have h2 : ‖ndir w0 (1 / 100 / ρ0) (orDir w0 v) - w0‖ ≤ 8 / 100 := by
    calc _ ≤ 2 * (1 / 100 / ρ0) * ‖orDir w0 v - w0‖ := h1
      _ ≤ 2 * (1 / 100 / ρ0) * (4 * ρ0) := by gcongr
      _ = 8 / 100 := by field_simp; ring
  have hww : ⟪w0, w0⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hw0]; norm_num
  have e1 : ⟪ndir w0 (1 / 100 / ρ0) (orDir w0 v), w0⟫ =
      1 + ⟪ndir w0 (1 / 100 / ρ0) (orDir w0 v) - w0, w0⟫ := by
    rw [inner_sub_left, hww]; ring
  have h3 := abs_real_inner_le_norm (ndir w0 (1 / 100 / ρ0) (orDir w0 v) - w0) w0
  rw [hw0, mul_one] at h3
  rw [e1, abs_le] at *
  rw [abs_of_pos (by linarith [h3.1])]
  linarith [h3.1]

/-- Two points of one unit tube transverse to `w` are controlled by their heights. -/
theorem dist_le_of_heights {τ : ℝ} {x v w p q : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hvw : 1 / 2 ≤ |⟪v, w⟫|) (hp : p ∈ tube τ x v) (hq : q ∈ tube τ x v) :
    ‖p - q‖ ≤ 2 * |⟪p - q, w⟫| + 6 * τ := by
  obtain ⟨s, -, hs⟩ := exists_param_of_mem_Tube hp
  obtain ⟨t, -, ht⟩ := exists_param_of_mem_Tube hq
  have hw1 : ∀ u : Space, |⟪u, w⟫| ≤ ‖u‖ := fun u => by
    have := abs_real_inner_le_norm u w
    rwa [hw, mul_one] at this
  set e := p - (x + s • v) with he
  set e' := q - (x + t • v) with he'
  have hpq : p - q = (s - t) • v + (e - e') := by rw [he, he']; module
  have hin : ⟪p - q, w⟫ = (s - t) * ⟪v, w⟫ + (⟪e, w⟫ - ⟪e', w⟫) := by
    rw [hpq, inner_add_left, real_inner_smul_left, inner_sub_left]
  have h1 := hw1 e
  have h2 := hw1 e'
  have hst : |s - t| ≤ 2 * (|⟪p - q, w⟫| + 2 * τ) := by
    have h3 : |s - t| * |⟪v, w⟫| ≤ |⟪p - q, w⟫| + 2 * τ := by
      rw [← abs_mul]
      have : (s - t) * ⟪v, w⟫ = ⟪p - q, w⟫ - (⟪e, w⟫ - ⟪e', w⟫) := by rw [hin]; ring
      rw [this]
      calc |⟪p - q, w⟫ - (⟪e, w⟫ - ⟪e', w⟫)| ≤ |⟪p - q, w⟫| + |⟪e, w⟫ - ⟪e', w⟫| :=
            abs_sub _ _
        _ ≤ |⟪p - q, w⟫| + (|⟪e, w⟫| + |⟪e', w⟫|) := by gcongr; exact abs_sub _ _
        _ ≤ |⟪p - q, w⟫| + 2 * τ := by linarith
    have h4 : |s - t| * (1 / 2) ≤ |s - t| * |⟪v, w⟫| :=
      mul_le_mul_of_nonneg_left hvw (abs_nonneg _)
    linarith
  calc ‖p - q‖ = ‖(s - t) • v + (e - e')‖ := by rw [hpq]
    _ ≤ ‖(s - t) • v‖ + ‖e - e'‖ := norm_add_le _ _
    _ ≤ |s - t| + (‖e‖ + ‖e'‖) := by
        rw [norm_smul, hv, mul_one, Real.norm_eq_abs]
        gcongr
        exact norm_sub_le _ _
    _ ≤ 2 * (|⟪p - q, w⟫| + 2 * τ) + (τ + τ) := by linarith
    _ = 2 * |⟪p - q, w⟫| + 6 * τ := by ring

/-- The normalized orthogonal component of a unit vector almost orthogonal to `w`. -/
noncomputable def perpDir (w V : Space) : Space := ‖V - ⟪V, w⟫ • w‖⁻¹ • (V - ⟪V, w⟫ • w)

theorem norm_perpDir {w V : Space} (hV : ‖V‖ = 1) (hw : ‖w‖ = 1) (hVw : |⟪V, w⟫| ≤ 1 / 2) :
    ‖perpDir w V‖ = 1 := by
  have h := norm_perp_ge hV hw hVw
  rw [perpDir, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (by linarith)]

theorem inner_perpDir_self {w V : Space} (hw : ‖w‖ = 1) : ⟪perpDir w V, w⟫ = 0 := by
  have hww : ⟪w, w⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hw]; norm_num
  rw [perpDir, real_inner_smul_left, inner_sub_left, real_inner_smul_left, hww]
  ring

/-- The normalized orthogonal component is Lipschitz. -/
theorem perpDir_sub_le {w V V' : Space} (hV : ‖V‖ = 1) (hV' : ‖V'‖ = 1) (hw : ‖w‖ = 1)
    (hVw : |⟪V, w⟫| ≤ 1 / 2) (hV'w : |⟪V', w⟫| ≤ 1 / 2) :
    ‖perpDir w V - perpDir w V'‖ ≤ 8 * ‖V - V'‖ := by
  have h1 := norm_perp_ge hV hw hVw
  have h2 := norm_perp_ge hV' hw hV'w
  have h := norm_normalize_sub_le (p := V - ⟪V, w⟫ • w) (q := V' - ⟪V', w⟫ • w)
    (by linarith) (by linarith)
  have hproj : ‖(V - ⟪V, w⟫ • w) - (V' - ⟪V', w⟫ • w)‖ ≤ 2 * ‖V - V'‖ := by
    have e : (V - ⟪V, w⟫ • w) - (V' - ⟪V', w⟫ • w) = (V - V') - ⟪V - V', w⟫ • w := by
      rw [inner_sub_left]; module
    rw [e]
    calc ‖(V - V') - ⟪V - V', w⟫ • w‖ ≤ ‖V - V'‖ + ‖⟪V - V', w⟫ • w‖ := norm_sub_le _ _
      _ ≤ ‖V - V'‖ + ‖V - V'‖ := by
          rw [norm_smul, hw, mul_one, Real.norm_eq_abs]
          gcongr
          have := abs_real_inner_le_norm (V - V') w
          rwa [hw, mul_one] at this
      _ = 2 * ‖V - V'‖ := by ring
  calc ‖perpDir w V - perpDir w V'‖ ≤ 2 * ‖(V - ⟪V, w⟫ • w) - (V' - ⟪V', w⟫ • w)‖ /
        ‖V - ⟪V, w⟫ • w‖ := h
    _ ≤ 2 * (2 * ‖V - V'‖) / (1 / 2) := by
        apply div_le_div₀ (by positivity) (by linarith) (by norm_num) h1
    _ = 8 * ‖V - V'‖ := by ring

/-- Slopes of unit vectors with first coordinate at least `1/2` are Lipschitz. -/
theorem slope_sub_le {a b : Space} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (ha0 : 1 / 2 ≤ a 0)
    (hb0 : 1 / 2 ≤ b 0) : |a 1 / a 0 - b 1 / b 0| ≤ 8 * ‖a - b‖ := by
  have hc : ∀ (p : Space) (i : Fin 3), |p i| ≤ ‖p‖ := fun p i => by
    have := PiLp.norm_apply_le p i
    rwa [Real.norm_eq_abs] at this
  have ha1 : |a 1| ≤ 1 := ha ▸ hc a 1
  have hb1 : |b 1| ≤ 1 := hb ▸ hc b 1
  have h0 : |a 0 - b 0| ≤ ‖a - b‖ := abs_coord_sub_le a b 0
  have h1 : |a 1 - b 1| ≤ ‖a - b‖ := abs_coord_sub_le a b 1
  have ha0' : 0 < a 0 := by linarith
  have hb0' : 0 < b 0 := by linarith
  have e : a 1 / a 0 - b 1 / b 0 = ((a 1 - b 1) * b 0 + b 1 * (b 0 - a 0)) / (a 0 * b 0) := by
    field_simp; ring
  rw [e, abs_div, abs_of_pos (mul_pos ha0' hb0'), div_le_iff₀ (mul_pos ha0' hb0')]
  have hb0le : b 0 ≤ 1 := by have := hc b 0; rw [hb] at this; exact (le_abs_self _).trans this
  have hnum : |(a 1 - b 1) * b 0 + b 1 * (b 0 - a 0)| ≤ 2 * ‖a - b‖ := by
    calc |(a 1 - b 1) * b 0 + b 1 * (b 0 - a 0)| ≤ |(a 1 - b 1) * b 0| + |b 1 * (b 0 - a 0)| :=
          abs_add_le _ _
      _ = |a 1 - b 1| * |b 0| + |b 1| * |b 0 - a 0| := by rw [abs_mul, abs_mul]
      _ ≤ ‖a - b‖ * 1 + 1 * ‖a - b‖ := by
          rw [abs_of_pos hb0', abs_sub_comm (b 0)]
          gcongr
      _ = 2 * ‖a - b‖ := by ring
  have hab : 1 / 4 ≤ a 0 * b 0 := by nlinarith
  nlinarith [norm_nonneg (a - b)]

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
