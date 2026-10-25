-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_intermediate_twist_normalization.NormTube.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_intermediate_twist_normalization.Zoom
import Submission.WZ.Obl.wz_compact_offset_normalization.Basic

/-!
# The normalized tube of a tube of a class

A tube `T = tube δ x v` of a class with reference line `α + β z` of the coordinate `Xc`
(`|icX - α| ≤ 300/c²`, `|slX - β| ≤ 200/c²`) is zoomed by `zoom Z c α β`. Its image lies in a
plate around the zoomed axis line, which is nearly vertical. The *normalized tube* is the
`ρ`-tube, `ρ = 10 Z |c| δ`, around the unit segment of the zoomed axis line starting at the
height `nhb`, chosen so that

* the normalized tube lies in the thin cylinder `safeCyl r0 e` (`ntube_subset_safeCyl`);
* the zoomed tube lies in `W + 2e (W - W)` whenever the normalized tube lies in a convex `W`
  (`zoom_tube_subset`);
* the zoomed points of `T` at heights in `[nhb + δ, nhb + nuz - δ]` are within `ρ/2` of the
  normalized axis (`zoom_near_axis`).
-/

namespace WangZahlLot.Obl.wz_intermediate_twist_normalization

open Set Metric MeasureTheory
open scoped ENNReal Pointwise
open WangZahlLot.Obl.wz_small_twist_projection_estimate (Space tube lineAt Xc slX icX
  Xc_lineAt_eq norm_lineAt_le abs_slX_le lineAt_two coord_abs_le)
open WangZahlLot.Obl.wz_compact_offset_normalization (norm_sq_eq abs_coord_le_norm
  norm_le_of_sq_le segment_subset_of_tube mem_tube_iff mem_segment_param)

/-- The hypotheses on a tube of a class and on the zoom parameters. -/
structure CG (c δ Z ρ e r0 α β : ℝ) (x v : Space) : Prop where
  hc : 100 < |c|
  hδ : 0 < δ
  hδc : δ * c ^ 2 ≤ 1
  hv : ‖v‖ = 1
  hv2 : (1 / 2 : ℝ) ≤ |v 2|
  hT : tube δ x v ⊆ ball 0 1
  hα : |icX c x v - α| ≤ 300 / c ^ 2
  hβ : |slX c v - β| ≤ 200 / c ^ 2
  hβ3 : |β| ≤ 3
  hZ : 0 < Z
  hZc : 1 ≤ Z * |c|
  hZr : Z ≤ r0 * |c| / 1000
  hρ : ρ = 10 * Z * |c| * δ
  hr0 : 0 < r0
  he16 : 16 * r0 ^ 2 ≤ e
  he4 : e ≤ 1 / 4
  hρe : ρ ≤ e / 4
  hρr : ρ ≤ r0 / 4

/-- The vertical slope of the normalized tube. -/
noncomputable def nuz (Z c β : ℝ) (v : Space) : ℝ := |v 2| / ‖zlin Z c β v‖

/-- The direction of the normalized tube (pointing upwards). -/
noncomputable def ndir (Z c β : ℝ) (v : Space) : Space :=
  (v 2 / |v 2| / ‖zlin Z c β v‖) • zlin Z c β v

/-- The lower height of the axis. -/
noncomputable def nzlo (x v : Space) : ℝ := min (x 2) (x 2 + v 2)

/-- The starting height of the normalized axis. -/
noncomputable def nhb (Z c β ρ e : ℝ) (x v : Space) : ℝ :=
  max (-1 + e + 2 * ρ) (min (nzlo x v) (1 - e - 2 * ρ - nuz Z c β v))

/-- The base point of the normalized tube. -/
noncomputable def nbase (Z c α β ρ e : ℝ) (x v : Space) : Space :=
  zoom Z c α β (lineAt x v (nhb Z c β ρ e x v))

/-- The normalized tube. -/
noncomputable def ntube (Z c α β ρ e : ℝ) (x v : Space) : Set Space :=
  tube ρ (nbase Z c α β ρ e x v) (ndir Z c β v)

section

variable {c δ Z ρ e r0 α β : ℝ} {x v : Space}

theorem sq_le_sq_of_abs_le {a b : ℝ} (h : |a| ≤ b) : a ^ 2 ≤ b ^ 2 := by
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg a) h 2

/-- The linear part of the zoom stretches by at most `5 Z |c|`. -/
theorem CG.zlin_norm_le (h : CG c δ Z ρ e r0 α β x v) (w : Space) :
    ‖zlin Z c β w‖ ≤ 5 * Z * |c| * ‖w‖ := by
  have hc := h.hc
  have hZ := h.hZ
  set n := ‖w‖ with hn
  have hn0 : 0 ≤ n := norm_nonneg w
  have a0 := abs_coord_le_norm w 0
  have a1 := abs_coord_le_norm w 1
  have a2 := abs_coord_le_norm w 2
  have hb3 := h.hβ3
  have hc0 : 0 ≤ |c| := abs_nonneg c
  have e0 : |w 0 + c * w 1 - c * β * w 2| ≤ 41 / 10 * |c| * n := by
    calc |w 0 + c * w 1 - c * β * w 2| ≤ |w 0| + |c| * |w 1| + |c| * |β| * |w 2| := by
          calc _ ≤ |w 0 + c * w 1| + |c * β * w 2| := abs_sub _ _
            _ ≤ |w 0| + |c * w 1| + |c * β * w 2| := by gcongr; exact abs_add_le _ _
            _ = _ := by rw [abs_mul, abs_mul, abs_mul]
      _ ≤ n + |c| * n + |c| * 3 * n := by
          have : |c| * |β| * |w 2| ≤ |c| * 3 * n := by
            have := mul_le_mul hb3 a2 (abs_nonneg _) (by norm_num)
            calc |c| * |β| * |w 2| = |c| * (|β| * |w 2|) := by ring
              _ ≤ |c| * (3 * n) := by gcongr
              _ = |c| * 3 * n := by ring
          have h2 : |c| * |w 1| ≤ |c| * n := by gcongr
          linarith
      _ ≤ 41 / 10 * |c| * n := by nlinarith
  have e1 : |w 1 - β * w 2| ≤ 4 * n := by
    calc |w 1 - β * w 2| ≤ |w 1| + |β| * |w 2| := by
          rw [← abs_mul]; exact abs_sub _ _
      _ ≤ n + 3 * n := by
          have := mul_le_mul hb3 a2 (abs_nonneg _) (by norm_num)
          linarith
      _ = 4 * n := by ring
  have s0 := sq_le_sq_of_abs_le e0
  have s1 := sq_le_sq_of_abs_le e1
  have s2 := sq_le_sq_of_abs_le a2
  have hZc := h.hZc
  have hZc2 : 1 ≤ (Z * |c|) ^ 2 := by nlinarith
  have hcc : (100 : ℝ) ^ 2 ≤ |c| ^ 2 := pow_le_pow_left₀ (by norm_num) hc.le 2
  apply norm_le_of_sq_le (by positivity)
  simp only [zlin_apply_zero, zlin_apply_one, zlin_apply_two]
  have t0 : (Z * (w 0 + c * w 1 - c * β * w 2)) ^ 2 ≤ Z ^ 2 * (41 / 10 * |c| * n) ^ 2 := by
    rw [mul_pow]; gcongr
  have t1 : (Z * (w 1 - β * w 2)) ^ 2 ≤ Z ^ 2 * (4 * n) ^ 2 := by
    rw [mul_pow]; gcongr
  have t1' : Z ^ 2 * (4 * n) ^ 2 ≤ Z ^ 2 * |c| ^ 2 * n ^ 2 * (16 / 10000) := by
    have : (4 * n) ^ 2 ≤ |c| ^ 2 * n ^ 2 * (16 / 10000) := by nlinarith [sq_nonneg n]
    calc Z ^ 2 * (4 * n) ^ 2 ≤ Z ^ 2 * (|c| ^ 2 * n ^ 2 * (16 / 10000)) := by gcongr
      _ = _ := by ring
  have t2 : w 2 ^ 2 ≤ Z ^ 2 * |c| ^ 2 * n ^ 2 := by
    calc w 2 ^ 2 ≤ n ^ 2 := s2
      _ = 1 * n ^ 2 := by ring
      _ ≤ (Z * |c|) ^ 2 * n ^ 2 := by gcongr
      _ = Z ^ 2 * |c| ^ 2 * n ^ 2 := by ring
  have : Z ^ 2 * (41 / 10 * |c| * n) ^ 2 + Z ^ 2 * |c| ^ 2 * n ^ 2 * (16 / 10000) +
      Z ^ 2 * |c| ^ 2 * n ^ 2 ≤ (5 * Z * |c| * n) ^ 2 := by
    have hp : 0 ≤ Z ^ 2 * |c| ^ 2 * n ^ 2 := by positivity
    nlinarith
  linarith

/-- The zoomed axis line, first coordinate. -/
theorem zoom_lineAt_zero (hc : c ≠ 0) (hv2 : v 2 ≠ 0) (Z α β z : ℝ) :
    zoom Z c α β (lineAt x v z) 0 = Z * c * ((icX c x v - α) + (slX c v - β) * z) := by
  have hX := Xc_lineAt_eq c x v z
  rw [zoom_apply_zero, lineAt_two hv2]
  simp only [Xc] at hX
  have : lineAt x v z 0 + c * lineAt x v z 1 = c * (lineAt x v z 0 / c + lineAt x v z 1) := by
    field_simp
  rw [this, hX]
  ring

/-- The zoomed axis line, second coordinate. -/
theorem zoom_lineAt_one (hc : c ≠ 0) (hv2 : v 2 ≠ 0) (Z α β z : ℝ) :
    zoom Z c α β (lineAt x v z) 1 =
      Z * ((icX c x v - α) + (slX c v - β) * z - lineAt x v z 0 / c) := by
  have hX := Xc_lineAt_eq c x v z
  rw [zoom_apply_one, lineAt_two hv2]
  simp only [Xc] at hX
  have : lineAt x v z 1 = (lineAt x v z 0 / c + lineAt x v z 1) - lineAt x v z 0 / c := by ring
  rw [this, hX]
  ring

theorem CG.c_ne (h : CG c δ Z ρ e r0 α β x v) : c ≠ 0 := by
  have := h.hc
  intro h0; rw [h0, abs_zero] at this; linarith

theorem CG.v2_ne (h : CG c δ Z ρ e r0 α β x v) : v 2 ≠ 0 := by
  have := h.hv2
  intro h0; rw [h0, abs_zero] at this; linarith

theorem CG.c2_pos (h : CG c δ Z ρ e r0 α β x v) : 0 < c ^ 2 := by
  have := h.c_ne; positivity

/-- The zoomed axis line stays within `r0/2` of the vertical axis, first coordinate. -/
theorem CG.zoom_lineAt_zero_le (h : CG c δ Z ρ e r0 α β x v) {z : ℝ} (hz : |z| ≤ 1) :
    |zoom Z c α β (lineAt x v z) 0| ≤ r0 / 2 := by
  rw [zoom_lineAt_zero h.c_ne h.v2_ne]
  have hc := h.hc
  have hc0 : 0 < |c| := by linarith
  have hc2 := h.c2_pos
  have hZ := h.hZ
  have hs : |(icX c x v - α) + (slX c v - β) * z| ≤ 500 / c ^ 2 := by
    calc _ ≤ |icX c x v - α| + |(slX c v - β) * z| := abs_add_le _ _
      _ = |icX c x v - α| + |slX c v - β| * |z| := by rw [abs_mul]
      _ ≤ 300 / c ^ 2 + 200 / c ^ 2 * 1 := by
          gcongr
          · exact h.hα
          · exact h.hβ
      _ = 500 / c ^ 2 := by ring
  rw [abs_mul, abs_mul, abs_of_pos hZ]
  calc Z * |c| * |(icX c x v - α) + (slX c v - β) * z| ≤ Z * |c| * (500 / c ^ 2) := by gcongr
    _ = 500 * Z / |c| := by
        rw [← sq_abs c]; field_simp
    _ ≤ 500 * (r0 * |c| / 1000) / |c| := by gcongr; exact h.hZr
    _ = r0 / 2 := by field_simp; ring

/-- The zoomed axis line stays within `r0/100` of the vertical axis, second coordinate. -/
theorem CG.zoom_lineAt_one_le (h : CG c δ Z ρ e r0 α β x v) {z : ℝ} (hz : |z| ≤ 1) :
    |zoom Z c α β (lineAt x v z) 1| ≤ r0 / 100 := by
  rw [zoom_lineAt_one h.c_ne h.v2_ne]
  have hc := h.hc
  have hc0 : 0 < |c| := by linarith
  have hc2 := h.c2_pos
  have hZ := h.hZ
  have hL := norm_lineAt_le h.hδ h.hv h.hv2 h.hT hz
  have hL0 : |lineAt x v z 0| ≤ 5 := (coord_abs_le _ 0).trans hL
  have hs : |(icX c x v - α) + (slX c v - β) * z - lineAt x v z 0 / c| ≤ 10 / |c| := by
    calc _ ≤ |icX c x v - α| + |(slX c v - β) * z| + |lineAt x v z 0 / c| := by
          calc _ ≤ |(icX c x v - α) + (slX c v - β) * z| + |lineAt x v z 0 / c| := abs_sub _ _
            _ ≤ _ := by gcongr; exact abs_add_le _ _
      _ = |icX c x v - α| + |slX c v - β| * |z| + |lineAt x v z 0| / |c| := by
          rw [abs_mul, abs_div]
      _ ≤ 300 / c ^ 2 + 200 / c ^ 2 * 1 + 5 / |c| := by
          gcongr
          · exact h.hα
          · exact h.hβ
      _ ≤ 10 / |c| := by
          have h1 : 300 / c ^ 2 + 200 / c ^ 2 * 1 = 500 / |c| ^ 2 := by rw [sq_abs]; ring
          have h2 : 500 / |c| ^ 2 ≤ 5 / |c| := by
            rw [div_le_div_iff₀ (by positivity) hc0]
            nlinarith
          have h3 : 5 / |c| + 5 / |c| = 10 / |c| := by ring
          have h4 : 0 ≤ 5 / |c| := by positivity
          linarith
  rw [abs_mul, abs_of_pos hZ]
  calc Z * |(icX c x v - α) + (slX c v - β) * z - lineAt x v z 0 / c| ≤ Z * (10 / |c|) := by
        gcongr
    _ ≤ (r0 * |c| / 1000) * (10 / |c|) := by gcongr; exact h.hZr
    _ = r0 / 100 := by field_simp; ring

/-- The zoomed direction is nearly vertical: `|v 2| ≤ ‖zlin v‖ ≤ |v 2| (1 + e / 8)`. -/
theorem CG.zlin_v_le (h : CG c δ Z ρ e r0 α β x v) :
    ‖zlin Z c β v‖ ≤ |v 2| * (1 + e / 8) := by
  have hc := h.hc
  have hc0 : 0 < |c| := by linarith
  have hc2 := h.c2_pos
  have hZ := h.hZ
  have hv2 := h.hv2
  have hv20 : 0 < |v 2| := by linarith
  have he := h.he16
  have hr0 := h.hr0
  -- the slope of `Xc` along `v` is close to `β`
  have hXv : v 0 / c + v 1 = v 2 * slX c v := by
    simp only [slX, Xc]; field_simp [h.v2_ne]
  have e0 : zlin Z c β v 0 = Z * c * (v 2 * (slX c v - β)) := by
    rw [zlin_apply_zero]
    have : v 0 + c * v 1 = c * (v 0 / c + v 1) := by field_simp [h.c_ne]
    rw [this, hXv]; ring
  have e1 : zlin Z c β v 1 = Z * (v 2 * (slX c v - β) - v 0 / c) := by
    rw [zlin_apply_one]
    have : v 1 = (v 0 / c + v 1) - v 0 / c := by ring
    rw [this, hXv]; ring
  have hb := h.hβ
  have hv0 : |v 0| ≤ 1 := by rw [← h.hv]; exact abs_coord_le_norm v 0
  have hZr := h.hZr
  -- bounds on the two horizontal coordinates
  have b0 : |zlin Z c β v 0| ≤ |v 2| * (r0 / 5) := by
    rw [e0, abs_mul, abs_mul, abs_mul, abs_of_pos hZ]
    calc Z * |c| * (|v 2| * |slX c v - β|) ≤ Z * |c| * (|v 2| * (200 / c ^ 2)) := by gcongr
      _ = |v 2| * (200 * Z / |c|) := by rw [← sq_abs c]; field_simp
      _ ≤ |v 2| * (200 * (r0 * |c| / 1000) / |c|) := by gcongr
      _ = |v 2| * (r0 / 5) := by congr 1; field_simp; ring
  have b1 : |zlin Z c β v 1| ≤ |v 2| * (r0 / 100) := by
    rw [e1, abs_mul, abs_of_pos hZ]
    have : |v 2 * (slX c v - β) - v 0 / c| ≤ |v 2| * (10 / |c|) := by
      calc _ ≤ |v 2 * (slX c v - β)| + |v 0 / c| := abs_sub _ _
        _ = |v 2| * |slX c v - β| + |v 0| / |c| := by rw [abs_mul, abs_div]
        _ ≤ |v 2| * (200 / c ^ 2) + 1 / |c| := by
            have h1 := mul_le_mul_of_nonneg_left hb (abs_nonneg (v 2))
            have h2 : |v 0| / |c| ≤ 1 / |c| := div_le_div_of_nonneg_right hv0 hc0.le
            linarith
        _ ≤ |v 2| * (2 / |c|) + |v 2| * (2 / |c|) := by
            have ha : 200 / c ^ 2 ≤ 2 / |c| := by
              rw [← sq_abs c, div_le_div_iff₀ (by positivity) hc0]; nlinarith
            have hb' : 1 / |c| ≤ |v 2| * (2 / |c|) := by
              rw [show |v 2| * (2 / |c|) = (2 * |v 2|) / |c| by ring]
              exact div_le_div_of_nonneg_right (by linarith) hc0.le
            have := mul_le_mul_of_nonneg_left ha (abs_nonneg (v 2))
            linarith
        _ ≤ |v 2| * (10 / |c|) := by
            have : 0 ≤ |v 2| * (2 / |c|) := by positivity
            have h6 : |v 2| * (2 / |c|) * 5 = |v 2| * (10 / |c|) := by ring
            linarith
    calc Z * |v 2 * (slX c v - β) - v 0 / c| ≤ Z * (|v 2| * (10 / |c|)) := by gcongr
      _ ≤ (r0 * |c| / 1000) * (|v 2| * (10 / |c|)) := by gcongr
      _ = |v 2| * (r0 / 100) := by field_simp; ring
  have he0' : 0 ≤ e := by nlinarith
  apply norm_le_of_sq_le (mul_nonneg (abs_nonneg _) (by linarith))
  rw [zlin_apply_two]
  have s0 := sq_le_sq_of_abs_le b0
  have s1 := sq_le_sq_of_abs_le b1
  have hv22 : v 2 ^ 2 = |v 2| ^ 2 := (sq_abs _).symm
  have hr2 : r0 ^ 2 ≤ e / 16 := by linarith
  have key : (|v 2| * (r0 / 5)) ^ 2 + (|v 2| * (r0 / 100)) ^ 2 + |v 2| ^ 2 ≤
      (|v 2| * (1 + e / 8)) ^ 2 := by
    have hA : 0 ≤ |v 2| ^ 2 := by positivity
    have he0 : 0 ≤ e := by nlinarith
    have : (r0 / 5) ^ 2 + (r0 / 100) ^ 2 ≤ e / 4 := by nlinarith
    have h1 : (|v 2| * (r0 / 5)) ^ 2 + (|v 2| * (r0 / 100)) ^ 2 + |v 2| ^ 2 =
        |v 2| ^ 2 * ((r0 / 5) ^ 2 + (r0 / 100) ^ 2 + 1) := by ring
    have h2 : (|v 2| * (1 + e / 8)) ^ 2 = |v 2| ^ 2 * (1 + e / 8) ^ 2 := by ring
    rw [h1, h2]
    apply mul_le_mul_of_nonneg_left _ hA
    nlinarith [sq_nonneg e]
  linarith

theorem CG.v2_le_zlin (h : CG c δ Z ρ e r0 α β x v) : |v 2| ≤ ‖zlin Z c β v‖ := by
  have := abs_coord_le_norm (zlin Z c β v) 2
  rwa [zlin_apply_two] at this

theorem CG.zlin_pos (h : CG c δ Z ρ e r0 α β x v) : 0 < ‖zlin Z c β v‖ := by
  have := h.v2_le_zlin; have := h.hv2; linarith

/-- The normalized slope is close to `1`. -/
theorem CG.nuz_bounds (h : CG c δ Z ρ e r0 α β x v) :
    1 - e / 4 ≤ nuz Z c β v ∧ nuz Z c β v ≤ 1 := by
  have hN := h.zlin_pos
  have hle := h.zlin_v_le
  have hge := h.v2_le_zlin
  have hv2 := h.hv2
  have he : 0 ≤ e := by have := h.he16; have := h.hr0; nlinarith
  have he4 := h.he4
  unfold nuz
  constructor
  · rw [le_div_iff₀ hN]
    calc (1 - e / 4) * ‖zlin Z c β v‖ ≤ (1 - e / 4) * (|v 2| * (1 + e / 8)) := by
          gcongr; linarith
      _ ≤ |v 2| := by
          have : (1 - e / 4) * (1 + e / 8) ≤ 1 := by nlinarith
          nlinarith [abs_nonneg (v 2)]
  · rw [div_le_one hN]; exact hge

theorem CG.ndir_norm (h : CG c δ Z ρ e r0 α β x v) : ‖ndir Z c β v‖ = 1 := by
  have hN := h.zlin_pos
  have hv20 : 0 < |v 2| := by have := h.hv2; linarith
  rw [ndir, norm_smul, Real.norm_eq_abs, abs_div, abs_div, abs_abs, abs_of_pos hN,
    div_self hv20.ne', one_div, inv_mul_cancel₀ hN.ne']

theorem CG.ndir_two (h : CG c δ Z ρ e r0 α β x v) : ndir Z c β v 2 = nuz Z c β v := by
  have hN := h.zlin_pos
  have hv20 : 0 < |v 2| := by have := h.hv2; linarith
  rw [ndir, PiLp.smul_apply, smul_eq_mul, zlin_apply_two, nuz]
  have hsq : v 2 * v 2 = |v 2| * |v 2| := (abs_mul_abs_self _).symm
  rw [div_div, div_mul_eq_mul_div, div_eq_div_iff (mul_pos hv20 hN).ne' hN.ne', hsq]
  ring

/-- The zoomed axis line, parametrized along the normalized direction. -/
theorem CG.nbase_add_smul (h : CG c δ Z ρ e r0 α β x v) (t : ℝ) :
    nbase Z c α β ρ e x v + t • ndir Z c β v =
      zoom Z c α β (lineAt x v (nhb Z c β ρ e x v + t * nuz Z c β v)) := by
  have hN := h.zlin_pos
  have hv2 := h.v2_ne
  have hv20 : 0 < |v 2| := abs_pos.mpr hv2
  have hl : ∀ z, zoom Z c α β (lineAt x v z) = zoom Z c α β x + ((z - x 2) / v 2) • zlin Z c β v := by
    intro z
    rw [lineAt, zoom_add, map_smul]
  have key : v 2 / |v 2| = |v 2| / v 2 := by
    rw [div_eq_div_iff hv20.ne' hv2]
    exact (abs_mul_abs_self _).symm
  have hs : (nhb Z c β ρ e x v - x 2) / v 2 + t * (v 2 / |v 2| / ‖zlin Z c β v‖) =
      (nhb Z c β ρ e x v + t * nuz Z c β v - x 2) / v 2 := by
    rw [key, nuz]
    ring
  rw [nbase, hl, hl, ndir, smul_smul, add_assoc, ← add_smul, hs]

/-- Points of the axis segment, as points of the axis line. -/
theorem lineAt_of_segment {x v : Space} (hv2 : v 2 ≠ 0) (t : ℝ) :
    lineAt x v ((x + t • v) 2) = x + t • v := by
  rw [lineAt]
  congr 2
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- Heights of the axis segment. -/
theorem CG.height_bounds (h : CG c δ Z ρ e r0 α β x v) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    -1 + δ ≤ (x + t • v) 2 ∧ (x + t • v) 2 ≤ 1 - δ ∧
      nzlo x v ≤ (x + t • v) 2 ∧ (x + t • v) 2 ≤ nzlo x v + |v 2| := by
  have hseg := segment_subset_of_tube h.hδ h.hT
  have hmem : x + t • v ∈ segment ℝ x (x + v) := mem_segment_param.mpr ⟨t, ht, rfl⟩
  have hn := mem_closedBall_zero_iff.mp (hseg hmem)
  have habs := (abs_coord_le_norm (x + t • v) 2).trans hn
  have h2 : (x + t • v) 2 = x 2 + t * v 2 := by simp
  refine ⟨by linarith [(abs_le.mp habs).1], by linarith [(abs_le.mp habs).2], ?_, ?_⟩
  · rw [h2, nzlo]
    rcases le_total 0 (v 2) with hv | hv
    · exact (min_le_left _ _).trans (by nlinarith [ht.1])
    · exact (min_le_right _ _).trans (by nlinarith [ht.2])
  · rw [h2, nzlo]
    rcases le_total 0 (v 2) with hv | hv
    · rw [min_eq_left (by linarith), abs_of_nonneg hv]; nlinarith [ht.2]
    · rw [min_eq_right (by linarith), abs_of_nonpos hv]; nlinarith [ht.1]

/-- The window of the normalized axis. -/
theorem CG.nhb_bounds (h : CG c δ Z ρ e r0 α β x v) :
    -1 + e + 2 * ρ ≤ nhb Z c β ρ e x v ∧
      nhb Z c β ρ e x v + nuz Z c β v ≤ 1 - e - 2 * ρ ∧
      nhb Z c β ρ e x v - 2 * e * nuz Z c β v ≤ nzlo x v ∧
      nzlo x v + |v 2| ≤ nhb Z c β ρ e x v + nuz Z c β v + 2 * e * nuz Z c β v := by
  obtain ⟨hu1, hu2⟩ := h.nuz_bounds
  have he4 := h.he4
  have hρe := h.hρe
  have hρ0 : 0 ≤ ρ := by rw [h.hρ]; have := h.hZ; have := h.hδ; positivity
  have he0 : 0 ≤ e := by have := h.he16; have := h.hr0; nlinarith
  have hδ := h.hδ
  -- the axis heights lie in `[-1 + δ, 1 - δ]`
  have hb0 := h.height_bounds (t := 0) ⟨le_rfl, zero_le_one⟩
  have hb1 := h.height_bounds (t := 1) ⟨zero_le_one, le_rfl⟩
  have hlo : -1 + δ ≤ nzlo x v := by
    rw [nzlo]; simp only [zero_smul, add_zero, one_smul, PiLp.add_apply] at hb0 hb1
    exact le_min hb0.1 hb1.1
  have hhi : nzlo x v + |v 2| ≤ 1 - δ := by
    rw [nzlo]; simp only [zero_smul, add_zero, one_smul, PiLp.add_apply] at hb0 hb1
    rcases le_total 0 (v 2) with hv | hv
    · rw [min_eq_left (by linarith), abs_of_nonneg hv]; linarith [hb1.2.1]
    · rw [min_eq_right (by linarith), abs_of_nonpos hv]; linarith [hb0.2.1]
  have hv21 : |v 2| ≤ 1 := by rw [← h.hv]; exact abs_coord_le_norm v 2
  have key : e + 2 * ρ ≤ 2 * e * nuz Z c β v + δ := by nlinarith
  unfold nhb
  set A := -1 + e + 2 * ρ
  set B := 1 - e - 2 * ρ - nuz Z c β v
  refine ⟨le_max_left _ _, ?_, ?_, ?_⟩
  · rcases le_total A (min (nzlo x v) B) with hm | hm
    · rw [max_eq_right hm]; have := min_le_right (nzlo x v) B; linarith
    · rw [max_eq_left hm]; linarith
  · have hen : 0 ≤ e * nuz Z c β v := mul_nonneg he0 (by linarith)
    rcases le_total A (min (nzlo x v) B) with hm | hm
    · rw [max_eq_right hm]
      have := min_le_left (nzlo x v) B
      linarith
    · rw [max_eq_left hm]; linarith
  · have hge : min (nzlo x v) B ≤ max A (min (nzlo x v) B) := le_max_right _ _
    rcases le_total (nzlo x v) B with hm | hm
    · have h1 : min (nzlo x v) B = nzlo x v := min_eq_left hm
      rw [h1] at hge
      have : 1 ≤ nuz Z c β v + 2 * e * nuz Z c β v := by nlinarith
      have h2 : max A (min (nzlo x v) B) = max A (nzlo x v) := by rw [h1]
      rw [h2]
      linarith
    · have h1 : min (nzlo x v) B = B := min_eq_right hm
      rw [h1] at hge
      have h2 : max A (min (nzlo x v) B) = max A B := by rw [h1]
      rw [h2]
      linarith

/-- The zoomed points of the tube at heights inside the window are within `ρ / 2` of the
normalized axis. -/
theorem CG.zoom_near_axis (h : CG c δ Z ρ e r0 α β x v) {p : Space} (hp : p ∈ tube δ x v)
    (hlo : nhb Z c β ρ e x v + δ ≤ p 2) (hhi : p 2 ≤ nhb Z c β ρ e x v + nuz Z c β v - δ) :
    ∃ s ∈ segment ℝ (nbase Z c α β ρ e x v) (nbase Z c α β ρ e x v + ndir Z c β v),
      dist (zoom Z c α β p) s < ρ / 2 := by
  obtain ⟨t, ht, hpt⟩ := mem_tube_iff.mp hp
  obtain ⟨hu1, hu2⟩ := h.nuz_bounds
  have hu0 : 0 < nuz Z c β v := by have := h.he4; linarith
  set q := x + t • v with hq
  have hpq2 : |p 2 - q 2| < δ := by
    have := abs_coord_le_norm (p - q) 2
    rw [PiLp.sub_apply] at this
    rw [dist_eq_norm] at hpt
    linarith
  set s := (q 2 - nhb Z c β ρ e x v) / nuz Z c β v with hs
  have hs0 : 0 ≤ s := by
    rw [hs]; apply div_nonneg _ hu0.le; linarith [(abs_lt.mp hpq2).1, (abs_lt.mp hpq2).2]
  have hs1 : s ≤ 1 := by
    rw [hs, div_le_one hu0]; linarith [(abs_lt.mp hpq2).1, (abs_lt.mp hpq2).2]
  refine ⟨nbase Z c α β ρ e x v + s • ndir Z c β v,
    mem_segment_param.mpr ⟨s, ⟨hs0, hs1⟩, rfl⟩, ?_⟩
  rw [h.nbase_add_smul s]
  have hz : nhb Z c β ρ e x v + s * nuz Z c β v = q 2 := by
    rw [hs]; field_simp; ring
  rw [hz, hq, lineAt_of_segment h.v2_ne, dist_eq_norm, zoom_sub]
  calc ‖zlin Z c β (p - (x + t • v))‖ ≤ 5 * Z * |c| * ‖p - (x + t • v)‖ := h.zlin_norm_le _
    _ < 5 * Z * |c| * δ := by
        have : 0 < 5 * Z * |c| := by have := h.hZ; have := h.hc; positivity
        rw [← dist_eq_norm]
        exact mul_lt_mul_of_pos_left hpt this
    _ = ρ / 2 := by rw [h.hρ]; ring

/-- The normalized tube lies in the thin cylinder away from the poles. -/
theorem CG.ntube_subset_safeCyl (h : CG c δ Z ρ e r0 α β x v) :
    ntube Z c α β ρ e x v ⊆ safeCyl r0 e := by
  intro p hp
  obtain ⟨t, ht, hpt⟩ := mem_tube_iff.mp hp
  rw [h.nbase_add_smul t] at hpt
  obtain ⟨hA, hB, -, -⟩ := h.nhb_bounds
  obtain ⟨hu1, hu2⟩ := h.nuz_bounds
  set z := nhb Z c β ρ e x v + t * nuz Z c β v with hz
  have hu0 : 0 ≤ nuz Z c β v := by have := h.he4; linarith
  have hz1 : -1 + e + 2 * ρ ≤ z := by rw [hz]; nlinarith [ht.1]
  have hz2 : z ≤ 1 - e - 2 * ρ := by rw [hz]; nlinarith [ht.2]
  have he0 : 0 ≤ e := by have := h.he16; have := h.hr0; nlinarith
  have hρ0 : 0 ≤ ρ := by rw [h.hρ]; have := h.hZ; have := h.hδ; positivity
  have hzabs : |z| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  set s := zoom Z c α β (lineAt x v z)
  have hd : ‖p - s‖ < ρ := by rwa [dist_eq_norm] at hpt
  have d0 := abs_coord_le_norm (p - s) 0
  have d1 := abs_coord_le_norm (p - s) 1
  have d2 := abs_coord_le_norm (p - s) 2
  simp only [PiLp.sub_apply] at d0 d1 d2
  have s0 := h.zoom_lineAt_zero_le hzabs
  have s1 := h.zoom_lineAt_one_le hzabs
  have s2 : s 2 = z := by simp [s, zoom_apply_two, lineAt_two h.v2_ne]
  have hρr := h.hρr
  have hr0 := h.hr0
  refine ⟨?_, ?_⟩
  · have a0 : |p 0| ≤ r0 / 2 + ρ := by
      calc |p 0| = |s 0 + (p 0 - s 0)| := by ring_nf
        _ ≤ |s 0| + |p 0 - s 0| := abs_add_le _ _
        _ ≤ r0 / 2 + ρ := by linarith
    have a1 : |p 1| ≤ r0 / 100 + ρ := by
      calc |p 1| = |s 1 + (p 1 - s 1)| := by ring_nf
        _ ≤ |s 1| + |p 1 - s 1| := abs_add_le _ _
        _ ≤ r0 / 100 + ρ := by linarith
    have q0 := sq_le_sq_of_abs_le a0
    have q1 := sq_le_sq_of_abs_le a1
    nlinarith
  · have : |p 2 - s 2| < ρ := lt_of_le_of_lt d2 hd
    rw [s2] at this
    rw [abs_lt]
    constructor <;> linarith [(abs_lt.mp this).1, (abs_lt.mp this).2]

/-- **Inheritance of the convex count.** If the normalized tube lies in a convex set `W`, the
zoomed tube lies in `W + 2e (W - W)`. -/
theorem CG.zoom_tube_subset (h : CG c δ Z ρ e r0 α β x v) {W : Set Space} (hW : Convex ℝ W)
    (hTW : ntube Z c α β ρ e x v ⊆ W) :
    tube δ x v ⊆ zoom Z c α β ⁻¹' (W + (2 * e) • (W - W)) := by
  intro p hp
  obtain ⟨t, ht, hpt⟩ := mem_tube_iff.mp hp
  obtain ⟨hA, hB, hC, hD⟩ := h.nhb_bounds
  obtain ⟨hu1, hu2⟩ := h.nuz_bounds
  have hu0 : 0 < nuz Z c β v := by have := h.he4; linarith
  have he0 : 0 < e := by have := h.he16; have := h.hr0; nlinarith
  have hρ0 : 0 < ρ := by rw [h.hρ]; have := h.hZ; have := h.hδ; have := h.hc; positivity
  obtain ⟨-, -, hq1, hq2⟩ := h.height_bounds ht
  set q := x + t • v with hq
  set nb := nbase Z c α β ρ e x v
  set u := ndir Z c β v
  set s := (q 2 - nhb Z c β ρ e x v) / nuz Z c β v with hs
  have hsl : -(2 * e) ≤ s := by
    rw [hs, le_div_iff₀ hu0]; nlinarith
  have hsu : s ≤ 1 + 2 * e := by
    rw [hs, div_le_iff₀ hu0]; nlinarith
  have hzq : zoom Z c α β q = nb + s • u := by
    rw [h.nbase_add_smul s]
    have hz : nhb Z c β ρ e x v + s * nuz Z c β v = q 2 := by
      rw [hs]; field_simp; ring
    rw [hz, hq, lineAt_of_segment h.v2_ne]
  set s' := max 0 (min s 1) with hs'
  have hs'0 : 0 ≤ s' := le_max_left _ _
  have hs'1 : s' ≤ 1 := max_le zero_le_one (min_le_right _ _)
  have hd : |s - s'| ≤ 2 * e := by
    rw [hs', abs_le]
    constructor
    · rcases le_total s 1 with h1 | h1
      · rw [min_eq_left h1]
        rcases le_total 0 s with h0 | h0
        · rw [max_eq_right h0]; linarith
        · rw [max_eq_left h0]; linarith
      · rw [min_eq_right h1, max_eq_right zero_le_one]; linarith
    · rcases le_total s 1 with h1 | h1
      · rw [min_eq_left h1]
        rcases le_total 0 s with h0 | h0
        · rw [max_eq_right h0]; linarith
        · rw [max_eq_left h0]; linarith
      · rw [min_eq_right h1, max_eq_right zero_le_one]; linarith
  -- the main term lies in the normalized tube
  have hmain : nb + s' • u + zlin Z c β (p - q) ∈ W := by
    apply hTW
    refine mem_tube_iff.mpr ⟨s', ⟨hs'0, hs'1⟩, ?_⟩
    rw [dist_eq_norm, add_sub_cancel_left]
    calc ‖zlin Z c β (p - q)‖ ≤ 5 * Z * |c| * ‖p - q‖ := h.zlin_norm_le _
      _ ≤ 5 * Z * |c| * δ := by
          have : 0 ≤ 5 * Z * |c| := by have := h.hZ; positivity
          rw [← dist_eq_norm]; exact mul_le_mul_of_nonneg_left hpt.le this
      _ < ρ := by
          rw [h.hρ]
          have : 0 < Z * |c| * δ := by have := h.hZ; have := h.hδ; have := h.hc; positivity
          nlinarith
  -- the axis direction lies in `W - W`
  have hu_end : nb ∈ W ∧ nb + u ∈ W := by
    constructor
    · apply hTW
      exact mem_tube_iff.mpr ⟨0, ⟨le_rfl, zero_le_one⟩, by
        rw [zero_smul, add_zero]; exact (dist_self _).trans_lt hρ0⟩
    · apply hTW
      exact mem_tube_iff.mpr ⟨1, ⟨zero_le_one, le_rfl⟩, by
        rw [one_smul]; exact (dist_self _).trans_lt hρ0⟩
  have hsub : Convex ℝ (W - W) := hW.sub hW
  have hu_mem : u ∈ W - W := by
    have := Set.sub_mem_sub hu_end.2 hu_end.1
    simpa using this
  have hnu_mem : -u ∈ W - W := by
    have := Set.sub_mem_sub hu_end.1 hu_end.2
    simpa using this
  set lam := (s - s') / (2 * e) with hlam
  have hlam1 : |lam| ≤ 1 := by
    rw [hlam, abs_div, abs_of_pos (by linarith : (0 : ℝ) < 2 * e), div_le_one (by linarith)]
    exact hd
  have hlam_mem : lam • u ∈ W - W := by
    have ha : 0 ≤ (1 + lam) / 2 := by linarith [(abs_le.mp hlam1).1]
    have hb : 0 ≤ (1 - lam) / 2 := by linarith [(abs_le.mp hlam1).2]
    have := hsub hu_mem hnu_mem ha hb (by ring)
    have he : ((1 + lam) / 2) • u + ((1 - lam) / 2) • -u = lam • u := by
      rw [smul_neg, ← sub_eq_add_neg, ← sub_smul]
      congr 1
      ring
    rwa [he] at this
  have hfin : zoom Z c α β p = (nb + s' • u + zlin Z c β (p - q)) + (2 * e) • (lam • u) := by
    rw [smul_smul, hlam, mul_div_cancel₀ _ (by linarith : (2 * e) ≠ 0)]
    have : zoom Z c α β p = zoom Z c α β q + zlin Z c β (p - q) := by
      rw [← zoom_sub]; abel
    rw [this, hzq, sub_smul]
    abel
  rw [mem_preimage, hfin]
  exact Set.add_mem_add hmain (Set.smul_mem_smul_set hlam_mem)

end

end WangZahlLot.Obl.wz_intermediate_twist_normalization
