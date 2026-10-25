-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.TSGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_cover_refinement.Covers
import Submission.WZ.Obl.wz_direction_density_transfer.Geometry
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.Basic

/-!
# Geometry of nested unit tubes

Elementary facts used to build coarse families: containment of a unit tube in a
thicker unit tube pins down both endpoints, distances to segments are convex,
a contraction about the origin followed by symmetric re-extension keeps unit
length, and two tubes with a large overlap lie in a common thin cylinder.
-/

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_separated_cover_refinement (Tube Dilate)

/-- A point of a tube is close to a point of its axis. -/
theorem exists_param_of_mem_Tube {r : ℝ} {x v p : Space} (hp : p ∈ Tube r x v) :
    ∃ t ∈ Icc (0 : ℝ) 1, ‖p - (x + t • v)‖ < r := by
  obtain ⟨y, hy, hpy⟩ := mem_thickening_iff.mp hp
  rw [segment_eq_image'] at hy
  obtain ⟨t, ht, rfl⟩ := hy
  refine ⟨t, ht, ?_⟩
  rw [← dist_eq_norm]
  simpa using hpy

/-- A point close to a point of the axis lies in the tube. -/
theorem mem_Tube_of_param {r : ℝ} {x v p : Space} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hp : ‖p - (x + t • v)‖ < r) : p ∈ Tube r x v := by
  apply mem_thickening_iff.mpr
  refine ⟨x + t • v, ?_, ?_⟩
  · rw [segment_eq_image']
    exact ⟨t, ht, by simp⟩
  · rwa [dist_eq_norm]

theorem axis_mem_Tube {r : ℝ} (hr : 0 < r) (x v : Space) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    x + t • v ∈ Tube r x v :=
  mem_Tube_of_param ht (by simpa using hr)

/-- A unit tube inside a thicker unit tube has both endpoints within three times
the larger radius of the endpoints of the larger axis, in one of the two orders. -/
theorem endpoints_close {δ ρ : ℝ} (hδ : 0 < δ) {x v z w : Space}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hT : Tube δ x v ⊆ Tube ρ z w) :
    (‖x - z‖ ≤ 3 * ρ ∧ ‖x + v - (z + w)‖ ≤ 3 * ρ) ∨
      (‖x - (z + w)‖ ≤ 3 * ρ ∧ ‖x + v - z‖ ≤ 3 * ρ) := by
  obtain ⟨s, hs, hxs⟩ := exists_param_of_mem_Tube
    (hT (axis_mem_Tube hδ x v (t := 0) ⟨le_rfl, zero_le_one⟩))
  obtain ⟨t, ht, hxt⟩ := exists_param_of_mem_Tube
    (hT (axis_mem_Tube hδ x v (t := 1) ⟨zero_le_one, le_rfl⟩))
  simp only [zero_smul, add_zero, one_smul] at hxs hxt
  have hvw : ‖v - (t - s) • w‖ < 2 * ρ := by
    have he : v - (t - s) • w = (x + v - (z + t • w)) - (x - (z + s • w)) := by module
    rw [he]
    exact (norm_sub_le _ _).trans_lt (by linarith)
  have hts : 1 - 2 * ρ < |t - s| := by
    have h1 : ‖v‖ - ‖(t - s) • w‖ ≤ ‖v - (t - s) • w‖ := norm_sub_norm_le _ _
    rw [hv, norm_smul, hw, mul_one, Real.norm_eq_abs] at h1
    linarith
  rcases le_or_gt 0 (t - s) with hpos | hneg
  · rw [abs_of_nonneg hpos] at hts
    left
    constructor
    · have he : x - z = (x - (z + s • w)) + s • w := by module
      rw [he]
      calc ‖(x - (z + s • w)) + s • w‖ ≤ ‖x - (z + s • w)‖ + ‖s • w‖ := norm_add_le _ _
        _ ≤ ρ + s := by
          rw [norm_smul, hw, mul_one, Real.norm_eq_abs, abs_of_nonneg hs.1]
          linarith
        _ ≤ 3 * ρ := by linarith [ht.2]
    · have he : x + v - (z + w) = (x + v - (z + t • w)) - (1 - t) • w := by module
      rw [he]
      calc ‖(x + v - (z + t • w)) - (1 - t) • w‖ ≤
            ‖x + v - (z + t • w)‖ + ‖(1 - t) • w‖ := norm_sub_le _ _
        _ ≤ ρ + (1 - t) := by
          rw [norm_smul, hw, mul_one, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
          linarith
        _ ≤ 3 * ρ := by linarith [hs.1]
  · rw [abs_of_neg hneg] at hts
    right
    constructor
    · have he : x - (z + w) = (x - (z + s • w)) - (1 - s) • w := by module
      rw [he]
      calc ‖(x - (z + s • w)) - (1 - s) • w‖ ≤ ‖x - (z + s • w)‖ + ‖(1 - s) • w‖ :=
            norm_sub_le _ _
        _ ≤ ρ + (1 - s) := by
          rw [norm_smul, hw, mul_one, Real.norm_eq_abs, abs_of_nonneg (by linarith [hs.2])]
          linarith
        _ ≤ 3 * ρ := by linarith [ht.1]
    · have he : x + v - z = (x + v - (z + t • w)) + t • w := by module
      rw [he]
      calc ‖(x + v - (z + t • w)) + t • w‖ ≤ ‖x + v - (z + t • w)‖ + ‖t • w‖ :=
            norm_add_le _ _
        _ ≤ ρ + t := by
          rw [norm_smul, hw, mul_one, Real.norm_eq_abs, abs_of_nonneg ht.1]
          linarith
        _ ≤ 3 * ρ := by linarith [hs.2]

/-- Endpoint closeness passes to every point of the axis. -/
theorem axis_close_of_endpoints {x v z w : Space} {d : ℝ}
    (h0 : ‖x - z‖ ≤ d) (h1 : ‖x + v - (z + w)‖ ≤ d) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖(x + t • v) - (z + t • w)‖ ≤ d := by
  have he : (x + t • v) - (z + t • w) = (1 - t) • (x - z) + t • (x + v - (z + w)) := by
    module
  rw [he]
  calc ‖(1 - t) • (x - z) + t • (x + v - (z + w))‖ ≤
        ‖(1 - t) • (x - z)‖ + ‖t • (x + v - (z + w))‖ := norm_add_le _ _
    _ = (1 - t) * ‖x - z‖ + t * ‖x + v - (z + w)‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (by linarith [ht.2]), abs_of_nonneg ht.1]
    _ ≤ (1 - t) * d + t * d := by
      gcongr
      · linarith [ht.2]
      · exact ht.1
    _ = d := by ring

/-- Every point of the larger axis is within `3ρ` of the smaller axis. -/
theorem axis_close_of_subset {δ ρ : ℝ} (hδ : 0 < δ) {x v z w : Space}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hT : Tube δ x v ⊆ Tube ρ z w)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ s ∈ Icc (0 : ℝ) 1, ‖(z + t • w) - (x + s • v)‖ ≤ 3 * ρ := by
  rcases endpoints_close hδ hv hw hT with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · refine ⟨t, ht, ?_⟩
    rw [norm_sub_rev]
    exact axis_close_of_endpoints h0 h1 ht
  · refine ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
    have h := axis_close_of_endpoints (x := x + v) (v := -v) (z := z) (w := w)
      (by simpa using h1) (by simpa [add_neg_cancel_right] using h0) ht
    have he : (x + v + t • -v) = x + (1 - t) • v := by module
    rw [he] at h
    rw [norm_sub_rev]
    exact h

/-- Every point of the smaller axis is within the larger radius of the larger axis. -/
theorem axis_mem_of_subset {δ ρ : ℝ} (hδ : 0 < δ) {x v z w : Space}
    (hT : Tube δ x v ⊆ Tube ρ z w) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ s ∈ Icc (0 : ℝ) 1, ‖(x + t • v) - (z + s • w)‖ < ρ :=
  exists_param_of_mem_Tube (hT (axis_mem_Tube hδ x v ht))

/-- Axis points of a tube in the unit ball have norm at most `1 - δ`. -/
theorem axis_norm_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) {x v : Space}
    (hT : Tube δ x v ⊆ ball 0 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖x + t • v‖ ≤ 1 - δ := by
  set p := x + t • v
  by_contra hlt
  push Not at hlt
  have hp0 : 0 < ‖p‖ := by linarith
  have hp1 : ‖p‖ < 1 := by simpa using hT (axis_mem_Tube hδ x v ht)
  set ε := (δ + 1 - ‖p‖) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hεδ : ε < δ := by dsimp [ε]; linarith
  set q := p + (ε / ‖p‖) • p
  have hq : q ∈ Tube δ x v := by
    apply mem_Tube_of_param ht
    have he : q - (x + t • v) = (ε / ‖p‖) • p := by simp [q, p]
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hε hp0),
      div_mul_cancel₀ _ hp0.ne']
    exact hεδ
  have hqn : ‖q‖ = ‖p‖ + ε := by
    have he : q = (1 + ε / ‖p‖) • p := by simp only [q]; module
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), add_mul,
      div_mul_cancel₀ _ hp0.ne', one_mul]
  have hq1 : ‖q‖ < 1 := by simpa using hT hq
  dsimp [ε] at hqn
  linarith

/-! ### Contraction about the origin and symmetric re-extension -/

/-- The unit tube obtained by contracting the axis of `Tube · z w` by `1 - 2e`
about the origin and re-extending it by `e` at both ends. -/
def ntube (r e : ℝ) (z w : Space) : Set Space :=
  Tube r ((1 - 2 * e) • z - e • w) w

/-- Points of the contracted tube lie in the normalized tube. -/
theorem smul_mem_ntube {r ρ e : ℝ} (he : 0 ≤ e) (he1 : 2 * e < 1)
    (hrρ : (1 - 2 * e) * ρ ≤ r) {z w p : Space} (hp : p ∈ Tube ρ z w) :
    (1 - 2 * e) • p ∈ ntube r e z w := by
  obtain ⟨t, ht, hpt⟩ := exists_param_of_mem_Tube hp
  have hl : 0 < 1 - 2 * e := by linarith
  apply mem_Tube_of_param (t := e + (1 - 2 * e) * t)
  · constructor
    · nlinarith [ht.1]
    · nlinarith [ht.2]
  · have heq : (1 - 2 * e) • p - ((1 - 2 * e) • z - e • w + (e + (1 - 2 * e) * t) • w) =
        (1 - 2 * e) • (p - (z + t • w)) := by module
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hl]
    calc (1 - 2 * e) * ‖p - (z + t • w)‖ < (1 - 2 * e) * ρ :=
          mul_lt_mul_of_pos_left hpt hl
      _ ≤ r := hrρ

/-- An axis point of the normalized tube, written through the original axis. -/
theorem ntube_axis_decomp {e : ℝ} (he : 0 ≤ e) (he1 : 2 * e < 1) (z w : Space)
    {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) 1) :
    ∃ τ ∈ Icc (0 : ℝ) 1, ∃ μ : ℝ, |μ| ≤ e ∧
      (1 - 2 * e) • z - e • w + σ • w = (1 - 2 * e) • (z + τ • w) + μ • w := by
  have hl : 0 < 1 - 2 * e := by linarith
  rcases lt_or_ge (σ - e) 0 with h1 | h1
  · refine ⟨0, ⟨le_rfl, zero_le_one⟩, σ - e, ?_, by module⟩
    rw [abs_of_neg h1]
    linarith [hσ.1]
  rcases lt_or_ge (1 - 2 * e) (σ - e) with h2 | h2
  · refine ⟨1, ⟨zero_le_one, le_rfl⟩, σ - e - (1 - 2 * e), ?_, by module⟩
    rw [abs_of_pos (by linarith)]
    linarith [hσ.2]
  · refine ⟨(σ - e) / (1 - 2 * e), ⟨div_nonneg h1 hl.le, (div_le_one hl).mpr h2⟩,
      0, by simp [he], ?_⟩
    rw [zero_smul, add_zero, smul_add, smul_smul, mul_div_cancel₀ _ hl.ne']
    module

/-- The normalized tube stays in the unit ball. -/
theorem ntube_subset_ball {r e R : ℝ} (he : 0 ≤ e) (he1 : 2 * e < 1) {z w : Space}
    (hw : ‖w‖ = 1) (hR : ∀ t ∈ Icc (0 : ℝ) 1, ‖z + t • w‖ ≤ R)
    (hsmall : (1 - 2 * e) * R + e + r ≤ 1) : ntube r e z w ⊆ ball 0 1 := by
  intro q hq
  obtain ⟨σ, hσ, hqσ⟩ := exists_param_of_mem_Tube hq
  obtain ⟨τ, hτ, μ, hμ, heq⟩ := ntube_axis_decomp he he1 z w hσ
  rw [heq] at hqσ
  rw [mem_ball_zero_iff]
  have hl : 0 ≤ 1 - 2 * e := by linarith
  calc ‖q‖ ≤ ‖q - ((1 - 2 * e) • (z + τ • w) + μ • w)‖ +
        ‖(1 - 2 * e) • (z + τ • w) + μ • w‖ := by
          have := norm_add_le (q - ((1 - 2 * e) • (z + τ • w) + μ • w))
            ((1 - 2 * e) • (z + τ • w) + μ • w)
          simpa using this
    _ < r + ((1 - 2 * e) * R + e) := by
        apply add_lt_add_of_lt_of_le hqσ
        calc ‖(1 - 2 * e) • (z + τ • w) + μ • w‖ ≤
              ‖(1 - 2 * e) • (z + τ • w)‖ + ‖μ • w‖ := norm_add_le _ _
          _ = (1 - 2 * e) * ‖z + τ • w‖ + |μ| := by
            rw [norm_smul, norm_smul, hw, mul_one, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg hl]
          _ ≤ (1 - 2 * e) * R + e := by
            gcongr
            exact hR τ hτ
    _ ≤ 1 := by linarith

/-- Pointwise closeness of axes gives containment of normalized tubes. -/
theorem ntube_subset_ntube {r r' e d : ℝ} (he : 0 ≤ e) (he1 : 2 * e < 1)
    {z w z' w' : Space}
    (hclose : ∀ t ∈ Icc (0 : ℝ) 1, ∃ s ∈ Icc (0 : ℝ) 1,
      ‖(z + t • w) - (z' + s • w')‖ ≤ d)
    (hw : ‖w‖ = 1) (hr : r + e + d ≤ r') : ntube r e z w ⊆ ntube r' e z' w' := by
  intro q hq
  obtain ⟨σ, hσ, hqσ⟩ := exists_param_of_mem_Tube hq
  obtain ⟨τ, hτ, μ, hμ, heq⟩ := ntube_axis_decomp he he1 z w hσ
  rw [heq] at hqσ
  obtain ⟨s, hs, hd⟩ := hclose τ hτ
  have hl : 0 ≤ 1 - 2 * e := by linarith
  apply mem_Tube_of_param (t := e + (1 - 2 * e) * s)
  · constructor
    · nlinarith [hs.1]
    · nlinarith [hs.2]
  · have hsplit : q - ((1 - 2 * e) • z' - e • w' + (e + (1 - 2 * e) * s) • w') =
        (q - ((1 - 2 * e) • (z + τ • w) + μ • w)) + μ • w +
          (1 - 2 * e) • ((z + τ • w) - (z' + s • w')) := by module
    rw [hsplit]
    calc ‖(q - ((1 - 2 * e) • (z + τ • w) + μ • w)) + μ • w +
          (1 - 2 * e) • ((z + τ • w) - (z' + s • w'))‖ ≤
          ‖q - ((1 - 2 * e) • (z + τ • w) + μ • w)‖ + ‖μ • w‖ +
            ‖(1 - 2 * e) • ((z + τ • w) - (z' + s • w'))‖ := by
            exact (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ < r + e + d := by
          rw [norm_smul, norm_smul, hw, mul_one, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg hl]
          have h1 : (1 - 2 * e) * ‖(z + τ • w) - (z' + s • w')‖ ≤ d := by
            calc (1 - 2 * e) * ‖(z + τ • w) - (z' + s • w')‖ ≤ 1 * d :=
                  mul_le_mul (by linarith) hd (norm_nonneg _) zero_le_one
              _ = d := one_mul d
          linarith
      _ ≤ r' := hr

/-! ### Large overlaps force nearly coincident axes -/

/-- Two unit tubes of radius `R` whose overlap exceeds half of the first: every axis
point of the second is close to the line of the first, at a bounded parameter. -/
theorem overlap_axis_close {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1 / 10000) {a u b u' : Space}
    (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1)
    (hov : (1 / 2 : ℝ≥0∞) * volume (Tube R a u) < volume (Tube R a u ∩ Tube R b u')) :
    ∀ τ ∈ Icc (0 : ℝ) 1, ∃ σ ∈ Icc (-2 : ℝ) 3, ‖(b + τ • u') - (a + σ • u)‖ < 10000 * R := by
  classical
  let I : Set ℝ := {t | t ∈ Icc (0 : ℝ) 1 ∧
    ∃ s ∈ Icc (0 : ℝ) 1, ‖(a + t • u) - (b + s • u')‖ < 2 * R}
  have hsub : Tube R a u ∩ Tube R b u' ⊆ thickening R ((fun t => a + t • u) '' I) := by
    rintro p ⟨hp1, hp2⟩
    obtain ⟨t, ht, hpt⟩ := exists_param_of_mem_Tube hp1
    obtain ⟨s, hs, hps⟩ := exists_param_of_mem_Tube hp2
    apply mem_thickening_iff.mpr
    refine ⟨a + t • u, ⟨t, ⟨ht, s, hs, ?_⟩, rfl⟩, ?_⟩
    · calc ‖(a + t • u) - (b + s • u')‖ = ‖(p - (b + s • u')) - (p - (a + t • u))‖ := by
            congr 1; abel
        _ ≤ ‖p - (b + s • u')‖ + ‖p - (a + t • u)‖ := norm_sub_le _ _
        _ < 2 * R := by linarith
    · rw [dist_eq_norm]; exact hpt
  have hfar : ∃ t1 ∈ I, ∃ t2 ∈ I, 1 / 1000 < t2 - t1 := by
    by_contra hno
    push Not at hno
    have hdiam : ∀ s ∈ I, ∀ t ∈ I, dist s t ≤ 1 / 1000 := by
      intro s hs t ht
      rw [Real.dist_eq, abs_le]
      constructor
      · linarith [hno s hs t ht]
      · linarith [hno t ht s hs]
    have hup := WangZahlLot.Obl.wz_direction_density_transfer.segment_piece_volume_upper a u hu
      (T := I) (fun t ht => ht.1) hR (by norm_num : (0 : ℝ) ≤ 1 / 1000) hdiam
    have hlow := WangZahlLot.Obl.wz_direction_density_transfer.tube_volume_lower hR a u hu
    have h1 : volume (Tube R a u ∩ Tube R b u') ≤
        ENNReal.ofReal (128 * (2 * (1 / 1000) + R) * R ^ 2) :=
      (measure_mono hsub).trans hup
    have h2 : ENNReal.ofReal (128 * (2 * (1 / 1000) + R) * R ^ 2) ≤
        (1 / 2 : ℝ≥0∞) * ENNReal.ofReal (R ^ 2) := by
      have hhalf : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2) := by
        rw [ENNReal.ofReal_div_of_pos two_pos]; simp
      rw [hhalf, ← ENNReal.ofReal_mul (by norm_num)]
      apply ENNReal.ofReal_le_ofReal
      have hR2 : 0 ≤ R ^ 2 := sq_nonneg R
      nlinarith
    have h3 : (1 / 2 : ℝ≥0∞) * ENNReal.ofReal (R ^ 2) ≤
        (1 / 2 : ℝ≥0∞) * volume (Tube R a u) := by gcongr
    exact absurd (hov.trans_le (h1.trans (h2.trans h3))) (lt_irrefl _)
  obtain ⟨t1, ⟨ht1, s1, hs1, h1⟩, t2, ⟨ht2, s2, hs2, h2⟩, hgap⟩ := hfar
  have hE : ‖(s2 - s1) • u' - (t2 - t1) • u‖ < 4 * R := by
    have he : (s2 - s1) • u' - (t2 - t1) • u =
        ((a + t1 • u) - (b + s1 • u')) - ((a + t2 • u) - (b + s2 • u')) := by module
    rw [he]
    exact (norm_sub_le _ _).trans_lt (by linarith)
  have hnorms : abs ((t2 - t1) - abs (s2 - s1)) < 4 * R := by
    have h := abs_norm_sub_norm_le ((s2 - s1) • u') ((t2 - t1) • u)
    rw [norm_smul, norm_smul, hu, hu', mul_one, mul_one, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < t2 - t1), abs_sub_comm] at h
    exact h.trans_lt hE
  have hΔs : 6 / 10000 < |s2 - s1| := by
    have := (abs_lt.mp hnorms).2
    linarith
  have hΔs0 : 0 < |s2 - s1| := by linarith
  have hratio : (t2 - t1) / |s2 - s1| ≤ 5 / 3 := by
    rw [div_le_iff₀ hΔs0]
    have := (abs_lt.mp hnorms).2
    linarith
  intro τ hτ
  refine ⟨t1 + (τ - s1) * (t2 - t1) / (s2 - s1), ?_, ?_⟩
  · have hτs : |τ - s1| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [hτ.1, hτ.2, hs1.1, hs1.2]
    have hb : |(τ - s1) * (t2 - t1) / (s2 - s1)| ≤ 5 / 3 := by
      rw [mul_div_assoc, abs_mul, abs_div, abs_of_pos (by linarith : (0 : ℝ) < t2 - t1)]
      calc |τ - s1| * ((t2 - t1) / |s2 - s1|) ≤ 1 * (5 / 3) := by
            apply mul_le_mul hτs hratio (div_nonneg (by linarith) hΔs0.le) zero_le_one
        _ = 5 / 3 := one_mul _
    rw [abs_le] at hb
    constructor <;> linarith [ht1.1, ht1.2, hb.1, hb.2]
  · have hs0 : s2 - s1 ≠ 0 := by
      intro h0; rw [h0, abs_zero] at hΔs0; exact lt_irrefl _ hΔs0
    have heq : (b + τ • u') - (a + (t1 + (τ - s1) * (t2 - t1) / (s2 - s1)) • u) =
        ((b + s1 • u') - (a + t1 • u)) +
          ((τ - s1) / (s2 - s1)) • ((s2 - s1) • u' - (t2 - t1) • u) := by
      rw [smul_sub, smul_smul, smul_smul, div_mul_cancel₀ _ hs0]
      have : (τ - s1) / (s2 - s1) * (t2 - t1) = (τ - s1) * (t2 - t1) / (s2 - s1) := by ring
      rw [this]
      module
    rw [heq]
    have hτs : |τ - s1| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [hτ.1, hτ.2, hs1.1, hs1.2]
    calc ‖((b + s1 • u') - (a + t1 • u)) +
          ((τ - s1) / (s2 - s1)) • ((s2 - s1) • u' - (t2 - t1) • u)‖ ≤
          ‖(b + s1 • u') - (a + t1 • u)‖ +
            ‖((τ - s1) / (s2 - s1)) • ((s2 - s1) • u' - (t2 - t1) • u)‖ := norm_add_le _ _
      _ ≤ ‖(b + s1 • u') - (a + t1 • u)‖ + (10000 / 6) * (4 * R) := by
          gcongr
          rw [norm_smul, Real.norm_eq_abs, abs_div]
          apply mul_le_mul _ hE.le (norm_nonneg _) (by norm_num)
          rw [div_le_iff₀ hΔs0]
          nlinarith
      _ < 2 * R + (10000 / 6) * (4 * R) := by
          rw [norm_sub_rev]
          linarith
      _ ≤ 10000 * R := by nlinarith

/-! ### A long thin container and the packing bound inside it -/

/-- The cylinder of radius `10⁹ r` around the axis `z + t w`, `|t| ≤ 50`. -/
def bigContainer (r : ℝ) (z w : Space) : Set Space :=
  AffineMap.homothety (z - (50 : ℝ) • w) (100 : ℝ) ''
    Tube (10000000 * r) (z - (50 : ℝ) • w) w

theorem mem_bigContainer {r : ℝ} {z w p : Space} {t : ℝ}
    (ht : |t| ≤ 50) (hp : ‖p - (z + t • w)‖ < 1000000000 * r) :
    p ∈ bigContainer r z w := by
  let b := z - (50 : ℝ) • w
  let q := b + (1 / 100 : ℝ) • (p - b)
  have hq : q ∈ Tube (10000000 * r) b w := by
    apply mem_Tube_of_param (t := (t + 50) / 100)
    · obtain ⟨ht0, ht1⟩ := abs_le.mp ht
      constructor <;> linarith
    · have he : q - (b + ((t + 50) / 100) • w) = (1 / 100 : ℝ) • (p - (z + t • w)) := by
        dsimp [q, b]
        module
      rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
      linarith
  refine ⟨q, hq, ?_⟩
  rw [AffineMap.homothety_apply]
  simp only [vsub_eq_sub, vadd_eq_add]
  dsimp [q, b]
  module

theorem bigContainer_volume {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1 / 10000000)
    (z w : Space) (hw : ‖w‖ = 1) :
    volume (bigContainer r z w) ≤ ENNReal.ofReal (10 ^ 23 * r ^ 2) := by
  have h := WangZahlLot.Obl.wz_direction_density_transfer.segment_piece_volume_upper
    (z - (50 : ℝ) • w) w hw (T := Icc 0 1) subset_rfl (r := 10000000 * r) (A := 1)
    (by positivity) zero_le_one (by
      intro s hs t ht
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith [hs.1, hs.2, ht.1, ht.2])
  have he : (fun t : ℝ => z - (50 : ℝ) • w + t • w) '' Icc 0 1 =
      segment ℝ (z - (50 : ℝ) • w) (z - (50 : ℝ) • w + w) := by
    rw [segment_eq_image']
    simp
  rw [he] at h
  rw [bigContainer, Measure.addHaar_image_homothety, finrank_euclideanSpace_fin]
  calc _ ≤ ENNReal.ofReal (|(100 : ℝ) ^ 3|) *
        ENNReal.ofReal (128 * (2 * 1 + 10000000 * r) * (10000000 * r) ^ 2) :=
          mul_le_mul' le_rfl h
    _ ≤ _ := by
      rw [← ENNReal.ofReal_mul (abs_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      norm_num
      nlinarith [mul_le_mul_of_nonneg_right hr1 (sq_nonneg r)]

/-- An absolute bound for the number of pairwise half-distinct tubes in a container. -/
def bigBound : ℕ := 10 ^ 52

/-- Half-distinct tubes of radius `r` inside one big container are boundedly many. -/
theorem card_le_of_subset_bigContainer {k : ℕ} {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1 / 10000000)
    (z w : Fin k → Space) (hw : ∀ j, ‖w j‖ = 1)
    (hsep : ∀ j j', j ≠ j' → volume (Tube r (z j) (w j) ∩ Tube r (z j') (w j')) ≤
      (1 / 2 : ℝ≥0∞) * volume (Tube r (z j) (w j)))
    (z0 w0 : Space) (hw0 : ‖w0‖ = 1) (S : Finset (Fin k))
    (hS : ∀ j ∈ S, Tube r (z j) (w j) ⊆ bigContainer r z0 w0) :
    S.card ≤ bigBound := by
  classical
  let e : Fin S.card → Fin k := fun a => (S.equivFin.symm a).val
  have he : Function.Injective e := Subtype.val_injective.comp S.equivFin.symm.injective
  have hvol := bigContainer_volume hr hr1 z0 w0 hw0
  have hpack := WangZahlLot.Obl.wz_convex_container_tube_packing.packing hr
    (fun a => z (e a)) (fun a => w (e a))
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvol) (fun a => hw (e a))
    (fun a => hS _ (S.equivFin.symm a).property)
    (fun a b hab => hsep (e a) (e b) (he.ne hab))
  have hle : ENNReal.ofReal ((S.card : ℝ) * r ^ 4) ≤
      ENNReal.ofReal ((bigBound : ℝ) * r ^ 4) := by
    calc _ ≤ ENNReal.ofReal 1000000 * (volume (bigContainer r z0 w0)) ^ 2 := hpack
      _ ≤ ENNReal.ofReal 1000000 * (ENNReal.ofReal (10 ^ 23 * r ^ 2)) ^ 2 := by gcongr
      _ = ENNReal.ofReal (1000000 * (10 ^ 23 * r ^ 2) ^ 2) := by
        rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by norm_num)]
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have : (0 : ℝ) ≤ r ^ 4 := by positivity
        norm_num [bigBound]
        nlinarith
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle
  have hcard : (S.card : ℝ) ≤ bigBound :=
    (mul_le_mul_iff_left₀ (show 0 < r ^ 4 by positivity)).mp hreal
  exact_mod_cast hcard

/-- Two lines passing near both endpoints of one unit segment nearly coincide on
the relevant range. -/
theorem lines_close_of_common_segment {D : ℝ} (hD : D ≤ 1 / 100)
    {p0 v z w z' w' : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hw' : ‖w'‖ = 1)
    {a b a' b' : ℝ} (ha : |a| ≤ 7) (ha' : |a'| ≤ 7)
    (h0 : ‖p0 - (z + a • w)‖ < D) (h1 : ‖p0 + v - (z + b • w)‖ < D)
    (h0' : ‖p0 - (z' + a' • w')‖ < D) (h1' : ‖p0 + v - (z' + b' • w')‖ < D)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    ∃ σ : ℝ, |σ| ≤ 25 ∧ ‖(z' + u • w') - (z + σ • w)‖ ≤ 100 * D := by
  have hD0 : 0 < D := lt_of_le_of_lt (norm_nonneg _) h0
  have hvb : ‖v - (b - a) • w‖ < 2 * D := by
    have he : v - (b - a) • w = (p0 + v - (z + b • w)) - (p0 - (z + a • w)) := by module
    rw [he]; exact (norm_sub_le _ _).trans_lt (by linarith)
  have hvb' : ‖v - (b' - a') • w'‖ < 2 * D := by
    have he : v - (b' - a') • w' = (p0 + v - (z' + b' • w')) - (p0 - (z' + a' • w')) := by
      module
    rw [he]; exact (norm_sub_le _ _).trans_lt (by linarith)
  have hba : |b - a| ≤ 1 + 2 * D := by
    have h := norm_sub_norm_le ((b - a) • w) v
    rw [norm_smul, hw, mul_one, Real.norm_eq_abs, hv, norm_sub_rev] at h
    linarith
  have hba' : 1 - 2 * D ≤ |b' - a'| := by
    have h := norm_sub_norm_le v ((b' - a') • w')
    rw [norm_smul, hw', mul_one, Real.norm_eq_abs, hv] at h
    linarith
  have hpos : 0 < |b' - a'| := by linarith
  have hne : b' - a' ≠ 0 := abs_pos.mp hpos
  set c := (b - a) / (b' - a')
  have hc : |c| ≤ 2 := by
    rw [abs_div, div_le_iff₀ hpos]
    linarith
  have hcw : ‖w' - c • w‖ ≤ 5 * D := by
    have h : ‖(b' - a') • w' - (b - a) • w‖ < 4 * D := by
      have he : (b' - a') • w' - (b - a) • w = (v - (b - a) • w) - (v - (b' - a') • w') := by
        abel
      rw [he]; exact (norm_sub_le _ _).trans_lt (by linarith)
    have he : (b' - a') • w' - (b - a) • w = (b' - a') • (w' - c • w) := by
      rw [smul_sub, smul_smul]
      congr 2
      dsimp [c]
      field_simp
    rw [he, norm_smul, Real.norm_eq_abs] at h
    have h2 : |b' - a'| * ‖w' - c • w‖ ≤ |b' - a'| * (5 * D) := by
      have : 4 * D ≤ |b' - a'| * (5 * D) := by nlinarith
      linarith
    exact le_of_mul_le_mul_left h2 hpos
  refine ⟨a + (u - a') * c, ?_, ?_⟩
  · have hua : |u - a'| ≤ 8 := by
      rw [abs_le] at ha' ⊢; constructor <;> linarith [hu.1, hu.2]
    calc |a + (u - a') * c| ≤ |a| + |u - a'| * |c| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ 7 + 8 * 2 := by gcongr
      _ ≤ 25 := by norm_num
  · have he : (z' + u • w') - (z + (a + (u - a') * c) • w) =
        -(p0 - (z' + a' • w')) + (p0 - (z + a • w)) + (u - a') • (w' - c • w) := by module
    rw [he]
    have hua : |u - a'| ≤ 8 := by
      rw [abs_le] at ha' ⊢; constructor <;> linarith [hu.1, hu.2]
    calc ‖-(p0 - (z' + a' • w')) + (p0 - (z + a • w)) + (u - a') • (w' - c • w)‖ ≤
          ‖-(p0 - (z' + a' • w'))‖ + ‖p0 - (z + a • w)‖ + ‖(u - a') • (w' - c • w)‖ :=
          (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ D + D + 8 * (5 * D) := by
          rw [norm_neg, norm_smul, Real.norm_eq_abs]
          gcongr
      _ ≤ 100 * D := by linarith

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
