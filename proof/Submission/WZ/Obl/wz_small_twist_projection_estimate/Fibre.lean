-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_small_twist_projection_estimate.Fibre.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_small_twist_projection_estimate.Algebra
import Submission.WZ.Obl.wz_small_twist_projection_estimate.Slab
import Submission.WZ.Obl.wz_grains_nonsingular_slices.ShearFubini

/-!
# Grain fibres of a tube

A horizontal grain `y ↦ (u - f z * y, y, z)` meets a transverse tube in a set of length at
most `6δ / |f z|`, and only when `u` is within `3δ(1 + |f z|)` of the twisted coordinate of
the axis point at height `z`.  Two tubes whose grain fibres over the same `(u, z)` are both
nonempty have nearby fixed coordinates `Xc c` at height `z` (`key_algebra`).
-/

namespace WangZahlLot.Obl.wz_small_twist_projection_estimate

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_grains_nonsingular_slices (ofTwist grainFib mem_grainFib ofTwist_zero
  ofTwist_one ofTwist_two)

/-- The twisted coordinate of the axis point at height `z`. -/
noncomputable def ctr (f : ℝ → ℝ) (x v : Space) (z : ℝ) : ℝ :=
  lineAt x v z 0 + f z * lineAt x v z 1

/-- The grain fibres of a transverse tube are short. -/
lemma volume_grainFib_tube_le {δ m : ℝ} {x v : Space} {f : ℝ → ℝ} (hv : ‖v‖ = 1)
    (hv2 : (1 / 2 : ℝ) ≤ |v 2|) {u z : ℝ} (hm : 0 < m) (hfz : m ≤ |f z|) :
    volume (grainFib f (tube δ x v) u z) ≤ ENNReal.ofReal (6 * δ / m) := by
  refine (Real.volume_le_diam _).trans (Metric.ediam_le fun y hy y' hy' => ?_)
  have h := norm_sub_lt_of_same_height hv hv2 hy hy' (by simp only [ofTwist_two])
  have h0 := coord_abs_le (ofTwist f u y z - ofTwist f u y' z) 0
  rw [PiLp.sub_apply, ofTwist_zero, ofTwist_zero] at h0
  have heq : |u - f z * y - (u - f z * y')| = |f z| * |y - y'| := by
    rw [show u - f z * y - (u - f z * y') = f z * (y' - y) by ring, abs_mul, abs_sub_comm y' y]
  rw [heq] at h0
  rw [edist_dist, Real.dist_eq]
  apply ENNReal.ofReal_le_ofReal
  rw [le_div_iff₀ hm]
  nlinarith [abs_nonneg (y - y')]

/-- A nonempty grain fibre of a tube inside the unit ball lies at a height in `(-1, 1)`. -/
lemma abs_lt_one_of_grainFib {δ : ℝ} {x v : Space} {f : ℝ → ℝ} {u z : ℝ}
    (hT : tube δ x v ⊆ ball 0 1) (hne : (grainFib f (tube δ x v) u z).Nonempty) :
    |z| < 1 := by
  obtain ⟨y, hy⟩ := hne
  have h1 := mem_ball_zero_iff.mp (hT hy)
  have h2 := coord_abs_le (ofTwist f u y z) 2
  rw [ofTwist_two] at h2
  linarith

/-- A nonempty grain fibre forces `u` to be near the axis. -/
lemma abs_sub_ctr_le_of_grainFib {δ M : ℝ} {x v : Space} {f : ℝ → ℝ} {u z : ℝ}
    (hv : ‖v‖ = 1) (hv2 : (1 / 2 : ℝ) ≤ |v 2|) (hM : |f z| ≤ M)
    (hne : (grainFib f (tube δ x v) u z).Nonempty) :
    |u - ctr f x v z| ≤ 3 * δ * (1 + M) := by
  obtain ⟨y, hy⟩ := hne
  have h := twist_sub_lineAt_lt (f := f) (M := M) hv hv2 hy (by rw [ofTwist_two]; exact hM)
  simp only [ofTwist_zero, ofTwist_one, ofTwist_two] at h
  have heq : u - f z * y + f z * y = u := by ring
  rw [heq] at h
  exact h

/-- The fixed coordinate of the axis point at height `z` is affine in `z`. -/
lemma Xc_lineAt (c : ℝ) {x v : Space} (z : ℝ) :
    Xc c (lineAt x v z) = (Xc c x - x 2 * (Xc c v / v 2)) + (Xc c v / v 2) * z := by
  simp only [lineAt, Xc_add, Xc_smul]
  ring

end WangZahlLot.Obl.wz_small_twist_projection_estimate
