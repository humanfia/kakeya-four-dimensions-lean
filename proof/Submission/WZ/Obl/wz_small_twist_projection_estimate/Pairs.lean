-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_small_twist_projection_estimate.Pairs.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_small_twist_projection_estimate.Energy

/-!
# Pairs of tubes

For two tubes, `Zset` is the set of heights in `[-1, 1]` where the fixed coordinates `Xc c` of
their axes are within `κ`.  The difference of these coordinates is affine in the height with
slope `slX c v - slX c v'`, so `Zset` has length at most `2` and at most `2κ / |slope|`.  Both
grain fibres over `(u, z)` can only be nonempty when `z ∈ Zset c (27δ)`, and a tube whose
`Zset` with a fixed tube is nonempty and whose slope difference is at most `r` lies in a slab
of half-width `κ + 2r + 4δ`.
-/

namespace WangZahlLot.Obl.wz_small_twist_projection_estimate

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_grains_nonsingular_slices (ofTwist grainFib mem_grainFib ofTwist_zero
  ofTwist_one ofTwist_two)

/-- The slope of the fixed coordinate along the axis. -/
noncomputable def slX (c : ℝ) (v : Space) : ℝ := Xc c v / v 2

/-- The intercept of the fixed coordinate along the axis. -/
noncomputable def icX (c : ℝ) (x v : Space) : ℝ := Xc c x - x 2 * slX c v

lemma Xc_lineAt_eq (c : ℝ) (x v : Space) (z : ℝ) :
    Xc c (lineAt x v z) = icX c x v + slX c v * z := by
  rw [Xc_lineAt, icX, slX]

lemma abs_slX_le {c : ℝ} (hc : 100 < |c|) {v : Space} (hv : ‖v‖ = 1)
    (hv2 : (1 / 2 : ℝ) ≤ |v 2|) : |slX c v| ≤ 5 / 2 := by
  have h := abs_Xc_le hc v
  rw [hv, mul_one] at h
  have hv0 : 0 < |v 2| := by linarith
  rw [slX, abs_div, div_le_iff₀ hv0]
  linarith

/-- The heights where the fixed coordinates of two axes are within `κ`. -/
def Zset (c κ : ℝ) (x v x' v' : Space) : Set ℝ :=
  {z | z ∈ Icc (-1 : ℝ) 1 ∧ |Xc c (lineAt x v z) - Xc c (lineAt x' v' z)| ≤ κ}

lemma Zset_sub (c : ℝ) (x v x' v' : Space) (z : ℝ) :
    Xc c (lineAt x v z) - Xc c (lineAt x' v' z) =
      (icX c x v - icX c x' v') + (slX c v - slX c v') * z := by
  rw [Xc_lineAt_eq, Xc_lineAt_eq]
  ring

lemma volume_Zset_le_two (c κ : ℝ) (x v x' v' : Space) :
    volume (Zset c κ x v x' v') ≤ ENNReal.ofReal 2 := by
  calc volume (Zset c κ x v x' v') ≤ volume (Icc (-1 : ℝ) 1) := measure_mono fun z hz => hz.1
    _ = ENNReal.ofReal 2 := by rw [Real.volume_Icc]; norm_num

lemma volume_Zset_le_div {c κ : ℝ} {x v x' v' : Space} (hB : slX c v - slX c v' ≠ 0) :
    volume (Zset c κ x v x' v') ≤ ENNReal.ofReal (2 * κ / |slX c v - slX c v'|) := by
  set B := slX c v - slX c v' with hBdef
  have hB0 : 0 < |B| := abs_pos.mpr hB
  refine (Real.volume_le_diam _).trans (Metric.ediam_le fun z hz z' hz' => ?_)
  rw [edist_dist, Real.dist_eq]
  apply ENNReal.ofReal_le_ofReal
  have h1 := hz.2
  have h2 := hz'.2
  rw [Zset_sub] at h1 h2
  rw [le_div_iff₀ hB0]
  have heq : |z - z'| * |B| = |((icX c x v - icX c x' v') + B * z) -
      ((icX c x v - icX c x' v') + B * z')| := by
    rw [← abs_mul]
    congr 1
    ring
  rw [heq]
  exact (abs_sub _ _).trans (by linarith)

/-- Both grain fibres over `(u, z)` nonempty forces `z ∈ Zset c (27δ)`, the twisted
coordinate `u` being then within `3δ(|c|+3)` of the first axis. -/
lemma mem_Zset_of_grainFib {δ : ℝ} (hδ : 0 < δ) {f : ℝ → ℝ} (hf : SlopeN f)
    (hc : 100 < |f 0|) (hδc : 1 ≤ δ * (f 0) ^ 2)
    {x v x' v' : Space} (hv : ‖v‖ = 1) (hv2 : (1 / 2 : ℝ) ≤ |v 2|)
    (hT : tube δ x v ⊆ ball 0 1) (hv' : ‖v'‖ = 1) (hv2' : (1 / 2 : ℝ) ≤ |v' 2|)
    (hT' : tube δ x' v' ⊆ ball 0 1) {u z : ℝ}
    (hne : (grainFib f (tube δ x v) u z).Nonempty)
    (hne' : (grainFib f (tube δ x' v') u z).Nonempty) :
    z ∈ Zset (f 0) (27 * δ) x v x' v' ∧ |u - ctr f x v z| ≤ 3 * δ * (|f 0| + 3) := by
  set c := f 0 with hcdef
  have hz := abs_lt_one_of_grainFib hT hne
  have hfz : |f z - c| ≤ 2 := hf.sub_le hz.le
  have hM : |f z| ≤ |c| + 2 := by
    have := abs_add_le (f z - c) c
    rw [sub_add_cancel] at this
    linarith
  have h1 := abs_sub_ctr_le_of_grainFib hv hv2 hM hne
  have h2 := abs_sub_ctr_le_of_grainFib hv' hv2' hM hne'
  have hw : 3 * δ * (1 + (|c| + 2)) = 3 * δ * (|c| + 3) := by ring
  rw [hw] at h1 h2
  refine ⟨⟨abs_le.mp hz.le, ?_⟩, h1⟩
  -- the key algebra
  set L := lineAt x v z
  set L' := lineAt x' v' z
  have hL : ‖L‖ ≤ 5 := norm_lineAt_le hδ hv hv2 hT hz.le
  have hL' : ‖L'‖ ≤ 5 := norm_lineAt_le hδ hv' hv2' hT' hz.le
  have ha : |L 0 - L' 0| ≤ 10 := by
    have h := coord_abs_le (L - L') 0
    rw [PiLp.sub_apply] at h
    exact h.trans ((norm_sub_le _ _).trans (by linarith))
  have hD : |(L 0 - L' 0) + f z * (L 1 - L' 1)| ≤ 6 * δ * (|c| + 3) := by
    have heq : (L 0 - L' 0) + f z * (L 1 - L' 1) = (u - ctr f x' v' z) - (u - ctr f x v z) := by
      simp only [ctr, L, L']
      ring
    rw [heq]
    exact (abs_sub _ _).trans (by linarith)
  have hkey := key_algebra hc hδc hδ hfz ha hD
  have heq : Xc c L - Xc c L' = (L 0 - L' 0) / c + (L 1 - L' 1) := by
    simp only [Xc]
    ring
  rw [heq]
  exact hkey

/-- A tube whose `Zset` with a fixed tube is nonempty, with slope difference at most `r`, lies
in the slab around the fixed axis. -/
lemma tube_subset_slabW {δ κ r c : ℝ} (hδ : 0 < δ) (hc : 100 < |c|)
    {x v x' v' : Space} (hv' : ‖v'‖ = 1) (hv2' : (1 / 2 : ℝ) ≤ |v' 2|)
    (hT' : tube δ x' v' ⊆ ball 0 1) (hne : (Zset c κ x v x' v').Nonempty)
    (hr : |slX c v - slX c v'| ≤ r) :
    tube δ x' v' ⊆ slabW c (icX c x v) (slX c v) (κ + 2 * r + 4 * δ) := by
  intro p hp
  refine ⟨hT' hp, ?_⟩
  obtain ⟨z0, hz0, hz0κ⟩ := hne
  have hp1 : ‖p‖ < 1 := mem_ball_zero_iff.mp (hT' hp)
  have hz : |p 2| ≤ 1 := (coord_abs_le p 2).trans hp1.le
  have hz0' : |z0| ≤ 1 := abs_le.mpr hz0
  -- distance to the own axis
  have hnear := norm_sub_lineAt_lt hv' hv2' hp
  have h1 : |Xc c p - Xc c (lineAt x' v' (p 2))| ≤ 4 * δ := by
    rw [Xc_sub]
    have := abs_Xc_le hc (p - lineAt x' v' (p 2))
    nlinarith [norm_nonneg (p - lineAt x' v' (p 2))]
  -- the affine difference at `p 2`
  have h2 : |Xc c (lineAt x v (p 2)) - Xc c (lineAt x' v' (p 2))| ≤ κ + 2 * r := by
    rw [Zset_sub] at hz0κ ⊢
    have heq : (icX c x v - icX c x' v') + (slX c v - slX c v') * p 2 =
        ((icX c x v - icX c x' v') + (slX c v - slX c v') * z0) +
          (slX c v - slX c v') * (p 2 - z0) := by ring
    rw [heq]
    have h3 : |(slX c v - slX c v') * (p 2 - z0)| ≤ r * 2 := by
      rw [abs_mul]
      have h4 : |p 2 - z0| ≤ 2 := (abs_sub _ _).trans (by linarith)
      exact mul_le_mul hr h4 (abs_nonneg _) ((abs_nonneg _).trans hr)
    exact (abs_add_le _ _).trans (by linarith)
  have h5 : Xc c p - slX c v * p 2 - icX c x v =
      (Xc c p - Xc c (lineAt x' v' (p 2))) +
        (Xc c (lineAt x' v' (p 2)) - Xc c (lineAt x v (p 2))) := by
    rw [Xc_lineAt_eq c x v]
    ring
  show |Xc c p - slX c v * p 2 - icX c x v| ≤ κ + 2 * r + 4 * δ
  rw [h5]
  refine (abs_add_le _ _).trans ?_
  rw [abs_sub_comm (Xc c (lineAt x' v' (p 2)))]
  linarith

end WangZahlLot.Obl.wz_small_twist_projection_estimate
