-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.TubeChart.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o157/x0672 WangZahlLot/Obl/wz_furstenberg_bush_line_count/High/TubeChart.lean (c552951).
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.GraphData.ColumnCodes
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.TubeCoordinates.CoarseChart

/-!
# The chart of a coarse tube

For a coarse tube given by a label `T` (unit normal `T.2`, `‖T.1‖ ≤ 4`) we use the frame
`v = -perp T.2`, so that `perp v = T.2` and the central line of the tube has chart slope `0`.
A line `j` within offset `A` and angle `θ ≤ 1/2` of `T` (up to the sign of the normal) is then

* transverse: `1/2 ≤ |⟨j.2, perp v⟩|`;
* of small slope: `|(lineChart v j).1| ≤ 8 θ`;
* of small height in tube coordinates: for `|y| ≤ 4`,
  `|lineHeight (tubeLine v cT aT λ j) y| ≤ (2 A + 64 θ) / λ`, where `(cT, aT) = lineChart v T`.

These are the chart hypotheses of x0665's `coarse_tube_rounded_false` (ported in `O214`).
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.TubeCoordinates
open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData
open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

/-- The axis of the tube of the label `T`. -/
noncomputable def tubeAxis (T : Plane × Plane) : Plane := -perp T.2

theorem tubeAxis_norm {T : Plane × Plane} (hT : ‖T.2‖ = 1) : ‖tubeAxis T‖ = 1 := by
  rw [tubeAxis, norm_neg, perp_norm, hT]

theorem perp_tubeAxis (T : Plane × Plane) : perp (tubeAxis T) = T.2 := by
  have h : perp (-perp T.2) = -perp (perp T.2) := by
    ext i; fin_cases i <;> simp [perp]
  rw [tubeAxis, h, perp_perp, neg_neg]

theorem cotNormal_tubeAxis_self (T : Plane × Plane) :
    cotNormal (tubeAxis T) T.2 = 0 := by
  have h0 : inner ℝ T.2 (tubeAxis T) = 0 := by
    rw [tubeAxis, inner_neg_right, perp_inner, neg_zero]
  rw [cotNormal, h0, neg_zero, zero_div]

/-- A unit vector within `θ ≤ 1/2` of `T.2` or of `-T.2` is transverse to the axis. -/
theorem transverse_of_close {T : Plane × Plane} {e : Plane} {θ : ℝ} (hT : ‖T.2‖ = 1)
    (hθ : θ ≤ 1 / 2) (hd : dist e T.2 ≤ θ ∨ dist e (-T.2) ≤ θ) :
    1 / 2 ≤ |inner ℝ e (perp (tubeAxis T))| := by
  rw [perp_tubeAxis]
  have hself : inner ℝ T.2 T.2 = 1 := by
    rw [real_inner_self_eq_norm_sq, hT]; norm_num
  rcases hd with hd | hd
  · have hh := abs_real_inner_le_norm (e - T.2) T.2
    rw [hT, mul_one, inner_sub_left, hself, ← dist_eq_norm] at hh
    have := (abs_le.mp (hh.trans hd)).1
    rw [abs_of_pos (by linarith)]
    linarith
  · have hh := abs_real_inner_le_norm (e - -T.2) T.2
    rw [hT, mul_one, inner_sub_left, inner_neg_left, hself, ← dist_eq_norm] at hh
    have := (abs_le.mp (hh.trans hd)).2
    rw [abs_of_neg (by linarith)]
    linarith

/-- **Chart of a line near the tube.** -/
theorem near_tube_chart {T j : Plane × Plane} {A θ lam : ℝ} (hT : ‖T.2‖ = 1)
    (hT4 : ‖T.1‖ ≤ 4) (hj : ‖j.2‖ = 1) (hθ : θ ≤ 1 / 2) (hlam : 0 < lam)
    (hoff : |inner ℝ (j.1 - T.1) j.2| ≤ A)
    (hang : dist j.2 T.2 ≤ θ ∨ dist j.2 (-T.2) ≤ θ) :
    1 / 2 ≤ |inner ℝ j.2 (perp (tubeAxis T))| ∧
      |(lineChart (tubeAxis T) j).1| ≤ 8 * θ ∧
      ∀ y : ℝ, |y| ≤ 4 →
        |lineHeight (tubeLine (tubeAxis T) (lineChart (tubeAxis T) T).1
          (lineChart (tubeAxis T) T).2 lam j) y| ≤ (2 * A + 64 * θ) / lam := by
  set v := tubeAxis T with hv
  have hv1 : ‖v‖ = 1 := tubeAxis_norm hT
  have hw := transverse_of_close hT hθ hang
  have hwT : 1 / 2 ≤ |inner ℝ T.2 (perp v)| :=
    transverse_of_close hT (le_refl (1 / 2 : ℝ)) (Or.inl (by rw [dist_self]; norm_num))
  -- flip the normal of `j` if it is close to `-T.2`
  obtain ⟨e, he, hej, hdist, hoffe, hwe⟩ : ∃ e : Plane, ‖e‖ = 1 ∧
      lineChart v (j.1, e) = lineChart v j ∧ dist e T.2 ≤ θ ∧
      |inner ℝ (j.1 - T.1) e| ≤ A ∧ 1 / 2 ≤ |inner ℝ e (perp v)| := by
    rcases hang with h1 | h1
    · exact ⟨j.2, hj, rfl, h1, hoff, hw⟩
    · refine ⟨-j.2, by rw [norm_neg, hj], ?_, ?_, ?_, ?_⟩
      · rw [lineChart_neg_normal]
      · have : dist (-j.2) T.2 = dist j.2 (-T.2) := by
          rw [dist_eq_norm, dist_eq_norm, ← norm_neg]; congr 1; abel
        rw [this]; exact h1
      · rw [inner_neg_right, abs_neg]; exact hoff
      · rw [inner_neg_left, abs_neg]; exact hw
  have hcT : (lineChart v T).1 = 0 := by
    simp only [lineChart]
    exact cotNormal_tubeAxis_self T
  -- the slope
  have hslope : |(lineChart v j).1| ≤ 8 * θ := by
    have h1 := cotNormal_dist_bound hv1 hT hwe hwT
    rw [← hej]
    simp only [lineChart] at hcT ⊢
    rw [hcT, sub_zero] at h1
    exact h1.trans (by linarith)
  refine ⟨hw, hslope, ?_⟩
  intro y hy
  have hT' : T = (T.1, T.2) := rfl
  have hd := lineChart_dist_bound (p := j.1) (e := e) (p' := T.1) (e' := T.2) hv1 hT hT4 hwe hwT
  rw [hej, ← hT'] at hd
  have hb : dist (lineChart v j) (lineChart v T) ≤ 2 * A + 32 * θ := by linarith
  rw [Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq] at hb
  rw [lineHeight_tubeLine v hlam.ne', abs_div, abs_of_pos hlam]
  apply div_le_div_of_nonneg_right _ hlam.le
  simp only [height]
  rw [hcT]
  have hc : |(lineChart v j).1 * y| ≤ 8 * θ * 4 := by
    rw [abs_mul]
    exact mul_le_mul hslope hy (abs_nonneg _) (by linarith [abs_nonneg ((lineChart v j).1)])
  have hsplit : (lineChart v j).1 * y + (lineChart v j).2 - ((lineChart v T).2 + 0 * y) =
      (lineChart v j).1 * y + ((lineChart v j).2 - (lineChart v T).2) := by ring
  rw [hsplit]
  calc |(lineChart v j).1 * y + ((lineChart v j).2 - (lineChart v T).2)| ≤
      |(lineChart v j).1 * y| + |(lineChart v j).2 - (lineChart v T).2| := abs_add_le _ _
    _ ≤ 8 * θ * 4 + (2 * A + 32 * θ) := add_le_add hc hb.2
    _ = 2 * A + 64 * θ := by ring

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
