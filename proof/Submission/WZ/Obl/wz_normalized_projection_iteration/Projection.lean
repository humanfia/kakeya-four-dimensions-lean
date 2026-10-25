-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_iteration.Projection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_iteration.Basic

namespace WangZahlLot.Obl.wz_normalized_projection_iteration

open Set Metric MeasureTheory

/-- The point map underlying the projection. -/
def project (f : ℝ → ℝ) (p : Space) : ℝ × ℝ :=
  (p 0 + f (p 2) * p 1, p 2)

theorem slope_sub_le {f : ℝ → ℝ} (hf : Slope f) {s t : ℝ}
    (hs : s ∈ Icc (-1) 1) (ht : t ∈ Icc (-1) 1) :
    |f s - f t| ≤ 2 * |s - t| := by
  have hd : Differentiable ℝ f := hf.1.differentiable (by norm_num)
  simpa only [Real.norm_eq_abs] using (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (fun z _ => hd z) (fun z hz => by simpa only [Real.norm_eq_abs] using (hf.2 z hz).2.1) ht hs

theorem slope_abs_le {f : ℝ → ℝ} (hf : Slope f) (hf0 : |f 0| ≤ 1)
    {z : ℝ} (hz : z ∈ Icc (-1) 1) : |f z| ≤ 3 := by
  have h := slope_sub_le hf hz (show (0 : ℝ) ∈ Icc (-1) 1 by norm_num)
  have hz' : |z| ≤ 1 := abs_le.mpr hz
  have htri := abs_add_le (f z - f 0) (f 0)
  simp only [sub_add_cancel, sub_zero] at h htri
  linarith

theorem coordinate_abs_le (p : Space) (i : Fin 3) : |p i| ≤ ‖p‖ := by
  rw [← Real.norm_eq_abs]
  exact PiLp.norm_apply_le p i

theorem coordinate_dist_le (p q : Space) (i : Fin 3) : |p i - q i| ≤ dist p q := by
  simpa only [dist_eq_norm, PiLp.sub_apply] using coordinate_abs_le (p - q) i

theorem coordinate_mem_Icc {p : Space} (hp : p ∈ closedBall 0 1) (i : Fin 3) :
    p i ∈ Icc (-1) 1 := by
  rw [mem_closedBall, dist_zero_right] at hp
  exact abs_le.mp ((coordinate_abs_le p i).trans hp)

/-- The normalized projection is uniformly Lipschitz on the unit ball. -/
theorem project_dist_le {f : ℝ → ℝ} (hf : Slope f) (hf0 : |f 0| ≤ 1)
    {p q : Space} (hp : p ∈ closedBall 0 1) (hq : q ∈ closedBall 0 1) :
    dist (project f p) (project f q) ≤ 6 * dist p q := by
  have hp2 := coordinate_mem_Icc hp 2
  have hq2 := coordinate_mem_Icc hq 2
  have hfq := slope_abs_le hf hf0 hq2
  have hp1 : |p 1| ≤ 1 := abs_le.mpr (coordinate_mem_Icc hp 1)
  have hd0 := coordinate_dist_le p q 0
  have hd1 := coordinate_dist_le p q 1
  have hd2 := coordinate_dist_le p q 2
  have hdf := (slope_sub_le hf hp2 hq2).trans (mul_le_mul_of_nonneg_left hd2 (by norm_num))
  have hprod : |f (p 2) * p 1 - f (q 2) * q 1| ≤ 5 * dist p q := by
    calc
      |f (p 2) * p 1 - f (q 2) * q 1| =
          |(f (p 2) - f (q 2)) * p 1 + f (q 2) * (p 1 - q 1)| := by congr 1; ring
      _ ≤ |f (p 2) - f (q 2)| * |p 1| + |f (q 2)| * |p 1 - q 1| := by
        simpa only [abs_mul] using abs_add_le ((f (p 2) - f (q 2)) * p 1)
          (f (q 2) * (p 1 - q 1))
      _ ≤ (2 * dist p q) * 1 + 3 * dist p q := by
        exact add_le_add (mul_le_mul hdf hp1 (abs_nonneg _) (by positivity))
          (mul_le_mul hfq hd1 (abs_nonneg _) (by norm_num))
      _ = 5 * dist p q := by ring
  rw [Prod.dist_eq]
  apply max_le
  · change |p 0 + f (p 2) * p 1 - (q 0 + f (q 2) * q 1)| ≤ 6 * dist p q
    calc
      _ = |(p 0 - q 0) + (f (p 2) * p 1 - f (q 2) * q 1)| := by congr 1; ring
      _ ≤ |p 0 - q 0| + |f (p 2) * p 1 - f (q 2) * q 1| := abs_add_le _ _
      _ ≤ 6 * dist p q := by linarith
  · change |p 2 - q 2| ≤ 6 * dist p q
    linarith [dist_nonneg (x := p) (y := q)]

/-- Pointwise spatial proximity transfers to the prescribed planar thickening. -/
theorem projection_subset_thickening {f : ℝ → ℝ} (hf : Slope f) (hf0 : |f 0| ≤ 1)
    {E Z : Set Space} (hE : E ⊆ closedBall 0 1) (hZ : Z ⊆ closedBall 0 1)
    {r : ℝ} (hnear : ∀ p ∈ Z, ∃ q ∈ E, dist p q < r / 6) :
    Projection f Z ⊆ thickening r (Projection f E) := by
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨q, hq, hpq⟩ := hnear p hp
  apply mem_thickening_iff.mpr
  refine ⟨project f q, ⟨q, hq, rfl⟩, ?_⟩
  exact (project_dist_le hf hf0 (hZ hp) (hE hq)).trans_lt (by linarith)

/-- Every normalized projected shading in the unit ball lies in a fixed planar ball. -/
theorem projection_subset_ball {f : ℝ → ℝ} (hf : Slope f) (hf0 : |f 0| ≤ 1)
    {E : Set Space} (hE : E ⊆ closedBall 0 1) :
    Projection f E ⊆ closedBall (0 : ℝ × ℝ) 6 := by
  rintro _ ⟨p, hp, rfl⟩
  have h := project_dist_le hf hf0 (hE hp) (show (0 : Space) ∈ closedBall 0 1 by simp)
  have hp1 : dist p 0 ≤ 1 := hE hp
  have hzero : project f 0 = 0 := by simp [project]
  rw [hzero] at h
  change dist (project f p) 0 ≤ 6
  linarith

end WangZahlLot.Obl.wz_normalized_projection_iteration
