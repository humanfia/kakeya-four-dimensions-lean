import Mathlib

/-!
# Contracted traces, unit tubes, and marked-bin shadings

Adapted from: here:o002

A bounded affine chart in the plane is contracted by 1/10 in three-dimensional
space. Its full traces fit in central unit segments. Balls of radius 1/(200 D)
at marked bin centres give disjoint shadings on each trace, with volume exactly
(pi/6000000) times the number of bins divided by D^3. The combined union volume
is at most (4 pi/3) times the number of distinct visited cells divided by D^3.

Developed here for obligation o002 and its geometric-realization child.
-/

namespace Submission.Lib.K4PlankGeometry

open MeasureTheory Metric

noncomputable section

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- The fixed contraction leaves room for a unit segment around each trace. -/
def graphPoint (b u : Plane) (t : ℝ) : Space :=
  (1 / 10 : ℝ) • WithLp.toLp 2 ![t, (b + t • u) 0, (b + t • u) 1]

def binTime (D : ℕ) (j : Fin D) : ℝ :=
  (((j : ℕ) : ℝ) + 1 / 2) / (D : ℝ)

def markPoint (D : ℕ) (b u : Plane) (j : Fin D) : Space :=
  graphPoint b u (binTime D j)

def cellCode (D : ℕ) (b u : Plane) (j : Fin D) : ℕ × (Fin 2 → ℤ) :=
  ((j : ℕ), fun k => ⌊(D : ℝ) * (b + binTime D j • u) k⌋)

def cellCenter (D : ℕ) (p : ℕ × (Fin 2 → ℤ)) : Space :=
  (1 / 10 : ℝ) • WithLp.toLp 2
    ![((p.1 : ℝ) + 1 / 2) / (D : ℝ),
      ((p.2 0 : ℝ) + 1 / 2) / (D : ℝ),
      ((p.2 1 : ℝ) + 1 / 2) / (D : ℝ)]

def markedShading (D : ℕ) (b u : Plane) (J : Finset (Fin D)) : Set Space :=
  ⋃ j ∈ J, ball (markPoint D b u j) (1 / (200 * (D : ℝ)))

def visitedCells {D n : ℕ} (b u : Fin n → Plane) (J : Fin n → Finset (Fin D)) :
    Finset (ℕ × (Fin 2 → ℤ)) :=
  ((Finset.univ : Finset (Fin n)).sigma J).image
    (fun p => cellCode D (b p.1) (u p.1) p.2)

theorem binTime_gap {D : ℕ} (hD : 1 ≤ D) {j k : Fin D} (hjk : j ≠ k) :
    1 / (D : ℝ) ≤ |binTime D j - binTime D k| := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  suffices hh : ∀ a b : Fin D, a < b → 1 / (D : ℝ) ≤ binTime D b - binTime D a by
    rcases lt_or_gt_of_ne hjk with h | h
    · exact (hh j k h).trans (le_abs_self _ |>.trans_eq (abs_sub_comm _ _))
    · exact (hh k j h).trans (le_abs_self _)
  intro a b hab
  have hc : (a : ℕ) + 1 ≤ (b : ℕ) := by exact Nat.succ_le_of_lt hab
  have hc' : ((a : ℕ) : ℝ) + 1 ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hc
  dsimp only [binTime]
  rw [← sub_div, div_le_div_iff_of_pos_right hDpos]
  linarith

theorem markPoint_gap {D : ℕ} (hD : 1 ≤ D) (b u : Plane)
    {j k : Fin D} (hjk : j ≠ k) :
    1 / (10 * (D : ℝ)) ≤ dist (markPoint D b u j) (markPoint D b u k) := by
  have h := PiLp.norm_apply_le (markPoint D b u j - markPoint D b u k) (0 : Fin 3)
  have hcoord : (1 / 10 : ℝ) * |binTime D j - binTime D k| ≤
      dist (markPoint D b u j) (markPoint D b u k) := by
    simpa only [dist_eq_norm, markPoint, graphPoint, PiLp.sub_apply, PiLp.smul_apply,
      PiLp.toLp_apply, Matrix.cons_val_zero, smul_eq_mul, Real.norm_eq_abs,
      ← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 10)] using h
  calc
    _ = (1 / 10 : ℝ) * (1 / (D : ℝ)) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left (binTime_gap hD hjk) (by norm_num)).trans hcoord

theorem markedShading_measurable (D : ℕ) (b u : Plane) (J : Finset (Fin D)) :
    MeasurableSet (markedShading D b u J) := by
  exact MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun _ => measurableSet_ball

theorem markedShading_volume {D : ℕ} (hD : 1 ≤ D) (b u : Plane)
    (J : Finset (Fin D)) :
    volume (markedShading D b u J) = (J.card : ENNReal) *
      (ENNReal.ofReal (1 / (200 * (D : ℝ))) ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3)) := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  rw [markedShading, measure_biUnion_finset]
  · simp only [EuclideanSpace.volume_ball_fin_three, Finset.sum_const, nsmul_eq_mul]
  · intro j hj k hk hjk
    apply ball_disjoint_ball
    apply le_trans _ (markPoint_gap hD b u hjk)
    have : (0 : ℝ) ≤ 1 / (D : ℝ) := by positivity
    field_simp
    linarith
  · exact fun _ _ => measurableSet_ball

private theorem floor_center_bound {D : ℝ} (hD : 0 < D) (z : ℝ) :
    |z - ((⌊D * z⌋ : ℝ) + 1 / 2) / D| ≤ 1 / D := by
  have hlo := Int.floor_le (D * z)
  have hhi := Int.lt_floor_add_one (D * z)
  have heq : z - ((⌊D * z⌋ : ℝ) + 1 / 2) / D =
      (D * z - ((⌊D * z⌋ : ℝ) + 1 / 2)) / D := by field_simp
  rw [heq, abs_div, abs_of_pos hD, div_le_div_iff_of_pos_right hD, abs_le]
  constructor <;> linarith

theorem markPoint_cellCenter_dist {D : ℕ} (hD : 1 ≤ D) (b u : Plane) (j : Fin D) :
    dist (markPoint D b u j) (cellCenter D (cellCode D b u j)) ≤ 1 / (2 * (D : ℝ)) := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  let z := b + binTime D j • u
  have h0 := floor_center_bound hDpos (z 0)
  have h1 := floor_center_bound hDpos (z 1)
  have hs0 : (z 0 - ((⌊(D : ℝ) * z 0⌋ : ℝ) + 1 / 2) / (D : ℝ)) ^ 2 ≤
      (1 / (D : ℝ)) ^ 2 := by
    have hh := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr h0
    simpa only [sq_abs] using hh
  have hs1 : (z 1 - ((⌊(D : ℝ) * z 1⌋ : ℝ) + 1 / 2) / (D : ℝ)) ^ 2 ≤
      (1 / (D : ℝ)) ^ 2 := by
    have hh := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr h1
    simpa only [sq_abs] using hh
  have hs : ‖markPoint D b u j - cellCenter D (cellCode D b u j)‖ ^ 2 =
      (1 / 100 : ℝ) *
        ((z 0 - ((⌊(D : ℝ) * z 0⌋ : ℝ) + 1 / 2) / (D : ℝ)) ^ 2 +
         (z 1 - ((⌊(D : ℝ) * z 1⌋ : ℝ) + 1 / 2) / (D : ℝ)) ^ 2) := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    simp [markPoint, graphPoint, cellCenter, cellCode, binTime, z, PiLp.sub_apply,
      PiLp.smul_apply]
    ring
  rw [dist_eq_norm]
  have heq : 1 / (2 * (D : ℝ)) = (1 / 2 : ℝ) * (1 / (D : ℝ)) := by ring
  rw [heq]
  have hp : 0 ≤ 1 / (D : ℝ) := by positivity
  nlinarith [norm_nonneg (markPoint D b u j - cellCenter D (cellCode D b u j))]

theorem markedBall_subset_cellBall {D : ℕ} (hD : 1 ≤ D) (b u : Plane) (j : Fin D) :
    ball (markPoint D b u j) (1 / (200 * (D : ℝ))) ⊆
      ball (cellCenter D (cellCode D b u j)) (1 / (D : ℝ)) := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  intro p hp
  rw [mem_ball] at hp ⊢
  have hd := dist_triangle p (markPoint D b u j) (cellCenter D (cellCode D b u j))
  have hc := markPoint_cellCenter_dist hD b u j
  have hr : 1 / (200 * (D : ℝ)) + 1 / (2 * (D : ℝ)) ≤ 1 / (D : ℝ) := by
    field_simp
    linarith
  linarith

/-- Balls are charged to the distinct visited cells, so repeated incidences
do not increase this union-volume upper bound. -/
theorem markedShading_union_volume {D n : ℕ} (hD : 1 ≤ D)
    (b u : Fin n → Plane) (J : Fin n → Finset (Fin D)) :
    volume (⋃ i, markedShading D (b i) (u i) (J i)) ≤
      ((visitedCells b u J).card : ENNReal) *
        (ENNReal.ofReal (1 / (D : ℝ)) ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3)) := by
  classical
  have hsub : (⋃ i, markedShading D (b i) (u i) (J i)) ⊆
      ⋃ q ∈ visitedCells b u J, ball (cellCenter D q) (1 / (D : ℝ)) := by
    intro p hp
    simp only [markedShading, Set.mem_iUnion] at hp
    rcases hp with ⟨i, j, hj, hp⟩
    have hq : cellCode D (b i) (u i) j ∈ visitedCells b u J := by
      apply Finset.mem_image.mpr
      refine ⟨⟨i, j⟩, ?_, rfl⟩
      exact Finset.mem_sigma.mpr ⟨Finset.mem_univ i, hj⟩
    simp only [Set.mem_iUnion]
    exact ⟨cellCode D (b i) (u i) j, hq, markedBall_subset_cellBall hD (b i) (u i) j hp⟩
  calc
    _ ≤ volume (⋃ q ∈ visitedCells b u J, ball (cellCenter D q) (1 / (D : ℝ))) :=
      measure_mono hsub
    _ ≤ ∑ q ∈ visitedCells b u J, volume (ball (cellCenter D q) (1 / (D : ℝ))) :=
      measure_biUnion_finset_le _ _
    _ = _ := by
      simp only [EuclideanSpace.volume_ball_fin_three, Finset.sum_const, nsmul_eq_mul]

theorem markedShading_volume_eq {D : ℕ} (hD : 1 ≤ D) (b u : Plane)
    (J : Finset (Fin D)) :
    volume (markedShading D b u J) =
      ENNReal.ofReal ((Real.pi / 6000000) * (J.card : ℝ) / (D : ℝ) ^ 3) := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  rw [markedShading_volume hD]
  rw [← ENNReal.ofReal_natCast J.card, ← ENNReal.ofReal_pow (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  congr 1
  field_simp
  ring

theorem markedShading_union_volume_le {D n : ℕ} (hD : 1 ≤ D)
    (b u : Fin n → Plane) (J : Fin n → Finset (Fin D)) :
    volume (⋃ i, markedShading D (b i) (u i) (J i)) ≤
      ENNReal.ofReal ((Real.pi * 4 / 3) * ((visitedCells b u J).card : ℝ) /
        (D : ℝ) ^ 3) := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  apply le_trans (markedShading_union_volume hD b u J)
  apply le_of_eq
  rw [← ENNReal.ofReal_natCast (visitedCells b u J).card,
    ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  congr 1
  field_simp

def rawDirection (u : Plane) : Space := WithLp.toLp 2 ![1, u 0, u 1]

theorem rawDirection_ne_zero (u : Plane) : rawDirection u ≠ 0 := by
  intro h
  have hh := congrArg (fun z : Space => z 0) h
  norm_num [rawDirection] at hh

theorem rawDirection_norm_sq (u : Plane) : ‖rawDirection u‖ ^ 2 = 1 + ‖u‖ ^ 2 := by
  simp [rawDirection, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, Fin.sum_univ_two]
  ring

theorem rawDirection_norm_le {u : Plane} (hu : ‖u‖ ≤ 1) : ‖rawDirection u‖ ≤ 2 := by
  have hs := rawDirection_norm_sq u
  nlinarith [norm_nonneg u, norm_nonneg (rawDirection u)]

def unitDirection (u : Plane) : Space := ‖rawDirection u‖⁻¹ • rawDirection u

theorem unitDirection_norm (u : Plane) : ‖unitDirection u‖ = 1 :=
  norm_smul_inv_norm (rawDirection_ne_zero u)

theorem rawDirection_eq (u : Plane) : ‖rawDirection u‖ • unitDirection u = rawDirection u := by
  unfold unitDirection
  rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr (rawDirection_ne_zero u)), one_smul]

def tubeBase (b u : Plane) : Space := graphPoint b u (1 / 2) - (1 / 2 : ℝ) • unitDirection u

theorem graphPoint_eq_midpoint (b u : Plane) (t : ℝ) :
    graphPoint b u t = graphPoint b u (1 / 2) + ((t - 1 / 2) / 10) • rawDirection u := by
  ext k
  fin_cases k <;>
    simp [graphPoint, rawDirection, PiLp.add_apply, PiLp.smul_apply] <;> ring

theorem graphPoint_mem_unitSegment {b u : Plane} (hu : ‖u‖ ≤ 1)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    graphPoint b u t ∈ segment ℝ (tubeBase b u) (tubeBase b u + unitDirection u) := by
  let θ := 1 / 2 + ((t - 1 / 2) / 10) * ‖rawDirection u‖
  have hnorm := rawDirection_norm_le hu
  have hn0 := norm_nonneg (rawDirection u)
  have ht0 := mul_nonneg ht.1 hn0
  have ht1 := mul_nonneg (sub_nonneg.mpr ht.2) hn0
  rw [segment_eq_image' ℝ]
  refine ⟨θ, ⟨?_, ?_⟩, ?_⟩
  · dsimp only [θ]
    nlinarith
  · dsimp only [θ]
    nlinarith
  · rw [add_sub_cancel_left, graphPoint_eq_midpoint b u t, ← rawDirection_eq u]
    dsimp only [tubeBase, θ]
    module

theorem graphPoint_norm_sq (b u : Plane) (t : ℝ) :
    ‖graphPoint b u t‖ ^ 2 = (1 / 100 : ℝ) * (t ^ 2 + ‖b + t • u‖ ^ 2) := by
  simp [graphPoint, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, Fin.sum_univ_two]
  ring

theorem graphPoint_midpoint_norm {b u : Plane} (hb : ‖b‖ ≤ 1) (hu : ‖u‖ ≤ 1) :
    ‖graphPoint b u (1 / 2)‖ ≤ 1 / 5 := by
  have hz : ‖b + (1 / 2 : ℝ) • u‖ ≤ 3 / 2 := by
    have hh := norm_add_le b ((1 / 2 : ℝ) • u)
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hh
    linarith
  have hs := graphPoint_norm_sq b u (1 / 2)
  nlinarith [norm_nonneg (b + (1 / 2 : ℝ) • u), norm_nonneg (graphPoint b u (1 / 2))]

/-- The normalized tubes have unit length and are contained in the unit ball. -/
theorem unitTube_subset_ball {D : ℕ} (hD : 1 ≤ D) {b u : Plane}
    (hb : ‖b‖ ≤ 1) (hu : ‖u‖ ≤ 1) :
    thickening (1 / (100 * (D : ℝ)))
      (segment ℝ (tubeBase b u) (tubeBase b u + unitDirection u)) ⊆ ball (0 : Space) 1 := by
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hc := graphPoint_midpoint_norm hb hu
  have hhalf : ‖(1 / 2 : ℝ) • unitDirection u‖ = 1 / 2 := by
    rw [norm_smul, unitDirection_norm, mul_one, Real.norm_of_nonneg (by norm_num)]
  have hleft : ‖tubeBase b u‖ ≤ 7 / 10 := by
    have hh := norm_sub_le (graphPoint b u (1 / 2)) ((1 / 2 : ℝ) • unitDirection u)
    rw [hhalf] at hh
    exact hh.trans (by linarith)
  have heq : tubeBase b u + unitDirection u =
      graphPoint b u (1 / 2) + (1 / 2 : ℝ) • unitDirection u := by
    dsimp only [tubeBase]
    module
  have hright : ‖tubeBase b u + unitDirection u‖ ≤ 7 / 10 := by
    rw [heq]
    have hh := norm_add_le (graphPoint b u (1 / 2)) ((1 / 2 : ℝ) • unitDirection u)
    rw [hhalf] at hh
    exact hh.trans (by linarith)
  have hseg : segment ℝ (tubeBase b u) (tubeBase b u + unitDirection u) ⊆
      ball (0 : Space) (4 / 5) := by
    apply (convex_ball (0 : Space) (4 / 5)).segment_subset
    · rw [mem_ball_zero_iff]
      linarith
    · rw [mem_ball_zero_iff]
      linarith
  apply (thickening_subset_of_subset _ hseg).trans
  apply (thickening_ball (0 : Space) (1 / (100 * (D : ℝ))) (4 / 5)).trans
  apply ball_subset_ball
  have hh : 1 / (100 * (D : ℝ)) ≤ 1 / 100 := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  linarith

theorem binTime_mem_Icc {D : ℕ} (hD : 1 ≤ D) (j : Fin D) :
    binTime D j ∈ Set.Icc (0 : ℝ) 1 := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hj : (j : ℕ) + 1 ≤ D := Nat.succ_le_of_lt j.isLt
  have hj' : ((j : ℕ) : ℝ) + 1 ≤ (D : ℝ) := by exact_mod_cast hj
  constructor
  · dsimp only [binTime]
    positivity
  · dsimp only [binTime]
    rw [div_le_one hDpos]
    linarith

theorem markedShading_subset_tube {D : ℕ} (hD : 1 ≤ D) {b u : Plane}
    (hu : ‖u‖ ≤ 1) (J : Finset (Fin D)) :
    markedShading D b u J ⊆ thickening (1 / (100 * (D : ℝ)))
      (segment ℝ (tubeBase b u) (tubeBase b u + unitDirection u)) := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  apply Set.iUnion_subset
  intro j
  apply Set.iUnion_subset
  intro hj
  have hr : 1 / (200 * (D : ℝ)) ≤ 1 / (100 * (D : ℝ)) := by
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  exact (ball_subset_ball hr).trans
    (ball_subset_thickening (graphPoint_mem_unitSegment hu (binTime_mem_Icc hD j)) _)

end

end Submission.Lib.K4PlankGeometry
