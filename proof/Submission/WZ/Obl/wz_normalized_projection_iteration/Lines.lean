-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_iteration.Lines.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_iteration.Projection

namespace WangZahlLot.Obl.wz_normalized_projection_iteration

open Set Metric

noncomputable def lineSlope (v : Space) : Space := (v 2)⁻¹ • v
noncomputable def lineBase (x v : Space) : Space := x - (x 2) • lineSlope v
noncomputable def linePoint (x v : Space) (z : ℝ) : Space := lineBase x v + z • lineSlope v

theorem lineSlope_cancel {v : Space} (hv : v 2 ≠ 0) : (v 2) • lineSlope v = v := by
  simp [lineSlope, smul_smul, hv]

theorem norm_lineSlope {v : Space} (hv : ‖v‖ = 1) (hv2 : (1 / 2 : ℝ) ≤ v 2) :
    ‖lineSlope v‖ ≤ 2 := by
  have hvp : 0 < v 2 := by linarith
  rw [lineSlope, norm_smul, hv, mul_one, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvp)]
  rw [← one_div, div_le_iff₀ hvp]
  linarith

theorem lineSlope_dist {v w : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hv2 : (1 / 2 : ℝ) ≤ v 2) (hw2 : (1 / 2 : ℝ) ≤ w 2) :
    ‖lineSlope v - lineSlope w‖ ≤ 6 * ‖v - w‖ := by
  have hvp : 0 < v 2 := by linarith
  have hwp : 0 < w 2 := by linarith
  have hwi := norm_lineSlope hw hw2
  have hvi : (v 2)⁻¹ ≤ 2 := by rw [← one_div, div_le_iff₀ hvp]; linarith
  have hcoord : |w 2 - v 2| ≤ ‖v - w‖ := by
    simpa only [dist_eq_norm, abs_sub_comm] using coordinate_dist_le v w 2
  have heq : lineSlope v - lineSlope w =
      (v 2)⁻¹ • ((v - w) + (w 2 - v 2) • lineSlope w) := by
    have hcan := lineSlope_cancel hwp.ne'
    have hinner : (v - w) + (w 2 - v 2) • lineSlope w = v - (v 2) • lineSlope w := by
      rw [sub_smul, hcan]
      abel
    rw [hinner, smul_sub, smul_smul, inv_mul_cancel₀ hvp.ne', one_smul]
    rfl
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvp)]
  have hinner : ‖(v - w) + (w 2 - v 2) • lineSlope w‖ ≤ 3 * ‖v - w‖ := by
    calc
      _ ≤ ‖v - w‖ + ‖(w 2 - v 2) • lineSlope w‖ := norm_add_le _ _
      _ = ‖v - w‖ + |w 2 - v 2| * ‖lineSlope w‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖v - w‖ + ‖v - w‖ * 2 :=
        add_le_add le_rfl (mul_le_mul hcoord hwi (norm_nonneg _) (norm_nonneg _))
      _ = 3 * ‖v - w‖ := by ring
  calc
    _ ≤ 2 * (3 * ‖v - w‖) :=
      mul_le_mul hvi hinner (norm_nonneg _) (by norm_num)
    _ = _ := by ring

theorem linePoint_at_segment {x v : Space} (hv2 : v 2 ≠ 0) (t : ℝ) :
    linePoint x v ((x + t • v) 2) = x + t • v := by
  simp only [linePoint, lineBase, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    add_smul, mul_smul, lineSlope_cancel hv2]
  abel

theorem linePoint_dist_same (x v : Space) (s t : ℝ) :
    dist (linePoint x v s) (linePoint x v t) = |s - t| * ‖lineSlope v‖ := by
  rw [linePoint, linePoint, dist_add_left, dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs]

theorem linePoint_near_tube {δ : ℝ} {x v p : Space} (hv : ‖v‖ = 1)
    (hv2 : (1 / 2 : ℝ) ≤ v 2) (hp : p ∈ Tube δ x v) :
    dist (linePoint x v (p 2)) p < 3 * δ := by
  have hvp : 0 < v 2 := by linarith
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  rw [segment_eq_image'] at hq
  obtain ⟨t, ht, rfl⟩ := hq
  simp only [add_sub_cancel_left] at hpq
  have hcoord := coordinate_dist_le p (x + t • v) 2
  have hsl := norm_lineSlope hv hv2
  have hdist : dist (linePoint x v (p 2)) (x + t • v) ≤ 2 * dist p (x + t • v) := by
    calc
      _ = dist (linePoint x v (p 2)) (linePoint x v ((x + t • v) 2)) := by
        rw [linePoint_at_segment hvp.ne' t]
      _ = |p 2 - (x + t • v) 2| * ‖lineSlope v‖ := linePoint_dist_same ..
      _ ≤ 2 * dist p (x + t • v) := by
        nlinarith [abs_nonneg (p 2 - (x + t • v) 2)]
  have htri := dist_triangle (linePoint x v (p 2)) (x + t • v) p
  rw [dist_comm (x + t • v) p] at htri
  linarith

theorem linePoint_dist_le {x y v w : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hv2 : (1 / 2 : ℝ) ≤ v 2) (hw2 : (1 / 2 : ℝ) ≤ w 2)
    {z : ℝ} (hz : |z| ≤ 1) :
    dist (linePoint x v z) (linePoint y w z) ≤
      ‖lineBase x v - lineBase y w‖ + 6 * ‖v - w‖ := by
  calc
    _ ≤ dist (lineBase x v) (lineBase y w) + dist (z • lineSlope v) (z • lineSlope w) :=
      dist_add_add_le ..
    _ = ‖lineBase x v - lineBase y w‖ + |z| * ‖lineSlope v - lineSlope w‖ := by
      rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs]
    _ ≤ _ := by
      have hm := mul_le_mul hz (lineSlope_dist hv hw hv2 hw2) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      nlinarith

/-- Moving the start point by `d` moves the line's horizontal intercept by at most `3d`. -/
theorem lineBase_dist_start {x y v : Space} (hv : ‖v‖ = 1)
    (hv2 : (1 / 2 : ℝ) ≤ v 2) :
    ‖lineBase x v - lineBase y v‖ ≤ 3 * ‖x - y‖ := by
  have heq : lineBase x v - lineBase y v =
      (x - y) - (x 2 - y 2) • lineSlope v := by unfold lineBase; module
  rw [heq]
  calc
    _ ≤ ‖x - y‖ + ‖(x 2 - y 2) • lineSlope v‖ := norm_sub_le _ _
    _ = ‖x - y‖ + |x 2 - y 2| * ‖lineSlope v‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖x - y‖ + ‖x - y‖ * 2 := by
      apply add_le_add le_rfl
      exact mul_le_mul (by simpa [dist_eq_norm] using coordinate_dist_le x y 2)
        (norm_lineSlope hv hv2) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by ring

/-- Intersecting tubes with nearby directions must also have nearby intercepts. -/
theorem lineBase_dist_of_inter {δ : ℝ} {x y v w p : Space}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hv2 : (1 / 2 : ℝ) ≤ v 2) (hw2 : (1 / 2 : ℝ) ≤ w 2)
    (hp : p ∈ Tube δ x v ∩ Tube δ y w) (hp1 : ‖p‖ ≤ 1) :
    ‖lineBase x v - lineBase y w‖ < 6 * δ + 6 * ‖v - w‖ := by
  have hxp := linePoint_near_tube hv hv2 hp.1
  have hyp := linePoint_near_tube hw hw2 hp.2
  have hz : |p 2| ≤ 1 := (coordinate_abs_le p 2).trans hp1
  have hsl := lineSlope_dist hv hw hv2 hw2
  have heq : lineBase x v - lineBase y w =
      ((linePoint x v (p 2) - p) - (linePoint y w (p 2) - p)) -
        (p 2) • (lineSlope v - lineSlope w) := by unfold linePoint; module
  calc
    _ ≤ ‖linePoint x v (p 2) - p‖ + ‖linePoint y w (p 2) - p‖ +
        |p 2| * ‖lineSlope v - lineSlope w‖ := by
      rw [heq]
      exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) (by rw [norm_smul, Real.norm_eq_abs]))
    _ < _ := by
      rw [← dist_eq_norm, ← dist_eq_norm]
      have hm := mul_le_mul hz hsl (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      linarith

/-- The line parametrization belongs to the unit segment precisely over its vertical interval. -/
theorem linePoint_mem_segment {x v : Space} (hv2 : 0 < v 2) {z : ℝ}
    (hz : z ∈ Icc (x 2) (x 2 + v 2)) :
    linePoint x v z ∈ segment ℝ x (x + v) := by
  let t : ℝ := (z - x 2) / v 2
  have ht : t ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hz.1) hv2.le
    · exact (div_le_one hv2).mpr (by linarith [hz.2])
  have htz : (x + t • v) 2 = z := by
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, t]
    field_simp
    ring
  rw [← htz, linePoint_at_segment hv2.ne']
  rw [segment_eq_image']
  exact ⟨t, ht, by simp⟩

/-- Two extremal segments cover an entire small cell of transverse lines. -/
theorem tube_subset_two_tubes {δ ε : ℝ} (hδ : 0 < δ)
    {x v a u b w : Space} (hv : ‖v‖ = 1) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (hv2 : (1 / 2 : ℝ) ≤ v 2) (hu2 : (1 / 2 : ℝ) ≤ u 2) (hw2 : (1 / 2 : ℝ) ≤ w 2)
    (hseg : segment ℝ x (x + v) ⊆ closedBall (0 : Space) 1)
    (hbasea : ‖lineBase x v - lineBase a u‖ ≤ ε) (hdira : ‖v - u‖ ≤ ε)
    (hbaseb : ‖lineBase x v - lineBase b w‖ ≤ ε) (hdirb : ‖v - w‖ ≤ ε)
    (hbottom : a 2 ≤ x 2) (htop : x 2 + v 2 ≤ b 2 + w 2)
    (hbridge : b 2 ≤ a 2 + u 2) :
    Tube δ x v ⊆ Tube (δ + 7 * ε) a u ∪ Tube (δ + 7 * ε) b w := by
  intro p hp
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  have hq2 : |q 2| ≤ 1 := abs_le.mpr (coordinate_mem_Icc (hseg hq) 2)
  have hqseg := hq
  rw [segment_eq_image'] at hq
  obtain ⟨t, ht, rfl⟩ := hq
  simp only [add_sub_cancel_left] at hpq hq2 hqseg ⊢
  have hqinterval : (x + t • v) 2 ∈ Icc (x 2) (x 2 + v 2) := by
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    constructor <;> nlinarith [ht.1, ht.2]
  have hqline := linePoint_at_segment (show v 2 ≠ 0 by linarith) (x := x) t
  by_cases hleft : (x + t • v) 2 ≤ a 2 + u 2
  · left
    have hmem := linePoint_mem_segment (show 0 < u 2 by linarith)
      ⟨hbottom.trans hqinterval.1, hleft⟩
    have hd := linePoint_dist_le (x := x) (y := a) hv hu hv2 hu2 hq2
    rw [hqline] at hd
    apply mem_thickening_iff.mpr
    refine ⟨linePoint a u ((x + t • v) 2), hmem, ?_⟩
    have htri := dist_triangle p (x + t • v) (linePoint a u ((x + t • v) 2))
    linarith
  · right
    have hmem := linePoint_mem_segment (show 0 < w 2 by linarith)
      ⟨hbridge.trans (le_of_not_ge hleft), hqinterval.2.trans htop⟩
    have hd := linePoint_dist_le (x := x) (y := b) hv hw hv2 hw2 hq2
    rw [hqline] at hd
    apply mem_thickening_iff.mpr
    refine ⟨linePoint b w ((x + t • v) 2), hmem, ?_⟩
    have htri := dist_triangle p (x + t • v) (linePoint b w ((x + t • v) 2))
    linarith

end WangZahlLot.Obl.wz_normalized_projection_iteration
