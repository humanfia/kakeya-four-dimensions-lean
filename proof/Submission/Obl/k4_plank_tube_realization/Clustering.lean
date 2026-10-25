import Submission.Obl.k4_plank_tube_realization.CapPartition
import Submission.Lib.K4PlankGeometry

namespace Submission.Obl.k4_plank_tube_realization.ConvexGeometry

open Set MeasureTheory

noncomputable section

/-- The coordinate lift agrees with the shared tube construction. -/
theorem graphPoint_eq_shared (b u : Plane) (t : ℝ) :
    graphPoint t (b + t • u) = Submission.Lib.K4PlankGeometry.graphPoint b u t := by
  ext k
  fin_cases k <;> simp [graphPoint, Submission.Lib.K4PlankGeometry.graphPoint] <;> ring

theorem graphPoint_dist (t : ℝ) (z w : Plane) :
    dist (graphPoint t z) (graphPoint t w) = ‖z - w‖ / 10 := by
  have hs : dist (graphPoint t z) (graphPoint t w) ^ 2 = (‖z - w‖ / 10)^2 := by
    rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three,
      div_pow, plane_norm_sq]
    simp [graphPoint]
    ring
  nlinarith [dist_nonneg (x := graphPoint t z) (y := graphPoint t w), norm_nonneg (z - w)]

/-- The full-time plank cap becomes weighted convex clustering for the
contracted unit tubes. -/
theorem weighted_convex_clustering {D n : ℕ} (hD : 1 ≤ D)
    (b u : Fin n → Plane) (ω : Fin n → ℝ) {A : ℝ} (hA : 0 < A)
    (hbu : ∀ i, ‖b i‖ ≤ 1 ∧ ‖u i‖ ≤ 1)
    (hcap : ∀ (c w e₁ e₂ : Plane) (a β : ℝ),
      ‖e₁‖ = 1 → ‖e₂‖ = 1 → inner ℝ e₁ e₂ = 0 →
      1 ≤ a → a ≤ β → β ≤ (D : ℝ) → ∀ S : Finset (Fin n),
      (∀ i ∈ S, ∀ t ∈ Icc (0 : ℝ) 1,
        |inner ℝ (b i + t • u i - c - t • w) e₁| ≤ a / (D : ℝ) ∧
        |inner ℝ (b i + t • u i - c - t • w) e₂| ≤ β / (D : ℝ)) →
      ∑ i ∈ S, ω i ≤ A * a * β)
    (W : Set Space) (hW : Convex ℝ W) (S : Finset (Fin n))
    (hSW : ∀ i ∈ S, Metric.thickening (1 / (100 * (D : ℝ)))
      (segment ℝ (Submission.Lib.K4PlankGeometry.tubeBase (b i) (u i))
        (Submission.Lib.K4PlankGeometry.tubeBase (b i) (u i) +
          Submission.Lib.K4PlankGeometry.unitDirection (u i))) ⊆ W) :
    ENNReal.ofReal ((∑ i ∈ S, ω i) / (D : ℝ)^2) ≤
      ENNReal.ofReal (27000000000 * A) * volume W := by
  classical
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hδ : (0 : ℝ) < 1 / (100 * (D : ℝ)) := by positivity
  by_cases hne : S.Nonempty
  · obtain ⟨j, hj⟩ := hne
    let V : Set Space := W ∩ Metric.ball (0 : Space) 1
    have hVc : Convex ℝ V := hW.inter (convex_ball _ _)
    have hSV : ∀ i ∈ S, Metric.thickening (1 / (100 * (D : ℝ)))
        (segment ℝ (Submission.Lib.K4PlankGeometry.tubeBase (b i) (u i))
          (Submission.Lib.K4PlankGeometry.tubeBase (b i) (u i) +
            Submission.Lib.K4PlankGeometry.unitDirection (u i))) ⊆ V := by
      intro i hi y hy
      exact ⟨hSW i hi hy,
        Submission.Lib.K4PlankGeometry.unitTube_subset_ball hD (hbu i).1 (hbu i).2 hy⟩
    have hgraph : ∀ i ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, graphPoint t (b i + t • u i) ∈ V := by
      intro i hi t ht
      rw [graphPoint_eq_shared]
      exact hSV i hi (Metric.self_subset_thickening hδ _
        (Submission.Lib.K4PlankGeometry.graphPoint_mem_unitSegment (hbu i).2 ht))
    let r : ℝ := 1 / (20 * (D : ℝ))
    have hr : 0 < r := by dsimp only [r]; positivity
    have hpert : ∀ e : Plane, ‖e‖ = 1 → graphPoint 0 (b j + r • e) ∈ V := by
      intro e he
      apply hSV j hj
      apply Metric.mem_thickening_iff.mpr
      refine ⟨Submission.Lib.K4PlankGeometry.graphPoint (b j) (u j) 0,
        Submission.Lib.K4PlankGeometry.graphPoint_mem_unitSegment (hbu j).2
          (by constructor <;> norm_num), ?_⟩
      rw [← graphPoint_eq_shared]
      simp only [zero_smul, add_zero]
      rw [graphPoint_dist, add_sub_cancel_left, norm_smul, he, mul_one,
        Real.norm_eq_abs, abs_of_pos hr]
      dsimp only [r]
      have heq : 1 / (20 * (D : ℝ)) / 10 = 1 / (200 * (D : ℝ)) := by ring
      rw [heq]
      exact one_div_lt_one_div_of_lt (by positivity) (by nlinarith)
    obtain ⟨e₁, e₂, a, β, he₁, he₂, he12, hra, hab, hbhi, hrect, hvol⟩ :=
      exists_graph_rectangle hVc (fun _ hy => hy.2) (hbu j).1 (hbu j).2 hr
        (by simpa using hgraph j hj 0 (by constructor <;> norm_num))
        (by simpa using hgraph j hj 1 (by constructor <;> norm_num)) hpert
    have hapos : 0 < a := hr.trans_le hra
    have hbpos : 0 < β := hapos.trans_le hab
    have halower : 1 / (2 * (D : ℝ)) ≤ 10 * a := by
      have hh : 10 * r = 1 / (2 * (D : ℝ)) := by dsimp only [r]; ring
      rw [← hh]
      nlinarith
    have hweight := plank_bound_of_rectangle hD b u ω hA hbu hcap S (b j) (u j) e₁ e₂
      he₁ he₂ he12 halower (by nlinarith : 10 * a ≤ 10 * β) (by
        intro i hi t ht
        have hh := hrect (graphPoint t (b i + t • u i)) (hgraph i hi t ht)
        rw [oblique_graphPoint] at hh
        exact ⟨hh.1.trans (by nlinarith), hh.2.trans (by nlinarith)⟩)
    have hnormalized : (∑ i ∈ S, ω i) / (D : ℝ)^2 ≤ 250000 * A * (a * β) := by
      apply (div_le_iff₀ (sq_pos_of_pos hDpos)).mpr
      convert hweight using 1 <;> ring
    calc
      ENNReal.ofReal ((∑ i ∈ S, ω i) / (D : ℝ)^2) ≤
          ENNReal.ofReal (250000 * A) * ENNReal.ofReal (a * β) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal hnormalized
      _ ≤ ENNReal.ofReal (250000 * A) * (ENNReal.ofReal 108000 * volume V) := by gcongr
      _ = ENNReal.ofReal (27000000000 * A) * volume V := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring
      _ ≤ ENNReal.ofReal (27000000000 * A) * volume W := by
        have hVW : volume V ≤ volume W := measure_mono inter_subset_left
        exact mul_le_mul_of_nonneg_left hVW (by positivity)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty, zero_div, ENNReal.ofReal_zero]
    exact zero_le

end
end Submission.Obl.k4_plank_tube_realization.ConvexGeometry
