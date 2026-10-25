-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonconcentrated_dot_products.ScaleLines.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.PlaneCover
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Strips

namespace WangZahlLot.Obl.wz_nonconcentrated_dot_products

open Set Metric

/-- Orthogonal line concentration pulls back through separate expanding
similarities of the two factors, with explicit covering losses. -/
theorem LineConclusion.of_expanding_zooms {r ε ε' α β : ℝ} {F G : Set Plane}
    (b : Plane) (h : LineConclusion r ε' (zoom 0 α '' F) (zoom b β '' G))
    (hr : 0 < r) (hα : 1 ≤ α) (hβ : 1 ≤ β)
    (hNα : r ^ (ε - 1) ≤ r ^ (ε' - 1) / (9 * α ^ 2))
    (hNβ : r ^ (ε - 1) ≤ r ^ (ε' - 1) / (9 * β ^ 2)) :
    LineConclusion r ε F G := by
  obtain ⟨e, b₀, c, he, hF, hG⟩ := h
  have hαpos : 0 < α := zero_lt_one.trans_le hα
  have hβpos : 0 < β := zero_lt_one.trans_le hβ
  have hFS : Metric.thickening r {y : Plane | inner ℝ y e = c} ∩ (zoom 0 α '' F) ⊆
      zoom 0 α '' (Metric.thickening r {x : Plane | inner ℝ x e = c / α} ∩ F) := by
    rintro y ⟨hy, x, hx, rfl⟩
    refine ⟨x, ⟨?_, hx⟩, rfl⟩
    rw [thickening_hyperplane_eq_strip he] at hy ⊢
    change |inner ℝ (zoom 0 α x) e - c| < r at hy
    change |inner ℝ x e - c / α| < r
    have hid : inner ℝ (zoom 0 α x) e - c = α * (inner ℝ x e - c / α) := by
      simp only [zoom, sub_zero, real_inner_smul_left]
      field_simp
    rw [hid, abs_mul, abs_of_pos hαpos] at hy
    nlinarith [abs_nonneg (inner ℝ x e - c / α)]
  have hGS : Metric.thickening r (Set.range (fun t : ℝ => b₀ + t • e)) ∩
      (zoom b β '' G) ⊆ zoom b β ''
        (Metric.thickening r (Set.range (fun t : ℝ => (b + β⁻¹ • b₀) + t • e)) ∩ G) := by
    rintro y ⟨hy, x, hx, rfl⟩
    obtain ⟨z, ⟨t, rfl⟩, hdist⟩ := Metric.mem_thickening_iff.mp hy
    refine ⟨x, ⟨Metric.mem_thickening_iff.mpr ?_, hx⟩, rfl⟩
    refine ⟨b + β⁻¹ • (b₀ + t • e), ?_, ?_⟩
    · refine ⟨β⁻¹ * t, ?_⟩
      simp only [smul_add, smul_smul, add_assoc]
    · have hd := zoom_dist b hβpos.le x (b + β⁻¹ • (b₀ + t • e))
      rw [zoom_inverse b hβpos.ne'] at hd
      rw [hd] at hdist
      nlinarith [dist_nonneg (x := x) (y := b + β⁻¹ • (b₀ + t • e))]
  exact ⟨e, b + β⁻¹ • b₀, c / α, he,
    (hF.pullback_expanding_zoom 0 hr hα hFS).weaken hNα,
    (hG.pullback_expanding_zoom b hr hβ hGS).weaken hNβ⟩

end WangZahlLot.Obl.wz_nonconcentrated_dot_products
