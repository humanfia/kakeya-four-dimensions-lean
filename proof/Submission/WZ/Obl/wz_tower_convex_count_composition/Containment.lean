-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_tower_convex_count_composition.Containment.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
namespace WangZahlLot.Obl.wz_tower_convex_count_composition

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya

/-- Equal unit lengths make one-sided tubular containment symmetric up to a
fixed enlargement. We record the endpoint estimate first. -/
theorem parent_endpoints {r : ℝ} {x v y w : Space}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (h0 : x ∈ thickening r (segment ℝ y (y + w)))
    (h1 : x + v ∈ thickening r (segment ℝ y (y + w))) :
    (dist y x < 3 * r ∧ dist (y + w) (x + v) < 3 * r) ∨
      (dist y (x + v) < 3 * r ∧ dist (y + w) x < 3 * r) := by
  obtain ⟨p, hp, hxp⟩ := mem_thickening_iff.mp h0
  obtain ⟨q, hq, hxq⟩ := mem_thickening_iff.mp h1
  rw [segment_eq_image'] at hp hq
  obtain ⟨a, ha, rfl⟩ := hp
  obtain ⟨b, hb, rfl⟩ := hq
  simp only [add_sub_cancel_left] at hxp hxq
  have hparam (s t : ℝ) : dist (y + s • w) (y + t • w) = |s - t| := by
    rw [dist_add_left, dist_eq_norm, ← sub_smul, norm_smul, hw, mul_one, Real.norm_eq_abs]
  have hab : 1 < |a - b| + 2 * r := by
    have ht1 := dist_triangle x (y + a • w) (x + v)
    have ht2 := dist_triangle (y + a • w) (y + b • w) (x + v)
    have he : dist x (x + v) = 1 := by simpa [dist_eq_norm] using hv
    rw [he] at ht1
    rw [hparam, dist_comm (y + b • w)] at ht2
    linarith
  have hleft (p : Space) (t : ℝ) (ht0 : 0 ≤ t) (ht : t < 2 * r)
      (hp : dist p (y + t • w) < r) : dist y p < 3 * r := by
    have he : dist y (y + t • w) = t := by
      simpa [abs_of_nonneg ht0] using hparam 0 t
    have htri := dist_triangle y (y + t • w) p
    rw [he, dist_comm (y + t • w)] at htri
    linarith
  have hright (p : Space) (t : ℝ) (ht1 : t ≤ 1) (ht : 1 - t < 2 * r)
      (hp : dist p (y + t • w) < r) : dist (y + w) p < 3 * r := by
    have he : dist (y + w) (y + t • w) = 1 - t := by
      simpa [abs_of_nonneg (sub_nonneg.mpr ht1)] using hparam 1 t
    have htri := dist_triangle (y + w) (y + t • w) p
    rw [he, dist_comm (y + t • w)] at htri
    linarith
  rcases le_total a b with hab' | hab'
  · rw [abs_of_nonpos (sub_nonpos.mpr hab')] at hab
    exact Or.inl ⟨hleft x a ha.1 (by linarith [hb.2]) hxp,
      hright (x + v) b hb.2 (by linarith [ha.1]) hxq⟩
  · rw [abs_of_nonneg (sub_nonneg.mpr hab')] at hab
    exact Or.inr ⟨hleft (x + v) b hb.1 (by linarith [ha.2]) hxq,
      hright x a ha.2 (by linarith [hb.1]) hxp⟩

/-- A parent tube assigned a child contained in a convex set lies in a fixed
thickening of that set. -/
theorem parent_subset_thickening {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    {x v y w : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    {W : Set Space} (hW : Convex ℝ W)
    (hchild : thickening s (segment ℝ x (x + v)) ⊆ W)
    (hparent : thickening s (segment ℝ x (x + v)) ⊆
      thickening r (segment ℝ y (y + w))) :
    thickening r (segment ℝ y (y + w)) ⊆ thickening (4 * r) W := by
  have hx : x ∈ thickening s (segment ℝ x (x + v)) :=
    self_subset_thickening hs _ (left_mem_segment ℝ x (x + v))
  have hxv : x + v ∈ thickening s (segment ℝ x (x + v)) :=
    self_subset_thickening hs _ (right_mem_segment ℝ x (x + v))
  have hy : y ∈ thickening (3 * r) W ∧ y + w ∈ thickening (3 * r) W := by
    rcases parent_endpoints hv hw (hparent hx) (hparent hxv) with h | h
    · exact ⟨mem_thickening_iff.mpr ⟨x, hchild hx, h.1⟩,
        mem_thickening_iff.mpr ⟨x + v, hchild hxv, h.2⟩⟩
    · exact ⟨mem_thickening_iff.mpr ⟨x + v, hchild hxv, h.1⟩,
        mem_thickening_iff.mpr ⟨x, hchild hx, h.2⟩⟩
  have hseg := (hW.thickening (3 * r)).segment_subset hy.1 hy.2
  intro p hp
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  obtain ⟨z, hz, hqz⟩ := mem_thickening_iff.mp (hseg hq)
  exact mem_thickening_iff.mpr ⟨z, hz, (dist_triangle p q z).trans_lt (by linarith)⟩

end WangZahlLot.Obl.wz_tower_convex_count_composition
