-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.ZoomClosedFrostman.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.Zoom
import Submission.WZ.Obl.wz_separated_projection_dichotomy.FiniteLineMap

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

attribute [local instance] Classical.propDecidable

theorem zoom_mem_closedBall (b : Plane) {k : ℝ} (hk : 0 < k) (x y : Plane) (r : ℝ) :
    zoom b k y ∈ Metric.closedBall x r ↔
      y ∈ Metric.closedBall (b + k⁻¹ • x) (r / k) := by
  have hd : dist (zoom b k y) x = k * dist y (b + k⁻¹ • x) := by
    conv_lhs => rw [← zoom_inverse b hk.ne' x]
    exact zoom_dist b hk.le _ _
  simp only [Metric.mem_closedBall, hd]
  rw [le_div_iff₀ hk, mul_comm]

theorem ClosedFiniteFrostman.map_zoom {δ C k : ℝ} {S : Finset Plane}
    (h : ClosedFiniteFrostman δ C S) (b : Plane) (hk : 0 < k) :
    ClosedFiniteFrostman (k * δ) (C / k) (S.image (zoom b k)) := by
  classical
  intro x r hδr
  have hscale : δ ≤ r / k := (le_div_iff₀ hk).mpr (by nlinarith)
  have hfilt : (S.image (zoom b k)).filter (fun y => y ∈ Metric.closedBall x r) =
      (S.filter (fun y => y ∈ Metric.closedBall (b + k⁻¹ • x) (r / k))).image (zoom b k) := by
    rw [Finset.filter_image]
    congr 1
    ext y
    simp only [Finset.mem_filter, zoom_mem_closedBall b hk]
  have hcount := h.filter_closedBall (b + k⁻¹ • x) (r / k) hscale
  have hset : ((↑(S.image (zoom b k)) : Set Plane) ∩ Metric.closedBall x r) =
      ↑((S.image (zoom b k)).filter (fun y => y ∈ Metric.closedBall x r)) := by
    ext y
    simp only [Set.mem_inter_iff, Finset.mem_coe, Finset.mem_filter]
  rw [hset, Set.ncard_coe_finset, hfilt,
    Finset.card_image_of_injective _ (zoom_injective b hk),
    Finset.card_image_of_injective _ (zoom_injective b hk)]
  simp only [Metric.mem_closedBall]
  convert hcount using 1 <;> ring

theorem IndexedLineFrostman.map_zoom {I : Type*} [Fintype I] {f : I → Plane}
    {δ C ζ k : ℝ} (h : IndexedLineFrostman δ C ζ f) (b : Plane) (hk : 0 < k) :
    IndexedLineFrostman (k * δ) (C / k) ζ (fun i => zoom b k (f i)) := by
  intro u a r hu hδr
  have hscale : δ ≤ r / k := (le_div_iff₀ hk).mpr (by nlinarith)
  have hi (i : I) : |inner ℝ (zoom b k (f i)) u - a| < r ↔
      |inner ℝ (f i) u - (inner ℝ b u + a / k)| < r / k := by
    have heq : inner ℝ (zoom b k (f i)) u - a =
        k * (inner ℝ (f i) u - (inner ℝ b u + a / k)) := by
      simp only [zoom, real_inner_smul_left, inner_sub_left]
      field_simp
      <;> ring
    rw [heq, abs_mul, abs_of_pos hk, lt_div_iff₀ hk, mul_comm]
  have hfilt : Finset.univ.filter (fun i => |inner ℝ (zoom b k (f i)) u - a| < r) =
      Finset.univ.filter (fun i => |inner ℝ (f i) u - (inner ℝ b u + a / k)| < r / k) := by
    ext i
    simp only [Finset.mem_filter, hi]
  rw [hfilt]
  convert h u (inner ℝ b u + a / k) (r / k) hu hscale using 1 <;> congr 2 <;> ring

theorem IndexedLineFrostman.image_zoom {δ C ζ k : ℝ} {S : Finset Plane}
    (h : IndexedLineFrostman δ C ζ (fun x : S => (x : Plane)))
    (b : Plane) (hk : 0 < k) :
    IndexedLineFrostman (k * δ) (C / k) ζ (fun y : S.image (zoom b k) => (y : Plane)) :=
  indexedLineFrostman_image (zoom_injective b hk) (h.map_zoom b hk)

end WangZahlLot.Obl.wz_separated_projection_dichotomy
