-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.Zoom.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.Quantization

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

open Set Metric

noncomputable def zoom (b : Plane) (k : ℝ) (x : Plane) : Plane := k • (x - b)

theorem zoom_dist (b : Plane) {k : ℝ} (hk : 0 ≤ k) (x y : Plane) :
    dist (zoom b k x) (zoom b k y) = k * dist x y := by
  simp only [zoom, dist_smul₀, dist_sub_right, Real.norm_of_nonneg hk]

theorem zoom_injective (b : Plane) {k : ℝ} (hk : 0 < k) :
    Function.Injective (zoom b k) := by
  intro x y hxy
  have h := zoom_dist b hk.le x y
  rw [hxy, dist_self] at h
  exact dist_eq_zero.mp ((mul_eq_zero.mp h.symm).resolve_left hk.ne')

theorem zoom_inverse (b : Plane) {k : ℝ} (hk : k ≠ 0) (x : Plane) :
    zoom b k (b + k⁻¹ • x) = x := by
  simp only [zoom, add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hk, one_smul]

theorem zoom_mem_ball (b : Plane) {k : ℝ} (hk : 0 < k) (x y : Plane) (r : ℝ) :
    zoom b k y ∈ Metric.ball x r ↔ y ∈ Metric.ball (b + k⁻¹ • x) (r / k) := by
  have hd : dist (zoom b k y) x = k * dist y (b + k⁻¹ • x) := by
    conv_lhs => rw [← zoom_inverse b hk.ne' x]
    exact zoom_dist b hk.le _ _
  simp only [Metric.mem_ball, hd]
  rw [lt_div_iff₀ hk, mul_comm]

/-- Translation and positive dilation transport a finite Frostman bound with
the exact change of scale and constant. -/
theorem FiniteFrostman.map_zoom {δ C k : ℝ} {S : Finset Plane}
    (h : FiniteFrostman δ C S) (b : Plane) (hk : 0 < k) :
    FiniteFrostman (k * δ) (C / k) (S.image (zoom b k)) := by
  classical
  intro x r hδr
  have hscale : δ ≤ r / k := (le_div_iff₀ hk).mpr (by nlinarith)
  have hfilter : (S.image (zoom b k)).filter (fun y => y ∈ Metric.ball x r) =
      (S.filter (fun y => y ∈ Metric.ball (b + k⁻¹ • x) (r / k))).image (zoom b k) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hzb⟩
      exact ⟨z, ⟨hz, (zoom_mem_ball b hk x z r).mp hzb⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hzb⟩, rfl⟩
      exact ⟨⟨z, hz, rfl⟩, (zoom_mem_ball b hk x z r).mpr hzb⟩
  have hcount : ballCount (S.image (zoom b k)) x r =
      ballCount S (b + k⁻¹ • x) (r / k) := by
    dsimp [ballCount]
    rw [hfilter, Finset.card_image_of_injective _ (zoom_injective b hk)]
  rw [hcount, Finset.card_image_of_injective _ (zoom_injective b hk)]
  convert h (b + k⁻¹ • x) (r / k) hscale using 1 <;> ring

noncomputable def zoomTriple (b : Plane) (α β : ℝ) (p : Triple) : Triple :=
  (zoom 0 α p.1, zoom b β p.2.1, zoom b β p.2.2)

theorem dotValue_zoomTriple (b : Plane) (α β : ℝ) (p : Triple) :
    dotValue (zoomTriple b α β p) = (α * β) * dotValue p := by
  simp only [dotValue, zoomTriple, zoom, sub_zero, ← smul_sub,
    sub_sub_sub_cancel_right, real_inner_smul_left, real_inner_smul_right]
  ring

theorem zoomTriple_injective (b : Plane) {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    Function.Injective (zoomTriple b α β) := by
  intro p q hpq
  have ha := (zoom_injective 0 hα) (congrArg Prod.fst hpq)
  have hb := (zoom_injective b hβ) (congrArg (fun p : Triple => p.2.1) hpq)
  have hc := (zoom_injective b hβ) (congrArg (fun p : Triple => p.2.2) hpq)
  exact Prod.ext ha (Prod.ext hb hc)

theorem DotSet.image_zoomTriple (b : Plane) (α β : ℝ) (Q : Set Triple) :
    DotSet (zoomTriple b α β '' Q) = (fun t : ℝ => (α * β) * t) '' DotSet Q := by
  ext t
  constructor
  · rintro ⟨q, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨dotValue p, ⟨p, hp, rfl⟩, (dotValue_zoomTriple b α β p).symm⟩
  · rintro ⟨t, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨zoomTriple b α β p, ⟨p, hp, rfl⟩, (dotValue_zoomTriple b α β p).symm⟩

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
