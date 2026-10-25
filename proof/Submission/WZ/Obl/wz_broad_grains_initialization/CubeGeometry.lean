-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_initialization.CubeGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_initialization.LocalCount
import Submission.WZ.Obl.wz_balanced_cluster_cover.Basic

namespace WangZahlLot.Obl.wz_broad_grains_initialization

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open wz_clustered_cover_volume_gain.Parent.Factor (box)

/-- The isotropic prisms used at unit coarse scale. -/
def cube (c : ℝ) (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) : Set Space := box c c c z e

lemma mem_cube_iff {c : ℝ} {z p : Space} {e : Space ≃ₗᵢ[ℝ] Space} :
    p ∈ cube c z e ↔ ∀ i : Fin 3, |e (p - z) i| ≤ c / 2 := by
  constructor
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i <;> assumption
  · intro h
    exact ⟨h 0, h 1, h 2⟩

lemma cube_isClosed (c : ℝ) (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) :
    IsClosed (cube c z e) := by
  have he : cube c z e = ⋂ i : Fin 3, {p | |e (p - z) i| ≤ c / 2} := by
    ext p
    simp only [mem_cube_iff, mem_iInter, mem_ofPred_eq]
  rw [he]
  apply isClosed_iInter
  intro i
  exact isClosed_le (by fun_prop) continuous_const

lemma cube_coord_lt_mem_interior {c : ℝ} {z p : Space} {e : Space ≃ₗᵢ[ℝ] Space}
    (hp : ∀ i : Fin 3, |e (p - z) i| < c / 2) : p ∈ interior (cube c z e) := by
  let U : Set Space := ⋂ i : Fin 3, {q | |e (q - z) i| < c / 2}
  have hU : IsOpen U := isOpen_iInter_of_finite fun i =>
    isOpen_lt (by fun_prop) continuous_const
  have hsub : U ⊆ cube c z e := by
    intro q hq
    apply mem_cube_iff.mpr
    intro i
    exact (mem_iInter.mp hq i).le
  exact (interior_maximal hsub hU) (mem_iInter.mpr hp)

lemma cube_distance_le {c : ℝ} (hc : 0 ≤ c) {z p q : Space}
    {e : Space ≃ₗᵢ[ℝ] Space} (hp : p ∈ cube c z e) (hq : q ∈ cube c z e) :
    dist p q ≤ 2 * c := by
  rw [dist_eq_norm, ← e.norm_map (p - q)]
  apply wz_balanced_cluster_cover.norm_le_of_forall_abs_le hc
  intro i
  have he : e (p - q) i = e (p - z) i - e (q - z) i := by
    simp only [map_sub, PiLp.sub_apply]
    ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith [(mem_cube_iff.mp hp i), (mem_cube_iff.mp hq i)])

lemma tube_axis_coord_error {δ : ℝ} {x v p z : Space}
    (e : Space ≃ₗᵢ[ℝ] Space) {s : ℝ} (hs : ‖p - (x + s • v)‖ < δ) (i : Fin 3) :
    |e (p - z) i - (e (x - z) i + s * e v i)| < δ := by
  have he : e (p - z) i - (e (x - z) i + s * e v i) =
      e (p - (x + s • v)) i := by
    simp only [map_sub, map_add, map_smul, PiLp.sub_apply, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul]
    ring
  rw [he]
  exact (wz_balanced_cluster_cover.abs_apply_le_norm _ _).trans_lt
    (by simpa only [e.norm_map] using hs)

lemma cube_parameter_close {c δ : ℝ} (hc : 0 < c) (hδc : δ ≤ c / 100)
    {x v z p q : Space} (e : Space ≃ₗᵢ[ℝ] Space)
    (hv : 1 / 2 ≤ e v 2) (hp : p ∈ cube (c / 10) z e) (hq : q ∈ cube c z e)
    {s t : ℝ} (hs : ‖p - (x + s • v)‖ < δ) (ht : ‖q - (x + t • v)‖ < δ) :
    |t - s| ≤ 2 * c := by
  have hep := tube_axis_coord_error e hs (z := z) 2
  have heq := tube_axis_coord_error e ht (z := z) 2
  have ha := abs_sub (e (q - z) 2) (e (p - z) 2)
  have hb := abs_sub (e (q - z) 2 - e (p - z) 2)
    (e (q - z) 2 - (e (x - z) 2 + t * e v 2))
  have hd := abs_add_le
    (e (q - z) 2 - e (p - z) 2 -
      (e (q - z) 2 - (e (x - z) 2 + t * e v 2)))
    (e (p - z) 2 - (e (x - z) 2 + s * e v 2))
  have he : e (q - z) 2 - e (p - z) 2 -
      (e (q - z) 2 - (e (x - z) 2 + t * e v 2)) +
      (e (p - z) 2 - (e (x - z) 2 + s * e v 2)) = (t - s) * e v 2 := by ring
  rw [he, abs_mul, abs_of_nonneg (by linarith : 0 ≤ e v 2)] at hd
  have hp2 := mem_cube_iff.mp hp 2
  have hq2 := mem_cube_iff.mp hq 2
  have hlo := mul_le_mul_of_nonneg_left hv (abs_nonneg (t - s))
  nlinarith

/-- A tube that meets the core of a cube at a small angle to its long axis
cannot meet either of its two short faces. -/
theorem tube_cube_short_coord {c δ : ℝ} (hc : 0 < c) (hδc : δ ≤ c / 100)
    {x v z p q : Space} (e : Space ≃ₗᵢ[ℝ] Space)
    (hvlong : 1 / 2 ≤ e v 2)
    (hvshort : ∀ j : Fin 3, j ≠ 2 → |e v j| ≤ 1 / 100)
    (hpT : p ∈ Metric.thickening δ (segment ℝ x (x + v)))
    (hp : p ∈ cube (c / 10) z e)
    (hqT : q ∈ Metric.thickening δ (segment ℝ x (x + v))) (hq : q ∈ cube c z e)
    (j : Fin 3) (hj : j ≠ 2) : |e (q - z) j| < c / 2 := by
  obtain ⟨s, _, hs⟩ := wz_balanced_cluster_cover.exists_param_of_mem_tube hpT
  obtain ⟨t, _, ht⟩ := wz_balanced_cluster_cover.exists_param_of_mem_tube hqT
  have hst := cube_parameter_close hc hδc e hvlong hp hq hs ht
  have hep := tube_axis_coord_error e hs (z := z) j
  have heq := tube_axis_coord_error e ht (z := z) j
  have hmul : |(t - s) * e v j| ≤ 2 * c * (1 / 100) := by
    rw [abs_mul]
    exact mul_le_mul hst (hvshort j hj) (abs_nonneg _) (by positivity)
  have ha := abs_add_le (e (p - z) j) ((t - s) * e v j)
  have hb := abs_sub (e (p - z) j + (t - s) * e v j)
    (e (p - z) j - (e (x - z) j + s * e v j))
  have hd := abs_add_le
    (e (p - z) j + (t - s) * e v j -
      (e (p - z) j - (e (x - z) j + s * e v j)))
    (e (q - z) j - (e (x - z) j + t * e v j))
  have he : e (p - z) j + (t - s) * e v j -
      (e (p - z) j - (e (x - z) j + s * e v j)) +
      (e (q - z) j - (e (x - z) j + t * e v j)) = e (q - z) j := by ring
  rw [he] at hd
  have hpj := mem_cube_iff.mp hp j
  linarith

/-- Every boundary crossing is through one of the two long faces. -/
theorem tube_cube_frontier {c δ : ℝ} (hc : 0 < c) (hδc : δ ≤ c / 100)
    {x v z p : Space} (e : Space ≃ₗᵢ[ℝ] Space)
    (hvlong : 1 / 2 ≤ e v 2)
    (hvshort : ∀ j : Fin 3, j ≠ 2 → |e v j| ≤ 1 / 100)
    (hpT : p ∈ Metric.thickening δ (segment ℝ x (x + v)))
    (hp : p ∈ cube (c / 10) z e) :
    ∀ q ∈ Metric.thickening δ (segment ℝ x (x + v)) ∩ frontier (cube c z e),
      |e (q - z) 2| = c / 2 := by
  intro q hq
  have hqU : q ∈ cube c z e := (cube_isClosed c z e).frontier_subset hq.2
  apply le_antisymm (mem_cube_iff.mp hqU 2)
  by_contra hn
  have hi : q ∈ interior (cube c z e) := by
    apply cube_coord_lt_mem_interior
    intro j
    by_cases hj : j = 2
    · subst j
      exact lt_of_not_ge hn
    · exact tube_cube_short_coord hc hδc e hvlong hvshort hpT hp hq.1 hqU j hj
  exact hq.2.2 hi

/-- A core point away from the tube endpoints guarantees both long-face crossings. -/
theorem tube_cube_crosses {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hδc : δ ≤ c / 100)
    {x v z p : Space} (e : Space ≃ₗᵢ[ℝ] Space) (hv : ‖v‖ = 1)
    (hvlong : 1 / 2 ≤ e v 2)
    (hvshort : ∀ j : Fin 3, j ≠ 2 → |e v j| ≤ 1 / 100)
    (hpT : p ∈ Metric.thickening δ (segment ℝ x (x + v)))
    (hp : p ∈ cube (c / 10) z e)
    (hleft : 4 * c ≤ dist p x) (hright : 4 * c ≤ dist p (x + v)) :
    ∀ t ∈ ({-c / 2, c / 2} : Set ℝ),
      ∃ q ∈ Metric.thickening δ (segment ℝ x (x + v)) ∩ cube c z e,
        e (q - z) 2 = t := by
  obtain ⟨s, hs, hps⟩ := wz_balanced_cluster_cover.exists_param_of_mem_tube hpT
  have hslo : 2 * c ≤ s := by
    have h := dist_triangle p (x + s • v) x
    have he : dist (x + s • v) x = s := by
      simp [dist_eq_norm, norm_smul, hv, abs_of_nonneg hs.1]
    rw [he] at h
    have hps' : dist p (x + s • v) < δ := hps
    linarith
  have hshi : s ≤ 1 - 2 * c := by
    have h := dist_triangle p (x + s • v) (x + v)
    have he : dist (x + s • v) (x + v) = 1 - s := by
      rw [dist_eq_norm, show x + s • v - (x + v) = (s - 1) • v by module,
        norm_smul, hv, Real.norm_eq_abs, mul_one, abs_of_nonpos (by linarith [hs.2] : s - 1 ≤ 0)]
      ring
    rw [he] at h
    have hps' : dist p (x + s • v) < δ := hps
    linarith
  intro t ht
  have htbound : |t| ≤ c / 2 := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl <;> rw [abs_div] <;> simp [abs_of_pos hc]
  have hwpos : 0 < e v 2 := by linarith
  let τ : ℝ := (t - e (x - z) 2) / e v 2
  have hτeq : τ * e v 2 = t - e (x - z) 2 := div_mul_cancel₀ _ hwpos.ne'
  have hτnear : |τ - s| ≤ 2 * c := by
    have hep := tube_axis_coord_error e hps (z := z) 2
    have hnum : (τ - s) * e v 2 = t - e (p - z) 2 +
        (e (p - z) 2 - (e (x - z) 2 + s * e v 2)) := by nlinarith [hτeq]
    have ha := abs_sub t (e (p - z) 2)
    have hb := abs_add_le (t - e (p - z) 2)
      (e (p - z) 2 - (e (x - z) 2 + s * e v 2))
    rw [← hnum, abs_mul, abs_of_pos hwpos] at hb
    have hlo := mul_le_mul_of_nonneg_left hvlong (abs_nonneg (τ - s))
    have hp2 := mem_cube_iff.mp hp 2
    nlinarith
  have hτIcc : τ ∈ Set.Icc (0 : ℝ) 1 := by
    have habs := abs_le.mp hτnear
    constructor <;> linarith
  let q : Space := x + τ • v
  have hqT : q ∈ Metric.thickening δ (segment ℝ x (x + v)) := by
    apply Metric.self_subset_thickening hδ
    rw [segment_eq_image']
    exact ⟨τ, hτIcc, by simp [q]⟩
  have hq2 : e (q - z) 2 = t := by
    have he : e (q - z) 2 = e (x - z) 2 + τ * e v 2 := by
      simp only [q, map_sub, map_add, map_smul, PiLp.sub_apply, PiLp.add_apply,
        PiLp.smul_apply, smul_eq_mul]
      ring
    rw [he]
    linarith
  refine ⟨q, ⟨hqT, mem_cube_iff.mpr ?_⟩, hq2⟩
  intro j
  by_cases hj : j = 2
  · simpa only [hj, hq2] using htbound
  · have hep := tube_axis_coord_error e hps (z := z) j
    have hmul : |(τ - s) * e v j| ≤ 2 * c * (1 / 100) := by
      rw [abs_mul]
      exact mul_le_mul hτnear (hvshort j hj) (abs_nonneg _) (by positivity)
    have ha := abs_add_le (e (p - z) j) ((τ - s) * e v j)
    have hb := abs_sub (e (p - z) j + (τ - s) * e v j)
      (e (p - z) j - (e (x - z) j + s * e v j))
    have he : e (p - z) j + (τ - s) * e v j -
        (e (p - z) j - (e (x - z) j + s * e v j)) = e (q - z) j := by
      simp only [q, map_sub, map_add, map_smul, PiLp.sub_apply, PiLp.add_apply,
        PiLp.smul_apply, smul_eq_mul]
      ring
    rw [he] at hb
    have hpj := mem_cube_iff.mp hp j
    linarith

/-- Strict convexity of the unit ball gives a uniform clearance from its
boundary on the interior of a unit segment. -/
lemma unit_segment_norm_sq {x v : Space} (hx : ‖x‖ ≤ 1) (hxv : ‖x + v‖ ≤ 1)
    (hv : ‖v‖ = 1) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ‖x + s • v‖ ^ 2 ≤ 1 - s * (1 - s) := by
  have hx2 : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
  have hxv2 : ‖x + v‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (x + v)]
  have he : ‖x + s • v‖ ^ 2 = (1 - s) * ‖x‖ ^ 2 +
      s * ‖x + v‖ ^ 2 - s * (1 - s) := by
    rw [norm_add_sq_real x (s • v), norm_add_sq_real x v,
      inner_smul_right, norm_smul, hv, Real.norm_eq_abs, mul_one, sq_abs]
    ring
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left hx2 (by linarith [hs.2] : 0 ≤ 1 - s),
    mul_le_mul_of_nonneg_left hxv2 hs.1]

/-- Trimming a fixed multiple of the grain length at both tube ends puts a
whole cube around each retained core point inside the unit ball. -/
theorem tube_core_cube_subset_ball {c δ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 1000)
    (hδ : 0 < δ) (hδc : δ ≤ c / 100) {x v z p : Space}
    (e : Space ≃ₗᵢ[ℝ] Space) (hv : ‖v‖ = 1)
    (hball : Metric.thickening δ (segment ℝ x (x + v)) ⊆ Metric.ball (0 : Space) 1)
    (hpT : p ∈ Metric.thickening δ (segment ℝ x (x + v)))
    (hp : p ∈ cube (c / 10) z e)
    (hleft : 100 * c ≤ dist p x) (hright : 100 * c ≤ dist p (x + v)) :
    cube c z e ⊆ Metric.ball (0 : Space) 1 := by
  have hx : ‖x‖ ≤ 1 := by
    have := hball (Metric.self_subset_thickening hδ _ (left_mem_segment ℝ x (x + v)))
    exact le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using this)
  have hxv : ‖x + v‖ ≤ 1 := by
    have := hball (Metric.self_subset_thickening hδ _ (right_mem_segment ℝ x (x + v)))
    exact le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using this)
  obtain ⟨s, hs, hps⟩ := wz_balanced_cluster_cover.exists_param_of_mem_tube hpT
  have hslo : 99 * c ≤ s := by
    have h := dist_triangle p (x + s • v) x
    have he : dist (x + s • v) x = s := by
      simp [dist_eq_norm, norm_smul, hv, abs_of_nonneg hs.1]
    rw [he] at h
    have hps' : dist p (x + s • v) < δ := hps
    linarith
  have hshi : 99 * c ≤ 1 - s := by
    have h := dist_triangle p (x + s • v) (x + v)
    have he : dist (x + s • v) (x + v) = 1 - s := by
      rw [dist_eq_norm, show x + s • v - (x + v) = (s - 1) • v by module,
        norm_smul, hv, Real.norm_eq_abs, mul_one, abs_of_nonpos (by linarith [hs.2] : s - 1 ≤ 0)]
      ring
    rw [he] at h
    have hps' : dist p (x + s • v) < δ := hps
    linarith
  have hprod : 40 * c ≤ s * (1 - s) := by
    by_cases hs2 : s ≤ 1 / 2
    · nlinarith [mul_nonneg (sub_nonneg.mpr hslo) (show 0 ≤ 1 - s by linarith)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hshi) hs.1]
  have hnorm := unit_segment_norm_sq hx hxv hv hs
  have hclear : ‖x + s • v‖ < 1 - 3 * c := by
    nlinarith [norm_nonneg (x + s • v)]
  have hpU : p ∈ cube c z e := by
    apply mem_cube_iff.mpr
    intro i
    linarith [mem_cube_iff.mp hp i]
  intro q hq
  have hqp := cube_distance_le hc.le hq hpU
  have htri := dist_triangle q p (x + s • v)
  have hn' : ‖q‖ ≤ dist q (x + s • v) + ‖x + s • v‖ := by
    simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (q - (x + s • v)) (x + s • v)
  rw [Metric.mem_ball, dist_zero_right]
  have hps' : dist p (x + s • v) < δ := hps
  linarith

end WangZahlLot.Obl.wz_broad_grains_initialization
