-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_tower_depth_step.DoubleSlabGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_tower_depth_step.SlabTransport
import Submission.WZ.Obl.wz_tower_depth_step.TubeVolume

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_tower_depth_step

open Set Metric MeasureTheory

lemma isClosed_slab (u : Space) (t ρ : ℝ) : IsClosed (Slab u t ρ) :=
  isClosed_le (by fun_prop) continuous_const

lemma ball_slab_projection_bounds {r t ρ : ℝ} (hr : 0 < r) {x u : Space}
    (hu : ‖u‖ = 1) (hsub : ball x r ⊆ Slab u t ρ) :
    t - ρ ≤ inner ℝ u x - r ∧ inner ℝ u x + r ≤ t + ρ := by
  have hclosed : closedBall x r ⊆ Slab u t ρ := by
    rw [← closure_ball x hr.ne']
    exact closure_minimal hsub (isClosed_slab u t ρ)
  have hp : x + r • u ∈ closedBall x r := by
    simp only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, hu, mul_one, abs_of_pos hr, le_refl]
  have hn : x + (-r) • u ∈ closedBall x r := by
    simp only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, hu, mul_one, abs_neg, abs_of_pos hr, le_refl]
  have hp' := abs_le.mp (show |inner ℝ u (x + r • u) - t| ≤ ρ from hclosed hp)
  have hn' := abs_le.mp (show |inner ℝ u (x + (-r) • u) - t| ≤ ρ from hclosed hn)
  simp only [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq,
    hu, one_pow, mul_one] at hp' hn'
  constructor <;> linarith

/-- The exact closed projection interval of a tube is contained in every slab
containing the tube. -/
lemma tube_slab_projection_bounds {r t ρ : ℝ} (hr : 0 < r) {x v u : Space}
    (hu : ‖u‖ = 1) (hsub : Tube r x v ⊆ Slab u t ρ) :
    t - ρ ≤ inner ℝ u (x + (1 / 2 : ℝ) • v) - (r + |inner ℝ u v| / 2) ∧
      inner ℝ u (x + (1 / 2 : ℝ) • v) + (r + |inner ℝ u v| / 2) ≤ t + ρ := by
  have hleft := ball_slab_projection_bounds hr hu
    ((ball_subset_thickening (left_mem_segment ℝ x (x + v)) r).trans hsub)
  have hright := ball_slab_projection_bounds hr hu
    ((ball_subset_thickening (right_mem_segment ℝ x (x + v)) r).trans hsub)
  simp only [inner_add_right, inner_smul_right] at hright ⊢
  rcases le_total 0 (inner ℝ u v) with hv | hv
  · rw [abs_of_nonneg hv]
    constructor <;> linarith [hleft.1, hright.2]
  · rw [abs_of_nonpos hv]
    constructor <;> linarith [hright.1, hleft.2]

lemma tube_projection_abs_lt {r : ℝ} {x v p u : Space} (hu : ‖u‖ = 1)
    (hp : p ∈ Tube r x v) :
    |inner ℝ u p - inner ℝ u (x + (1 / 2 : ℝ) • v)| < r + |inner ℝ u v| / 2 := by
  obtain ⟨z, hz, hpz⟩ := mem_thickening_iff.mp hp
  rw [segment_eq_image'] at hz
  obtain ⟨a, ha, rfl⟩ := hz
  have he : |inner ℝ u (p - (x + a • v))| < r := by
    apply (abs_real_inner_le_norm _ _).trans_lt
    simpa only [hu, one_mul, dist_eq_norm, add_sub_cancel_left] using hpz
  have ha' : |a - 1 / 2| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith [ha.1, ha.2]
  have hformula : inner ℝ u p - inner ℝ u (x + (1 / 2 : ℝ) • v) =
      inner ℝ u (p - (x + a • v)) + (a - 1 / 2) * inner ℝ u v := by
    simp only [inner_sub_right, inner_add_right, inner_smul_right]
    ring
  rw [hformula]
  calc
    _ ≤ |inner ℝ u (p - (x + a • v))| + |(a - 1 / 2) * inner ℝ u v| := abs_add_le _ _
    _ < r + (1 / 2) * |inner ℝ u v| := add_lt_add_of_lt_of_le he (by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right ha' (abs_nonneg _))
    _ = _ := by ring

lemma doubled_tube_projection {r : ℝ} {y w p u : Space} (hu : ‖u‖ = 1)
    (hp : p ∈ Tube (2 * r) (y - (1 / 2 : ℝ) • w) (2 • w)) :
    |inner ℝ u p - inner ℝ u (y + (1 / 2 : ℝ) • w)| ≤
      2 * (r + |inner ℝ u w| / 2) := by
  have hh := tube_projection_abs_lt hu hp
  have he : y - (1 / 2 : ℝ) • w + (1 / 2 : ℝ) • (2 • w) = y + (1 / 2 : ℝ) • w := by module
  have hw : |inner ℝ u (2 • w)| = 2 * |inner ℝ u w| := by
    rw [two_smul, inner_add_right, ← two_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [he, hw] at hh
  linarith

/-- The interval hull of finitely many symmetric intervals has a midpoint in the
convex hull of their centers. Doubling each interval stays inside twice that hull. -/
theorem projection_interval_hull_scaled {ι : Type*} [DecidableEq ι]
    {K : ℝ} (hK : 1 ≤ K)
    (I : Finset ι) (hI : I.Nonempty) (p : ι → Space) (d : ι → ℝ)
    {D : Set Space} (hD : Convex ℝ D) {u : Space} {t ρ : ℝ}
    (hp : ∀ i ∈ I, p i ∈ D) (hd : ∀ i ∈ I, 0 < d i)
    (hbounds : ∀ i ∈ I, t - ρ ≤ inner ℝ u (p i) - d i ∧
      inner ℝ u (p i) + d i ≤ t + ρ) :
    ∃ (t' β : ℝ) (p₀ : Space), 0 < β ∧ p₀ ∈ D ∧ inner ℝ u p₀ = t' ∧
      Slab u t' β ⊆ Slab u t ρ ∧
      ∀ i ∈ I, ∀ q : Space, |inner ℝ u q - inner ℝ u (p i)| ≤ K * d i →
        q ∈ Slab u t' (K * β) := by
  obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image I (fun i => inner ℝ u (p i) - d i) hI
  obtain ⟨b, hb, hmax⟩ := Finset.exists_max_image I (fun i => inner ℝ u (p i) + d i) hI
  let l := inner ℝ u (p a) - d a
  let h := inner ℝ u (p b) + d b
  let t' := (l + h) / 2
  let β := (h - l) / 2
  have hcenters : inner ℝ u (p a) ≤ t' ∧ t' ≤ inner ℝ u (p b) := by
    have h₀ := hmax a ha
    have h₁ := hmin b hb
    dsimp only [t', l, h]
    constructor <;> linarith
  have hβ : 0 < β := by
    have h₀ := hmax a ha
    have hda := hd a ha
    dsimp only [β, l, h]
    linarith
  have hconv : Convex ℝ ((fun x : Space => inner ℝ u x) '' D) :=
    hD.linear_image (innerSL ℝ u).toLinearMap
  have hmid : t' ∈ (fun x : Space => inner ℝ u x) '' D :=
    hconv.segment_subset ⟨p a, hp a ha, rfl⟩ ⟨p b, hp b hb, rfl⟩
      (by rw [segment_eq_Icc (hcenters.1.trans hcenters.2)]; exact hcenters)
  obtain ⟨p₀, hp₀, he⟩ := hmid
  refine ⟨t', β, p₀, hβ, hp₀, he, ?_, ?_⟩
  · intro q hq
    have hq' := abs_le.mp (show |inner ℝ u q - t'| ≤ β from hq)
    have hlo := (hbounds a ha).1
    have hhi := (hbounds b hb).2
    change |inner ℝ u q - t| ≤ ρ
    rw [abs_le]
    dsimp only [t', β, l, h] at hq'
    constructor <;> linarith [hq'.1, hq'.2]
  · intro i hi q hq
    have hlow := hmin i hi
    have hhigh := hmax i hi
    have hdi : d i ≤ β := by dsimp only [β, l, h]; linarith
    have hc : |inner ℝ u (p i) - t'| ≤ β - d i := by
      rw [abs_le]
      dsimp only [t', β, l, h]
      constructor <;> linarith
    have hprod := mul_le_mul_of_nonneg_left hdi (show 0 ≤ K - 1 by linarith)
    change |inner ℝ u q - t'| ≤ K * β
    exact (abs_sub_le (inner ℝ u q) (inner ℝ u (p i)) t').trans (by linarith)

/-- The twofold version of the projection-interval hull. -/
theorem projection_interval_hull {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (hI : I.Nonempty) (p : ι → Space) (d : ι → ℝ)
    {D : Set Space} (hD : Convex ℝ D) {u : Space} {t ρ : ℝ}
    (hp : ∀ i ∈ I, p i ∈ D) (hd : ∀ i ∈ I, 0 < d i)
    (hbounds : ∀ i ∈ I, t - ρ ≤ inner ℝ u (p i) - d i ∧
      inner ℝ u (p i) + d i ≤ t + ρ) :
    ∃ (t' β : ℝ) (p₀ : Space), 0 < β ∧ p₀ ∈ D ∧ inner ℝ u p₀ = t' ∧
      Slab u t' β ⊆ Slab u t ρ ∧
      ∀ i ∈ I, ∀ q : Space, |inner ℝ u q - inner ℝ u (p i)| ≤ 2 * d i →
        q ∈ Slab u t' (2 * β) :=
  projection_interval_hull_scaled (by norm_num : (1 : ℝ) ≤ 2) I hI p d hD hp hd hbounds

/-- A slab centered at a projection of a point of a convex body has a uniform
volume-doubling bound, even near the boundary of the body. -/
theorem centered_slab_volume_double {D : Set Space} (hD : Convex ℝ D)
    {p u : Space} {t β : ℝ} (hp : p ∈ D) (he : inner ℝ u p = t) :
    volume (D ∩ Slab u t (2 * β)) ≤ (8 : ENNReal) * volume (D ∩ Slab u t β) := by
  have hsub : AffineMap.homothety p (1 / 2 : ℝ) '' (D ∩ Slab u t (2 * β)) ⊆ D ∩ Slab u t β := by
    rintro z ⟨q, hq, rfl⟩
    constructor
    · have hz : AffineMap.homothety p (1 / 2 : ℝ) q ∈ segment ℝ p q := by
        rw [segment_eq_image']
        exact ⟨1 / 2, by norm_num, by simp [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, add_comm]⟩
      exact hD.segment_subset hp hq.1 hz
    · have hq' := abs_le.mp (show |inner ℝ u q - t| ≤ 2 * β from hq.2)
      change |inner ℝ u (AffineMap.homothety p (1 / 2 : ℝ) q) - t| ≤ β
      simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, inner_add_right,
        inner_smul_right, inner_sub_right, he]
      rw [abs_le]
      constructor <;> linarith [hq'.1, hq'.2]
  have hh := mul_le_mul' (le_refl (8 : ENNReal)) (measure_mono (μ := volume) hsub)
  rw [Measure.addHaar_image_homothety, finrank_euclideanSpace_fin] at hh
  norm_num [← mul_assoc, ENNReal.ofReal_div_of_pos] at hh
  simpa only [ENNReal.mul_inv_cancel (by norm_num : (8 : ENNReal) ≠ 0)
    (by norm_num : (8 : ENNReal) ≠ ⊤), one_mul] using hh

/-- All doubled covers whose unit covers lie in one slab are controlled by a
single enlarged slab, with a dimension-only loss for its section of the parent. -/
theorem doubled_cover_slab_test {n : ℕ} (I : Finset (Fin n)) (hI : I.Nonempty)
    (r : Fin n → ℝ) (x v : Fin n → Space) (hr : ∀ i ∈ I, 0 < r i)
    {D : Set Space} (hD : Convex ℝ D) {u : Space} (hu : ‖u‖ = 1) {t ρ : ℝ}
    (hcover : ∀ i ∈ I, Tube (r i) (x i) (v i) ⊆ D ∩ Slab u t ρ) :
    ∃ t' β : ℝ, 0 < β ∧
      (∀ i ∈ I, Tube (2 * r i) (x i - (1 / 2 : ℝ) • v i) (2 • v i) ⊆ Slab u t' (2 * β)) ∧
      volume (D ∩ Slab u t' (2 * β)) ≤ (8 : ENNReal) * volume (D ∩ Slab u t ρ) := by
  let p := fun i => x i + (1 / 2 : ℝ) • v i
  let d := fun i => r i + |inner ℝ u (v i)| / 2
  have hp (i) (hi : i ∈ I) : p i ∈ D := by
    apply (hcover i hi _).1
    apply self_subset_thickening (hr i hi)
    rw [segment_eq_image']
    exact ⟨1 / 2, by norm_num, by simp [p]⟩
  have hd (i) (hi : i ∈ I) : 0 < d i :=
    add_pos_of_pos_of_nonneg (hr i hi) (by positivity)
  have hb (i) (hi : i ∈ I) : t - ρ ≤ inner ℝ u (p i) - d i ∧
      inner ℝ u (p i) + d i ≤ t + ρ :=
    tube_slab_projection_bounds (hr i hi) hu ((hcover i hi).trans inter_subset_right)
  obtain ⟨t', β, p₀, hβ, hp₀, he, hsmall, hlarge⟩ :=
    projection_interval_hull I hI p d hD hp hd hb
  refine ⟨t', β, hβ, ?_, ?_⟩
  · intro i hi q hq
    exact hlarge i hi q (doubled_tube_projection hu hq)
  · exact (centered_slab_volume_double hD hp₀ he).trans
      (mul_le_mul' le_rfl (measure_mono (Set.inter_subset_inter_right D hsmall)))

end WangZahlLot.Obl.wz_tower_depth_step
