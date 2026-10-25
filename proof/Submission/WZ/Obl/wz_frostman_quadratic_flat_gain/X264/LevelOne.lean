-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264.LevelOne.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.Plates
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.AffinePacking
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.Geometry
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.PrismInterface
-- Copied from session x0264 (o072 branch, commit c1a4bfb, file LevelOne.lean), namespace renamed.

/-!
# Level i: the estimate `F` for the tubes inside one prism

`plateMap he c a b` sends the prism `prism a b c e₁ e₂ e₃` to the cube `[-1,1]³`: frame
coordinates `y ↦ (⟪e₁, y - c⟫, ⟪e₂, y - c⟫, ⟪e₃, y - c⟫)`, then `diag(1/a, 1/b, 1)`. It divides
volumes by `a b`. By `plate_sandwich` the image of a `δ`-tube in the prism is a convex body
between the boxes of half widths `(s/10, t/10, 1/10)` and `(10 s, 10 t, 10)`, with
`s = δ/(5b)`, `t = 3δ/(5a)`.

`level_one`: `PrismFrostmanEstimate σ ω` applied to these bodies. For tubes in one prism,
half-overlapping, with shading mass `s^η N δ²` and Frostman below with constant `s^(-η)`,
`|⋃ Y| ≥ a b · A s^e t^ω (N (s t)²)^(σ/2)`.
-/

namespace WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264

open MeasureTheory Set Metric

noncomputable section

/-- Frame coordinates `y ↦ (⟪e₁, y - c⟫, ⟪e₂, y - c⟫, ⟪e₃, y - c⟫)`. -/
def frameCoord {e₁ e₂ e₃ : Space} (he : Orthonormal ℝ ![e₁, e₂, e₃]) (c : Space) :
    Space ≃ᵃ[ℝ] Space :=
  (AffineEquiv.constVAdd ℝ Space (-c)).trans
    (orthonormalFrame he).repr.toLinearEquiv.toAffineEquiv

lemma frameCoord_apply {e₁ e₂ e₃ : Space} (he : Orthonormal ℝ ![e₁, e₂, e₃]) (c y : Space) :
    frameCoord he c y = (orthonormalFrame he).repr (y - c) := by
  simp [frameCoord, sub_eq_neg_add]

lemma frameCoord_coord {e₁ e₂ e₃ : Space} (he : Orthonormal ℝ ![e₁, e₂, e₃]) (c y : Space) :
    frameCoord he c y 0 = inner ℝ e₁ (y - c) ∧ frameCoord he c y 1 = inner ℝ e₂ (y - c) ∧
      frameCoord he c y 2 = inner ℝ e₃ (y - c) := by
  simp only [frameCoord_apply, OrthonormalBasis.repr_apply_apply, orthonormalFrame,
    WangZahlLot.Obl.wz_transverse_cell_weighted_cover.onb_apply]
  simp

lemma dist_frameCoord {e₁ e₂ e₃ : Space} (he : Orthonormal ℝ ![e₁, e₂, e₃]) (c y z : Space) :
    dist (frameCoord he c y) (frameCoord he c z) = dist y z := by
  rw [frameCoord_apply, frameCoord_apply, LinearIsometryEquiv.dist_map, dist_eq_norm,
    dist_eq_norm, sub_sub_sub_cancel_right]

lemma image_thickening_of_dist_eq (f : Space ≃ᵃ[ℝ] Space)
    (hf : ∀ y z, dist (f y) (f z) = dist y z) (r : ℝ) (S : Set Space) :
    f '' thickening r S = thickening r (f '' S) := by
  ext w
  simp only [mem_image, mem_thickening_iff]
  constructor
  · rintro ⟨y, ⟨z, hz, hyz⟩, rfl⟩
    exact ⟨f z, ⟨z, hz, rfl⟩, by rwa [hf]⟩
  · rintro ⟨_, ⟨z, hz, rfl⟩, hwz⟩
    refine ⟨f.symm w, ⟨z, hz, ?_⟩, f.apply_symm_apply w⟩
    rwa [← hf, f.apply_symm_apply]

/-- The image of a tube in frame coordinates is a tube. -/
lemma frameCoord_image_tube {e₁ e₂ e₃ : Space} (he : Orthonormal ℝ ![e₁, e₂, e₃])
    (c : Space) (δ : ℝ) (x v : Space) :
    frameCoord he c '' tube δ x v = tube δ (frameCoord he c x)
      (frameCoord he c (x + v) - frameCoord he c x) := by
  rw [tube, image_thickening_of_dist_eq _ (dist_frameCoord he c)]
  congr 1
  have h := image_segment ℝ (frameCoord he c).toAffineMap x (x + v)
  simp only [AffineEquiv.coe_toAffineMap] at h
  rw [h, add_sub_cancel]

lemma norm_frameCoord_sub {e₁ e₂ e₃ : Space} (he : Orthonormal ℝ ![e₁, e₂, e₃])
    (c x v : Space) : ‖frameCoord he c (x + v) - frameCoord he c x‖ = ‖v‖ := by
  rw [← dist_eq_norm, dist_frameCoord, dist_eq_norm, add_sub_cancel_left]

lemma frameCoord_image_prism_subset {e₁ e₂ e₃ : Space} (he : Orthonormal ℝ ![e₁, e₂, e₃])
    (a b : ℝ) (c : Space) : frameCoord he c '' prism a b c e₁ e₂ e₃ ⊆ stdBox a b := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨h0, h1, h2⟩ := frameCoord_coord he c y
  simp only [stdBox, mem_ofPred_eq]
  rw [h0, h1, h2]
  exact hy

lemma volume_frameCoord_image {e₁ e₂ e₃ : Space} (he : Orthonormal ℝ ![e₁, e₂, e₃])
    (c : Space) (U : Set Space) : volume (frameCoord he c '' U) = volume U := by
  have himage : frameCoord he c '' U =
      (orthonormalFrame he).repr '' ((fun y => -c + y) '' U) := by
    rw [Set.image_image]
    apply Set.image_congr
    intro y _
    rw [frameCoord_apply, sub_eq_neg_add]
  rw [himage, LinearIsometryEquiv.image_eq_preimage_symm,
    ((orthonormalFrame he).repr.symm.measurePreserving).measure_preimage_emb
      (orthonormalFrame he).repr.symm.toMeasurableEquiv.measurableEmbedding,
    Set.image_add_left, measure_preimage_add]

/-- `scaleLin a b` as a linear equivalence. -/
def scaleEquiv (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : Space ≃ₗ[ℝ] Space :=
  LinearEquiv.ofLinearMap (scaleLin a b) (scaleLin a⁻¹ b⁻¹)
    (LinearMap.ext fun p => scaleLin_inv_apply a b ha hb p)
    (LinearMap.ext fun p => scaleLin_inv_apply' a b ha hb p)

/-- The normalization of the prism `prism a b c e₁ e₂ e₃` to the cube `[-1,1]³`. -/
def plateMap {e₁ e₂ e₃ : Space} (he : Orthonormal ℝ ![e₁, e₂, e₃]) (c : Space) (a b : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) : Space ≃ᵃ[ℝ] Space :=
  (frameCoord he c).trans (scaleEquiv a b ha hb).toAffineEquiv

lemma plateMap_image {e₁ e₂ e₃ : Space} (he : Orthonormal ℝ ![e₁, e₂, e₃]) (c : Space)
    {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (U : Set Space) :
    plateMap he c a b ha hb '' U = scaleLin a b '' (frameCoord he c '' U) := by
  rw [Set.image_image]
  rfl

lemma volume_plateMap_image {e₁ e₂ e₃ : Space} (he : Orthonormal ℝ ![e₁, e₂, e₃])
    (c : Space) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (U : Set Space) :
    volume (plateMap he c a b ha.ne' hb.ne' '' U) = ENNReal.ofReal (a * b)⁻¹ * volume U := by
  rw [plateMap_image, volume_scaleLin_image ha hb, volume_frameCoord_image]

lemma plateMap_measurableSet {e₁ e₂ e₃ : Space} (he : Orthonormal ℝ ![e₁, e₂, e₃])
    (c : Space) {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) {U : Set Space} (hU : MeasurableSet U) :
    MeasurableSet (plateMap he c a b ha hb '' U) := by
  rw [← AffineEquiv.preimage_symm]
  exact hU.preimage (plateMap he c a b ha hb).symm.continuous_of_finiteDimensional.measurable

lemma scaleLin_stdBox_subset_ball {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    scaleLin a b '' stdBox a b ⊆ ball 0 10 := by
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨h0, h1, h2⟩ := hp
  rw [mem_ball_zero_iff]
  have hq0 : |p 0 / a| ≤ 1 := by rw [abs_div, abs_of_pos ha, div_le_one ha]; exact h0
  have hq1 : |p 1 / b| ≤ 1 := by rw [abs_div, abs_of_pos hb, div_le_one hb]; exact h1
  have hsq : ‖scaleLin a b p‖ ^ 2 ≤ 3 := by
    rw [norm_sq_coords]
    obtain ⟨c0, c1, c2⟩ := scaleLin_coord a b p
    rw [c0, c1, c2]
    have e0 : (p 0 / a) ^ 2 ≤ 1 := by
      rw [← sq_abs]; nlinarith [abs_nonneg (p 0 / a)]
    have e1 : (p 1 / b) ^ 2 ≤ 1 := by
      rw [← sq_abs]; nlinarith [abs_nonneg (p 1 / b)]
    have e2 : (p 2) ^ 2 ≤ 1 := by
      rw [← sq_abs]; nlinarith [abs_nonneg (p 2)]
    linarith
  nlinarith [norm_nonneg (scaleLin a b p)]

/-- Level i: `PrismFrostmanEstimate` for the normalized tubes of one prism. -/
theorem level_one {σ ω : ℝ} (hF : PrismFrostmanEstimate σ ω) {e : ℝ} (he : 0 < e) :
    ∃ A : ℝ, 0 < A ∧ ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℝ, 0 < d₀ ∧
    ∀ δ a b : ℝ, 0 < δ → δ ≤ a → a ≤ b → b ≤ 1 → a ≤ 1 / 4 → δ / (5 * b) ≤ d₀ →
    ∀ (c e₁ e₂ e₃ : Space), Orthonormal ℝ ![e₁, e₂, e₃] →
    ∀ (N : ℕ) (x v : Fin N → Space) (Y : Fin N → Set Space),
    0 < N → (∀ i, ‖v i‖ = 1) →
    (∀ i, tube δ (x i) (v i) ⊆ prism a b c e₁ e₂ e₃) →
    (∀ i j, i ≠ j → volume (tube δ (x i) (v i) ∩ tube δ (x j) (v j)) ≤
      (1 / 2 : ENNReal) * volume (tube δ (x i) (v i))) →
    (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ tube δ (x i) (v i)) →
    ENNReal.ofReal ((δ / (5 * b)) ^ η * N * δ ^ 2) ≤ ∑ i, volume (Y i) →
    (∀ U : Set Space, Convex ℝ U →
      ENNReal.ofReal (Set.ncard {i | tube δ (x i) (v i) ⊆ U}) *
          volume (prism a b c e₁ e₂ e₃) ≤
        ENNReal.ofReal ((δ / (5 * b)) ^ (-η) * N) * volume U) →
    ENNReal.ofReal (a * b * (A * (δ / (5 * b)) ^ e * (3 * δ / (5 * a)) ^ ω *
        (N * ((δ / (5 * b)) * (3 * δ / (5 * a))) ^ 2) ^ (σ / 2))) ≤
      volume (⋃ i, Y i) := by
  obtain ⟨A, hA, η, hη, d₀, hd₀, hFe⟩ := hF e he
  refine ⟨A, hA, η, hη, min d₀ ((14400 : ℝ)⁻¹ ^ (1 / η)), lt_min hd₀ (by positivity), ?_⟩
  intro δ a b hδ hδa hab hb1 ha4 hsd c e₁ e₂ e₃ hfr N x v Y hN hv hTW hover hYm hYT hmass
    hfrost
  have ha : 0 < a := hδ.trans_le hδa
  have hb : 0 < b := ha.trans_le hab
  have hs : 0 < δ / (5 * b) := by positivity
  have hst : δ / (5 * b) ≤ 3 * δ / (5 * a) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have ht1 : 3 * δ / (5 * a) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  have hsd₀ : δ / (5 * b) ≤ d₀ := hsd.trans (min_le_left _ _)
  have hsη : (δ / (5 * b)) ^ η ≤ (14400 : ℝ)⁻¹ := by
    have h1 : δ / (5 * b) ≤ (14400 : ℝ)⁻¹ ^ (1 / η) := hsd.trans (min_le_right _ _)
    calc (δ / (5 * b)) ^ η ≤ ((14400 : ℝ)⁻¹ ^ (1 / η)) ^ η :=
          Real.rpow_le_rpow hs.le h1 hη.le
      _ = (14400 : ℝ)⁻¹ := by
          rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hη.ne', Real.rpow_one]
  have h14400 : (14400 : ℝ) ≤ (δ / (5 * b)) ^ (-η) := by
    rw [Real.rpow_neg hs.le, le_inv_comm₀ (by norm_num) (by positivity)]
    exact hsη
  set f := plateMap hfr c a b ha.ne' hb.ne' with hf_def
  have hfvol : ∀ U, volume (f '' U) = ENNReal.ofReal (a * b)⁻¹ * volume U :=
    volume_plateMap_image hfr c ha hb
  -- the plates and their frames
  have hdata : ∀ i, ∃ c' e₁' e₂' e₃' : Space, Orthonormal ℝ ![e₁', e₂', e₃'] ∧
      {y | |inner ℝ e₁' (y - c')| ≤ δ / (5 * b) / 10 ∧
        |inner ℝ e₂' (y - c')| ≤ 3 * δ / (5 * a) / 10 ∧
          |inner ℝ e₃' (y - c')| ≤ 1 / 10} ⊆ f '' tube δ (x i) (v i) ∧
      f '' tube δ (x i) (v i) ⊆
        {y | |inner ℝ e₁' (y - c')| ≤ 10 * (δ / (5 * b)) ∧
          |inner ℝ e₂' (y - c')| ≤ 10 * (3 * δ / (5 * a)) ∧
            |inner ℝ e₃' (y - c')| ≤ 10} := by
    intro i
    have hT' : thickening δ (segment ℝ (frameCoord hfr c (x i))
        (frameCoord hfr c (x i) + (frameCoord hfr c (x i + v i) - frameCoord hfr c (x i)))) ⊆
        stdBox a b := by
      have h := frameCoord_image_tube hfr c δ (x i) (v i)
      simp only [tube] at h
      rw [← h]
      exact (Set.image_mono (hTW i)).trans (frameCoord_image_prism_subset hfr a b c)
    have hv' : ‖frameCoord hfr c (x i + v i) - frameCoord hfr c (x i)‖ = 1 := by
      rw [norm_frameCoord_sub, hv i]
    have hsand := plate_sandwich hδ hδa hab hb1 ha4 hv' hT'
    rw [hf_def, plateMap_image, frameCoord_image_tube]
    exact hsand
  choose c' e₁' e₂' e₃' hframe hin hout using hdata
  have hball : ∀ i, f '' tube δ (x i) (v i) ⊆ ball 0 10 := by
    intro i
    rw [hf_def, plateMap_image]
    exact (Set.image_mono ((Set.image_mono (hTW i)).trans
      (frameCoord_image_prism_subset hfr a b c))).trans (scaleLin_stdBox_subset_ball ha hb)
  have hconv : ∀ i, Convex ℝ (f '' tube δ (x i) (v i)) := by
    intro i
    have h := ((convex_segment (x i) (x i + v i)).thickening δ).affine_image f.toAffineMap
    simpa only [AffineEquiv.coe_toAffineMap] using h
  have hmeasP : ∀ i, MeasurableSet (f '' tube δ (x i) (v i)) := fun i =>
    plateMap_measurableSet hfr c ha.ne' hb.ne' isOpen_thickening.measurableSet
  have hover' : ∀ i j, i ≠ j → volume (f '' tube δ (x i) (v i) ∩ f '' tube δ (x j) (v j)) ≤
      (1 / 2 : ENNReal) * volume (f '' tube δ (x i) (v i)) := fun i j hij =>
    affine_overlap f _ _ hfvol (hover i j hij)
  have hZm : ∀ i, MeasurableSet (f '' Y i) := fun i =>
    plateMap_measurableSet hfr c ha.ne' hb.ne' (hYm i)
  have hZP : ∀ i, f '' Y i ⊆ f '' tube δ (x i) (v i) := fun i => Set.image_mono (hYT i)
  have hmass' : ENNReal.ofReal ((δ / (5 * b)) ^ η * N * (δ / (5 * b)) * (3 * δ / (5 * a))) ≤
      ∑ i, volume (f '' Y i) := by
    simp only [hfvol]
    rw [← Finset.mul_sum]
    calc ENNReal.ofReal ((δ / (5 * b)) ^ η * N * (δ / (5 * b)) * (3 * δ / (5 * a)))
        ≤ ENNReal.ofReal ((a * b)⁻¹ * ((δ / (5 * b)) ^ η * N * δ ^ 2)) := by
          apply ENNReal.ofReal_le_ofReal
          have hst' : (δ / (5 * b)) * (3 * δ / (5 * a)) ≤ (a * b)⁻¹ * δ ^ 2 := by
            rw [div_mul_div_comm, div_le_iff₀ (by positivity)]
            field_simp
            nlinarith [pow_pos hδ 2, mul_pos ha hb]
          have h0 : 0 ≤ (δ / (5 * b)) ^ η * N := by positivity
          calc (δ / (5 * b)) ^ η * N * (δ / (5 * b)) * (3 * δ / (5 * a))
              = ((δ / (5 * b)) ^ η * N) * ((δ / (5 * b)) * (3 * δ / (5 * a))) := by ring
            _ ≤ ((δ / (5 * b)) ^ η * N) * ((a * b)⁻¹ * δ ^ 2) :=
                mul_le_mul_of_nonneg_left hst' h0
            _ = _ := by ring
      _ = ENNReal.ofReal (a * b)⁻¹ * ENNReal.ofReal ((δ / (5 * b)) ^ η * N * δ ^ 2) :=
          ENNReal.ofReal_mul (by positivity)
      _ ≤ _ := by gcongr
  have hfrost' : ∀ U : Set Space, Convex ℝ U →
      ENNReal.ofReal (Set.ncard {i | f '' tube δ (x i) (v i) ⊆ U}) ≤
        ENNReal.ofReal ((δ / (5 * b)) ^ (-η) * N) * volume U := by
    intro U hU
    have h := affine_frostman_count (fun i => tube δ (x i) (v i)) (prism a b c e₁ e₂ e₃) f
      (ENNReal.ofReal (a * b)⁻¹) (ENNReal.ofReal ((δ / (5 * b)) ^ (-η) * N)) hfvol hfrost U hU
    have hP : volume (f '' prism a b c e₁ e₂ e₃) = 8 := by
      rw [hfvol, prism_volume ha.le hb.le c e₁ e₂ e₃ hfr, ← ENNReal.ofReal_mul (by positivity)]
      have : (a * b)⁻¹ * (8 * a * b) = 8 := by field_simp
      rw [this]
      norm_num
    rw [hP] at h
    calc ENNReal.ofReal (Set.ncard {i | f '' tube δ (x i) (v i) ⊆ U})
        ≤ ENNReal.ofReal (Set.ncard {i | f '' tube δ (x i) (v i) ⊆ U}) * 8 :=
          le_mul_of_one_le_right (by simp) (by norm_num)
      _ ≤ _ := h
  have hquad : ∀ U : Set Space, Convex ℝ U →
      ENNReal.ofReal (Set.ncard {i | f '' tube δ (x i) (v i) ⊆ U}) *
          ENNReal.ofReal (((δ / (5 * b)) * (3 * δ / (5 * a))) ^ 2) ≤
        ENNReal.ofReal ((δ / (5 * b)) ^ (-η)) * (volume U) ^ 2 := by
    intro U _
    have hJ : 0 < (a * b)⁻¹ := by positivity
    have h := affine_quadratic_count hδ hJ f hfvol x v hv hover U
    have heq : ((δ / (5 * b)) * (3 * δ / (5 * a))) ^ 2 =
        (9 / 625 : ℝ) * ((a * b)⁻¹ * δ ^ 2) ^ 2 := by
      field_simp
      ring
    rw [heq, ENNReal.ofReal_mul (by norm_num), mul_left_comm]
    calc ENNReal.ofReal (9 / 625) * (ENNReal.ofReal (Set.ncard {i | f '' tube δ (x i) (v i) ⊆ U})
          * ENNReal.ofReal (((a * b)⁻¹ * δ ^ 2) ^ 2))
        ≤ ENNReal.ofReal (9 / 625) * (ENNReal.ofReal 1000000 * (volume U) ^ 2) := by
          gcongr
      _ = ENNReal.ofReal 14400 * (volume U) ^ 2 := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]
          norm_num
      _ ≤ _ := by gcongr
  have key := hFe (δ / (5 * b)) (3 * δ / (5 * a)) hs hst ht1 hsd₀ N
    (fun i => f '' tube δ (x i) (v i)) (fun i => f '' Y i) c' e₁' e₂' e₃' hN hframe hconv
    hmeasP hin hout hball hover' hZm hZP hmass' hfrost' hquad
  rw [← Set.image_iUnion, hfvol] at key
  have hab0 : 0 < a * b := mul_pos ha hb
  calc ENNReal.ofReal (a * b * (A * (δ / (5 * b)) ^ e * (3 * δ / (5 * a)) ^ ω *
        (N * ((δ / (5 * b)) * (3 * δ / (5 * a))) ^ 2) ^ (σ / 2)))
      = ENNReal.ofReal (a * b) * ENNReal.ofReal (A * (δ / (5 * b)) ^ e *
          (3 * δ / (5 * a)) ^ ω * (N * ((δ / (5 * b)) * (3 * δ / (5 * a))) ^ 2) ^ (σ / 2)) :=
        ENNReal.ofReal_mul hab0.le
    _ ≤ ENNReal.ofReal (a * b) * (ENNReal.ofReal (a * b)⁻¹ * volume (⋃ i, Y i)) := by
        gcongr
    _ = volume (⋃ i, Y i) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hab0.le, mul_inv_cancel₀ hab0.ne',
          ENNReal.ofReal_one, one_mul]

end

end WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264
