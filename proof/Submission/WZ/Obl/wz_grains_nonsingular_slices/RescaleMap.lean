-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_grains_nonsingular_slices.RescaleMap.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_grains_nonsingular_slices.Defs

/-!
# The normalizing anisotropic map

`normMap a b m p = (p 0 / 2, b m p 1, (p 2 - a) / (2 b))` and
`normSlope a b m f z = f (a + 2 b z) / (2 b m)`.  The map sends twisted slices to halved
twisted slices of the normalized slope, scales volume by `m / 4`, makes transversal tubes
nearly vertical, and the normalized slope has derivative in `[1, 2]` when `|f'| ∈ [m, 2m]`.
-/

namespace WangZahlLot.Obl.wz_grains_nonsingular_slices

open Set Metric MeasureTheory
open LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_separated_cover_refinement
open scoped ENNReal

/-- The normalizing affine map. -/
noncomputable def normMap (a b m : ℝ) (p : Space) : Space :=
  WithLp.toLp 2 ![p 0 / 2, b * m * p 1, (p 2 - a) / (2 * b)]

/-- The normalized slope. -/
noncomputable def normSlope (a b m : ℝ) (f : ℝ → ℝ) (z : ℝ) : ℝ :=
  f (a + 2 * b * z) / (2 * b * m)

/-! ### The normalized slope -/

private lemma rmap_deriv_affine_comp (f : ℝ → ℝ) (a b z : ℝ) :
    deriv (fun t => f (a + b * t)) z = b * deriv f (a + b * z) := by
  have h := deriv_comp_mul_left b (fun t => f (a + t)) z
  simpa only [smul_eq_mul, deriv_comp_const_add] using h

private lemma rmap_normSlope_deriv {a b m : ℝ} (hb : 0 < b) (f : ℝ → ℝ) :
    deriv (normSlope a b m f) = fun z => deriv f (a + 2 * b * z) / m := by
  funext z
  unfold normSlope
  rw [deriv_div_const, rmap_deriv_affine_comp]
  field_simp

private lemma rmap_normSlope_deriv_deriv {a b m : ℝ} (hb : 0 < b) (f : ℝ → ℝ) (z : ℝ) :
    deriv (deriv (normSlope a b m f)) z = 2 * b * deriv (deriv f) (a + 2 * b * z) / m := by
  rw [rmap_normSlope_deriv hb, deriv_div_const, rmap_deriv_affine_comp]

theorem normSlope_bounds {a b m : ℝ} {f : ℝ → ℝ} (hb : 0 < b) (hm : 0 < m)
    (hbm : 200 * b ≤ m) (hf : ContDiff ℝ 2 f)
    (hderiv : ∀ t ∈ Icc (a - 2 * b) (a + 2 * b),
      m ≤ |deriv f t| ∧ |deriv f t| ≤ 2 * m ∧ |deriv (deriv f) t| ≤ 1) :
    ContDiff ℝ 2 (normSlope a b m f) ∧ ∀ z ∈ Icc (-1 : ℝ) 1,
      1 ≤ |deriv (normSlope a b m f) z| ∧ |deriv (normSlope a b m f) z| ≤ 2 ∧
        |deriv (deriv (normSlope a b m f)) z| ≤ (1 / 100 : ℝ) := by
  refine ⟨?_, ?_⟩
  · unfold normSlope
    exact (hf.comp (contDiff_const.add (contDiff_const.mul contDiff_id))).div_const _
  intro z hz
  have ht : a + 2 * b * z ∈ Icc (a - 2 * b) (a + 2 * b) := by
    constructor <;> nlinarith [hz.1, hz.2]
  obtain ⟨hl, hu, h2⟩ := hderiv _ ht
  rw [rmap_normSlope_deriv_deriv hb, rmap_normSlope_deriv hb]
  simp only [abs_div, abs_mul, abs_of_pos hm, abs_of_pos hb, abs_two]
  refine ⟨?_, ?_, ?_⟩
  · rw [le_div_iff₀ hm]; linarith
  · rw [div_le_iff₀ hm]; linarith
  · rw [div_le_iff₀ hm]
    have : 2 * b * |deriv (deriv f) (a + 2 * b * z)| ≤ 2 * b * 1 :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith

/-! ### Slices and volumes -/

private lemma rmap_normMap_proj {a b m : ℝ} (hb : 0 < b) (hm : 0 < m) (f : ℝ → ℝ)
    (p : Space) :
    normMap a b m p 0 + normSlope a b m f (normMap a b m p 2) * normMap a b m p 1 =
      (p 0 + f (p 2) * p 1) / 2 := by
  have h2 : a + 2 * b * ((p 2 - a) / (2 * b)) = p 2 := by field_simp; ring
  change p 0 / 2 + normSlope a b m f ((p 2 - a) / (2 * b)) * (b * m * p 1) = _
  unfold normSlope
  rw [h2]
  field_simp

theorem PS_normMap {a b m : ℝ} (hb : 0 < b) (hm : 0 < m) (f : ℝ → ℝ) (E : Set Space)
    (z : ℝ) :
    PS (normSlope a b m f) (normMap a b m '' E) z =
      (fun u : ℝ => u / 2) '' PS f E (a + 2 * b * z) := by
  ext u
  constructor
  · rintro ⟨q, ⟨p, hp, rfl⟩, he⟩
    obtain ⟨hu, hz⟩ := Prod.mk.inj he
    rw [rmap_normMap_proj hb hm] at hu
    refine ⟨p 0 + f (p 2) * p 1, ⟨p, hp, Prod.ext rfl ?_⟩, by simp only; linarith⟩
    change (p 2 - a) / (2 * b) = z at hz
    simp only
    rw [← hz]
    field_simp
    ring
  · rintro ⟨y, ⟨p, hp, he⟩, rfl⟩
    obtain ⟨hy, hz⟩ := Prod.mk.inj he
    refine ⟨normMap a b m p, ⟨p, hp, rfl⟩, Prod.ext ?_ ?_⟩
    · simp only at hy ⊢
      rw [rmap_normMap_proj hb hm, hy]
    · simp only at hz ⊢
      change (p 2 - a) / (2 * b) = z
      rw [hz]
      field_simp
      ring

theorem volume_PS_normMap_le {a b m : ℝ} (hb : 0 < b) (hm : 0 < m) (f : ℝ → ℝ)
    (E : Set Space) (z s : ℝ)
    (hs : volume (PS f E (a + 2 * b * z)) ≤ ENNReal.ofReal s) :
    volume (PS (normSlope a b m f) (normMap a b m '' E) z) ≤ ENNReal.ofReal (s / 2) := by
  rw [PS_normMap hb hm]
  have himg : ∀ S : Set ℝ, (fun u : ℝ => u / 2) '' S = (fun u : ℝ => 2 * u) ⁻¹' S := by
    intro S
    ext u
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_div_cancel₀] using hy
    · intro hu
      exact ⟨2 * u, hu, by ring⟩
  rw [himg, Real.volume_preimage_mul_left two_ne_zero]
  calc ENNReal.ofReal |(2 : ℝ)⁻¹| * volume (PS f E (a + 2 * b * z))
      ≤ ENNReal.ofReal |(2 : ℝ)⁻¹| * ENNReal.ofReal s := by gcongr
    _ = ENNReal.ofReal (s / 2) := by
      rw [← ENNReal.ofReal_mul (abs_nonneg _)]
      congr 1
      rw [abs_of_pos (by norm_num)]
      ring

theorem continuous_normMap (a b m : ℝ) : Continuous (normMap a b m) := by
  unfold normMap
  apply (PiLp.continuous_toLp 2 _).comp
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp <;> fun_prop

/-- The linear part of `normMap`, as a conjugated diagonal map. -/
private noncomputable def rmapLin (b m : ℝ) : Space →ₗ[ℝ] Space :=
  ((WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm : (Fin 3 → ℝ) →ₗ[ℝ] Space) ∘ₗ
    Matrix.toLin' (Matrix.diagonal ![1 / 2, b * m, 1 / (2 * b)]) ∘ₗ
      ((WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.symm : Space →ₗ[ℝ] (Fin 3 → ℝ))

private lemma rmapLin_det (b m : ℝ) : LinearMap.det (rmapLin b m) = b * m / (4 * b) := by
  unfold rmapLin
  rw [LinearMap.det_conj, LinearMap.det_toLin', Matrix.det_diagonal, Fin.prod_univ_three]
  simp
  ring

private lemma rmapLin_apply (b m : ℝ) (p : Space) :
    rmapLin b m p = WithLp.toLp 2 ![p 0 / 2, b * m * p 1, p 2 / (2 * b)] := by
  ext i
  fin_cases i <;> simp [rmapLin, Matrix.toLin'_apply, Matrix.mulVec_diagonal] <;> ring

theorem volume_normMap_image {a b m : ℝ} (hb : 0 < b) (hm : 0 < m) (S : Set Space) :
    volume (normMap a b m '' S) = ENNReal.ofReal (m / 4) * volume S := by
  set k : Space := WithLp.toLp 2 ![0, 0, -(a / (2 * b))] with hk
  have hfac : normMap a b m = (fun y => y + k) ∘ rmapLin b m := by
    funext p
    simp only [Function.comp_apply, rmapLin_apply]
    ext i
    fin_cases i
    · simp [normMap, hk]
    · simp [normMap, hk]
    · simp [normMap, hk]
      ring
  rw [hfac, image_comp, image_add_right, measure_preimage_add_right,
    Measure.addHaar_image_linearMap, rmapLin_det]
  congr 2
  rw [abs_of_pos (by positivity)]
  field_simp

/-! ### Coordinates in `Space` -/

private lemma rmap_norm_sq (y : Space) : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]

private lemma rmap_abs_le_norm (y : Space) (i : Fin 3) : |y i| ≤ ‖y‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le y i

private lemma rmap_norm_le_sum (y : Space) : ‖y‖ ≤ |y 0| + |y 1| + |y 2| := by
  have h := rmap_norm_sq y
  have h0 := abs_nonneg (y 0)
  have h1 := abs_nonneg (y 1)
  have h2 := abs_nonneg (y 2)
  rw [← sq_le_sq₀ (norm_nonneg y) (by positivity), h]
  nlinarith [sq_abs (y 0), sq_abs (y 1), sq_abs (y 2), mul_nonneg h0 h1, mul_nonneg h1 h2,
    mul_nonneg h0 h2]

private lemma rmap_norm_vec_le (α β γ : ℝ) :
    ‖(WithLp.toLp 2 ![α, β, γ] : Space)‖ ≤ |α| + |β| + |γ| :=
  rmap_norm_le_sum _

private lemma rmap_norm_vec_sq (α β γ : ℝ) :
    ‖(WithLp.toLp 2 ![α, β, γ] : Space)‖ ^ 2 = α ^ 2 + β ^ 2 + γ ^ 2 :=
  rmap_norm_sq _

/-! ### The new tube -/

/-- The image under the linear part of `normMap` of the old direction `v`, rescaled to have
third coordinate `1`. -/
private noncomputable def rmapHat (b m : ℝ) (v : Space) : Space :=
  WithLp.toLp 2 ![b * v 0 / v 2, 2 * b ^ 2 * m * v 1 / v 2, 1]

/-- The deviation of the image of `c + u` from the new axis. -/
private noncomputable def rmapDev (b m : ℝ) (v u : Space) : Space :=
  WithLp.toLp 2 ![(u 0 - u 2 * v 0 / v 2) / 2, b * m * (u 1 - u 2 * v 1 / v 2), 0]

/-- The image of `P` differs from the point of the new axis at the same height by the
deviation `rmapDev`. -/
private lemma rmap_key {a b m L : ℝ} (hb : b ≠ 0) (hL : L ≠ 0) {v : Space} (hv2 : v 2 ≠ 0)
    (c P : Space) :
    normMap a b m P - (normMap a b m c - (1 / 2 : ℝ) • (L⁻¹ • rmapHat b m v) +
      ((P 2 - c 2) / (2 * b) * L + 1 / 2) • (L⁻¹ • rmapHat b m v)) = rmapDev b m v (P - c) := by
  ext i
  fin_cases i
  · simp [normMap, rmapHat, rmapDev]
    field_simp
    ring
  · simp [normMap, rmapHat, rmapDev]
    field_simp
    ring
  · simp [normMap, rmapHat, rmapDev]
    field_simp
    ring

private lemma rmap_dev_le {b m θ ε σ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hbm0 : 0 ≤ b * m)
    (hbm : b * m ≤ 1 / 4) {v e : Space} (hv : ‖v‖ = 1) (hv2 : θ ≤ |v 2|) (he : ‖e‖ ≤ ε) :
    ‖rmapDev b m v (σ • v + e)‖ ≤ 3 / 2 * ε / θ := by
  have hv2pos : 0 < |v 2| := lt_of_lt_of_le hθ hv2
  have hv2ne : v 2 ≠ 0 := abs_pos.mp hv2pos
  have hε : 0 ≤ ε := (norm_nonneg e).trans he
  have hv0 : |v 0| ≤ 1 := (rmap_abs_le_norm v 0).trans hv.le
  have hv1 : |v 1| ≤ 1 := (rmap_abs_le_norm v 1).trans hv.le
  have he0 : |e 0| ≤ ε := (rmap_abs_le_norm e 0).trans he
  have he1 : |e 1| ≤ ε := (rmap_abs_le_norm e 1).trans he
  have he2 : |e 2| ≤ ε := (rmap_abs_le_norm e 2).trans he
  have hq : ∀ i : Fin 3, |v i| ≤ 1 → |e 2 * v i / v 2| ≤ ε / θ := by
    intro i hvi
    rw [abs_div, abs_mul, div_le_div_iff₀ hv2pos hθ]
    calc |e 2| * |v i| * θ ≤ ε * 1 * θ := by gcongr
      _ ≤ ε * |v 2| := by rw [mul_one]; exact mul_le_mul_of_nonneg_left hv2 hε
  have hεθ : ε ≤ ε / θ := by
    rw [le_div_iff₀ hθ]
    nlinarith
  have hd0 : (σ • v + e) 0 - (σ • v + e) 2 * v 0 / v 2 = e 0 - e 2 * v 0 / v 2 := by
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp
    ring
  have hd1 : (σ • v + e) 1 - (σ • v + e) 2 * v 1 / v 2 = e 1 - e 2 * v 1 / v 2 := by
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp
    ring
  have hD : rmapDev b m v (σ • v + e) =
      WithLp.toLp 2 ![(e 0 - e 2 * v 0 / v 2) / 2, b * m * (e 1 - e 2 * v 1 / v 2), 0] := by
    unfold rmapDev
    rw [hd0, hd1]
  rw [hD]
  have h0 : |(e 0 - e 2 * v 0 / v 2)| ≤ ε + ε / θ :=
    (abs_sub _ _).trans (add_le_add he0 (hq 0 hv0))
  have h1 : |(e 1 - e 2 * v 1 / v 2)| ≤ ε + ε / θ :=
    (abs_sub _ _).trans (add_le_add he1 (hq 1 hv1))
  refine (rmap_norm_vec_le _ _ _).trans ?_
  rw [abs_div, abs_two, abs_mul, abs_of_nonneg hbm0, abs_zero, add_zero]
  have h1' := mul_le_mul hbm h1 (abs_nonneg _) (by norm_num)
  have hr : 3 / 2 * ε / θ = 3 / 2 * (ε / θ) := by ring
  rw [hr]
  linarith

/-- A point of a segment, parametrized from its midpoint. -/
private lemma rmap_mem_segment (x' w : Space) {t : ℝ} (ht : |t| ≤ 1 / 2) :
    x' + (t + 1 / 2) • w ∈ segment ℝ x' (x' + w) := by
  rw [segment_eq_image']
  refine ⟨t + 1 / 2, ⟨by linarith [(abs_le.mp ht).1], by linarith [(abs_le.mp ht).2]⟩, ?_⟩
  simp only [add_sub_cancel_left]

/-- The image of a point `P = c + σ v + e` lies close to the new axis, provided its height
parameter is in range. -/
private lemma rmap_near_axis {a b m L θ ε σ : ℝ} (hb : 0 < b) (hLpos : 0 < L) (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (hbm0 : 0 ≤ b * m) (hbm : b * m ≤ 1 / 4) {v c P e : Space} (hv : ‖v‖ = 1)
    (hv2 : θ ≤ |v 2|) (hPc : P - c = σ • v + e) (he : ‖e‖ ≤ ε)
    (ht : |(P 2 - c 2) / (2 * b) * L| ≤ 1 / 2) :
    ∃ y ∈ segment ℝ (normMap a b m c - (1 / 2 : ℝ) • (L⁻¹ • rmapHat b m v))
        (normMap a b m c - (1 / 2 : ℝ) • (L⁻¹ • rmapHat b m v) + L⁻¹ • rmapHat b m v),
      dist (normMap a b m P) y ≤ 3 / 2 * ε / θ := by
  have hv2ne : v 2 ≠ 0 := abs_pos.mp (lt_of_lt_of_le hθ hv2)
  refine ⟨_, rmap_mem_segment _ _ ht, ?_⟩
  rw [dist_eq_norm, rmap_key hb.ne' hLpos.ne' hv2ne c P, hPc]
  exact rmap_dev_le hθ hθ1 hbm0 hbm hv hv2 he

/-- The new tube, centered at the image of a point of height `a` and with a nearly vertical
direction, stays in the unit ball. -/
private lemma rmap_tube_ball {a b m r : ℝ} {c w : Space} (hbm0 : 0 ≤ b * m)
    (hbm : b * m ≤ 1 / 4) (hc2 : c 2 = a) (hcn : ‖c‖ < 113 / 100) (hw0 : |w 0| ≤ 1 / 4)
    (hw1 : |w 1| ≤ 1 / 8) (hw2 : |w 2| ≤ 1) (hr : r ≤ 1 / 100) :
    thickening r (segment ℝ (normMap a b m c - (1 / 2 : ℝ) • w)
      (normMap a b m c - (1 / 2 : ℝ) • w + w)) ⊆ ball 0 1 := by
  intro y hy
  obtain ⟨z, hz, hyz⟩ := mem_thickening_iff.mp hy
  rw [segment_eq_image'] at hz
  obtain ⟨s, hs, rfl⟩ := hz
  rw [mem_ball_zero_iff]
  simp only [add_sub_cancel_left] at hyz ⊢
  have hts : |s - 1 / 2| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith [hs.1, hs.2]
  set z := normMap a b m c - (1 / 2 : ℝ) • w + s • w with hz
  have hz0e : z 0 = c 0 / 2 + (s - 1 / 2) * w 0 := by
    simp only [z, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, normMap]
    simp
    ring
  have hz1e : z 1 = b * m * c 1 + (s - 1 / 2) * w 1 := by
    simp only [z, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, normMap]
    simp
    ring
  have hz2e : z 2 = (s - 1 / 2) * w 2 := by
    simp only [z, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, normMap]
    simp [hc2]
    ring
  have hc0 : |c 0| ≤ 113 / 100 := (rmap_abs_le_norm c 0).trans hcn.le
  have hc1 : |c 1| ≤ 113 / 100 := (rmap_abs_le_norm c 1).trans hcn.le
  have hcsq : c 0 ^ 2 + c 1 ^ 2 + c 2 ^ 2 ≤ (113 / 100) ^ 2 := by
    rw [← rmap_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) hcn.le 2
  have hz0 : |z 0| ≤ |c 0| / 2 + 1 / 8 := by
    rw [hz0e]
    calc |c 0 / 2 + (s - 1 / 2) * w 0| ≤ |c 0 / 2| + |(s - 1 / 2) * w 0| := abs_add_le _ _
      _ ≤ |c 0| / 2 + 1 / 2 * (1 / 4) := by
        rw [abs_div, abs_two, abs_mul]
        gcongr
      _ = |c 0| / 2 + 1 / 8 := by ring
  have hz1 : |z 1| ≤ |c 1| / 4 + 1 / 16 := by
    rw [hz1e]
    calc |b * m * c 1 + (s - 1 / 2) * w 1| ≤ |b * m * c 1| + |(s - 1 / 2) * w 1| :=
          abs_add_le _ _
      _ ≤ 1 / 4 * |c 1| + 1 / 2 * (1 / 8) := by
        rw [abs_mul (b * m), abs_mul (s - 1 / 2), abs_of_nonneg hbm0]
        gcongr
      _ = |c 1| / 4 + 1 / 16 := by ring
  have hz2 : |z 2| ≤ 1 / 2 := by
    rw [hz2e, abs_mul]
    calc |s - 1 / 2| * |w 2| ≤ 1 / 2 * 1 := by gcongr
      _ = 1 / 2 := by ring
  have hzsq : ‖z‖ ^ 2 ≤ 9 / 10 := by
    rw [rmap_norm_sq]
    have e0 : z 0 ^ 2 ≤ (|c 0| / 2 + 1 / 8) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hz0 2
    have e1 : z 1 ^ 2 ≤ (|c 1| / 4 + 1 / 16) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hz1 2
    have e2 : z 2 ^ 2 ≤ (1 / 2) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hz2 2
    have E : (|c 0| / 2 + 1 / 8) ^ 2 + (|c 1| / 4 + 1 / 16) ^ 2 =
        |c 0| ^ 2 / 4 + |c 1| ^ 2 / 16 + |c 0| / 8 + |c 1| / 32 + (1 / 64 + 1 / 256) := by ring
    rw [sq_abs, sq_abs] at E
    have hc2sq := sq_nonneg (c 2)
    have hc1sq := sq_nonneg (c 1)
    have hc0sq := sq_nonneg (c 0)
    norm_num at e2 hcsq
    linarith
  have hzn : ‖z‖ < 19 / 20 := lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by linarith)
  calc ‖y‖ ≤ ‖z‖ + ‖y - z‖ := norm_le_insert' _ _
    _ < 1 := by rw [← dist_eq_norm]; linarith

/-- The new tube attached to a transversal tube meeting the central slab. The last clause says
that contracting the whole old tube by the factor `b / 2` towards a point `c` of its axis lands
inside the preimage of the new tube. -/
theorem rescale_tube {δ θ a b m : ℝ} (hδ : 0 < δ) (hb : 0 < b) (hm : 0 < m) (hm1 : m ≤ 1)
    (hbθ : 4 * b ≤ θ) (hθ1 : θ ≤ 1) (hδb : 100 * δ ≤ b) (hδθ : 400 * δ ≤ θ) (ha : |a| ≤ 1)
    {x v : Space} (hv : ‖v‖ = 1) (hv2 : θ ≤ |v 2|) (hT : Tube δ x v ⊆ ball 0 1)
    (hmeet : (Tube δ x v ∩ {q | |q 2 - a| ≤ b / 2}).Nonempty) :
    ∃ (x' w c : Space), ‖w‖ = 1 ∧ (1 / 2 : ℝ) ≤ |w 2| ∧ ‖c‖ ≤ 3 / 2 ∧
      Tube (4 * δ / θ) x' w ⊆ ball 0 1 ∧
      normMap a b m '' (Tube δ x v ∩ {q | |q 2 - a| ≤ b / 2}) ⊆
        cthickening (2 * δ / θ) (segment ℝ x' (x' + w)) ∧
      ∀ p ∈ Tube δ x v, c + (b / 2) • (p - c) ∈ normMap a b m ⁻¹' Tube (4 * δ / θ) x' w := by
  have hθ : 0 < θ := by linarith
  have hb4 : b ≤ 1 / 4 := by linarith
  have hbm0 : 0 ≤ b * m := by positivity
  have hbm : b * m ≤ 1 / 4 := by
    have := mul_le_mul_of_nonneg_left hm1 hb.le
    linarith
  have hv2pos : 0 < |v 2| := lt_of_lt_of_le hθ hv2
  have hv2ne : v 2 ≠ 0 := abs_pos.mp hv2pos
  have hv0 : |v 0| ≤ 1 := (rmap_abs_le_norm v 0).trans hv.le
  have hv1 : |v 1| ≤ 1 := (rmap_abs_le_norm v 1).trans hv.le
  have hδ1 : δ ≤ 1 / 400 := by linarith
  -- the new direction `w = L⁻¹ • rmapHat b m v`
  have hh0 : |b * v 0 / v 2| ≤ 1 / 4 := by
    rw [abs_div, abs_mul, abs_of_pos hb, div_le_iff₀ hv2pos]
    have : b * |v 0| ≤ b := mul_le_of_le_one_right hb.le hv0
    linarith
  have hh1 : |2 * b ^ 2 * m * v 1 / v 2| ≤ 1 / 8 := by
    rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * b ^ 2 * m),
      div_le_iff₀ hv2pos]
    have h1 : 2 * b ^ 2 * m * |v 1| ≤ 2 * b ^ 2 * m := mul_le_of_le_one_right (by positivity) hv1
    have h2 : 2 * b ^ 2 * m ≤ b / 2 := by nlinarith
    linarith
  obtain ⟨L, hL⟩ : ∃ L, L = ‖rmapHat b m v‖ := ⟨_, rfl⟩
  have hL2 : L ^ 2 = (b * v 0 / v 2) ^ 2 + (2 * b ^ 2 * m * v 1 / v 2) ^ 2 + 1 := by
    rw [hL, rmapHat, rmap_norm_vec_sq, one_pow]
  have hLnn : 0 ≤ L := hL ▸ norm_nonneg _
  have hL1 : 1 ≤ L := by
    refine le_of_pow_le_pow_left₀ two_ne_zero hLnn ?_
    rw [one_pow, hL2]
    nlinarith [sq_nonneg (b * v 0 / v 2), sq_nonneg (2 * b ^ 2 * m * v 1 / v 2)]
  have hL32 : L ≤ 3 / 2 := by
    have e0 : (b * v 0 / v 2) ^ 2 ≤ (1 / 4) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hh0 2
    have e1 : (2 * b ^ 2 * m * v 1 / v 2) ^ 2 ≤ (1 / 8) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hh1 2
    refine le_of_pow_le_pow_left₀ two_ne_zero (by norm_num) ?_
    rw [hL2]
    norm_num at e0 e1 ⊢
    linarith
  have hLpos : 0 < L := by linarith
  have hLinv : L⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hL1
  have hLinv0 : 0 < L⁻¹ := inv_pos.mpr hLpos
  have hw0 : |(L⁻¹ • rmapHat b m v) 0| ≤ 1 / 4 := by
    have : (L⁻¹ • rmapHat b m v) 0 = L⁻¹ * (b * v 0 / v 2) := by simp [rmapHat]
    rw [this, abs_mul, abs_of_pos hLinv0]
    calc L⁻¹ * |b * v 0 / v 2| ≤ 1 * (1 / 4) :=
          mul_le_mul hLinv hh0 (abs_nonneg _) zero_le_one
      _ = 1 / 4 := by ring
  have hw1 : |(L⁻¹ • rmapHat b m v) 1| ≤ 1 / 8 := by
    have : (L⁻¹ • rmapHat b m v) 1 = L⁻¹ * (2 * b ^ 2 * m * v 1 / v 2) := by simp [rmapHat]
    rw [this, abs_mul, abs_of_pos hLinv0]
    calc L⁻¹ * |2 * b ^ 2 * m * v 1 / v 2| ≤ 1 * (1 / 8) :=
          mul_le_mul hLinv hh1 (abs_nonneg _) zero_le_one
      _ = 1 / 8 := by ring
  have hw2e : (L⁻¹ • rmapHat b m v) 2 = L⁻¹ := by simp [rmapHat]
  -- the center: the point of height `a` on the axis line of the old tube
  obtain ⟨τc, hτc⟩ : ∃ τc : ℝ, τc = (a - x 2) / v 2 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : Space, c = x + τc • v := ⟨_, rfl⟩
  have hc2 : c 2 = a := by
    rw [hc, hτc]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp
    ring
  -- a point of the old tube in the central slab
  obtain ⟨q, hqT, hqs⟩ := hmeet
  obtain ⟨τq, hτq, hqe⟩ := WangZahlLot.Obl.wz_balanced_cluster_cover.exists_param_of_mem_tube hqT
  have hqn : ‖q‖ < 1 := mem_ball_zero_iff.mp (hT hqT)
  have hqs' : |q 2 - a| ≤ b / 2 := hqs
  have hτcq : |τc - τq| ≤ 51 / 400 := by
    have key : (τc - τq) * v 2 = a - q 2 + (q - (x + τq • v)) 2 := by
      rw [hτc]
      simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      field_simp
      ring
    have h2 : |(q - (x + τq • v)) 2| ≤ δ := (rmap_abs_le_norm _ 2).trans hqe.le
    have h3 : |τc - τq| * |v 2| ≤ b / 2 + δ := by
      rw [← abs_mul, key]
      calc |a - q 2 + (q - (x + τq • v)) 2| ≤ |a - q 2| + |(q - (x + τq • v)) 2| :=
            abs_add_le _ _
        _ ≤ b / 2 + δ := by rw [abs_sub_comm]; linarith
    have h4 : |τc - τq| * θ ≤ b / 2 + δ :=
      le_trans (mul_le_mul_of_nonneg_left hv2 (abs_nonneg _)) h3
    exact le_of_mul_le_mul_right (by linarith : |τc - τq| * θ ≤ 51 / 400 * θ) hθ
  have hcn : ‖c‖ < 113 / 100 := by
    have hcq : c = q + (τc - τq) • v - (q - (x + τq • v)) := by
      rw [hc]
      module
    rw [hcq]
    calc ‖q + (τc - τq) • v - (q - (x + τq • v))‖
        ≤ ‖q + (τc - τq) • v‖ + ‖q - (x + τq • v)‖ := norm_sub_le _ _
      _ ≤ ‖q‖ + ‖(τc - τq) • v‖ + ‖q - (x + τq • v)‖ := by gcongr; exact norm_add_le _ _
      _ < 113 / 100 := by
        rw [norm_smul, hv, Real.norm_eq_abs, mul_one]
        linarith
  have hτrange : ∀ τ ∈ Icc (0 : ℝ) 1, |τ - τc| ≤ 1 + 51 / 400 := by
    intro τ hτ
    calc |τ - τc| ≤ |τ - τq| + |τq - τc| := abs_sub_le _ _ _
      _ ≤ 1 + 51 / 400 := by
        rw [abs_sub_comm τq τc]
        have : |τ - τq| ≤ 1 := by
          rw [abs_le]
          constructor <;> linarith [hτ.1, hτ.2, hτq.1, hτq.2]
        linarith
  have hpc : ∀ p ∈ Tube δ x v, ∃ τ : ℝ, p - c = (τ - τc) • v + (p - (x + τ • v)) ∧
      ‖p - (x + τ • v)‖ < δ ∧ |p 2 - a| < 113 / 100 := by
    intro p hpT
    obtain ⟨τ, hτ, hpe⟩ := WangZahlLot.Obl.wz_balanced_cluster_cover.exists_param_of_mem_tube hpT
    have hu : p - c = (τ - τc) • v + (p - (x + τ • v)) := by
      rw [hc]
      module
    refine ⟨τ, hu, hpe, ?_⟩
    have h1 : |(p - c) 2| ≤ ‖p - c‖ := rmap_abs_le_norm _ 2
    rw [PiLp.sub_apply, hc2] at h1
    have h2 : ‖p - c‖ < 113 / 100 := by
      rw [hu]
      calc ‖(τ - τc) • v + (p - (x + τ • v))‖
          ≤ ‖(τ - τc) • v‖ + ‖p - (x + τ • v)‖ := norm_add_le _ _
        _ < 113 / 100 := by
          rw [norm_smul, hv, Real.norm_eq_abs, mul_one]
          have := hτrange τ hτ
          linarith
    linarith
  have h2b : (0 : ℝ) < 2 * b := by positivity
  refine ⟨normMap a b m c - (1 / 2 : ℝ) • (L⁻¹ • rmapHat b m v), L⁻¹ • rmapHat b m v, c,
    ?_, ?_, by linarith, ?_, ?_, ?_⟩
  · -- the new direction is a unit vector
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hLpos, ← hL]
    exact inv_mul_cancel₀ hLpos.ne'
  · -- the new direction is nearly vertical
    rw [hw2e, abs_of_pos hLinv0]
    have := inv_anti₀ hLpos hL32
    norm_num at this
    linarith
  · -- the new tube lies in the unit ball
    have h4 : 4 * δ / θ ≤ 1 / 100 := by
      rw [div_le_iff₀ hθ]
      calc 4 * δ = 400 * δ / 100 := by ring
        _ ≤ θ / 100 := div_le_div_of_nonneg_right hδθ (by norm_num)
        _ = 1 / 100 * θ := by ring
    have hw2 : |(L⁻¹ • rmapHat b m v) 2| ≤ 1 := by rw [hw2e, abs_of_pos hLinv0]; exact hLinv
    exact rmap_tube_ball hbm0 hbm hc2 hcn hw0 hw1 hw2 h4
  · -- the central part of the old tube goes close to the new axis
    rintro _ ⟨p, ⟨hpT, hps⟩, rfl⟩
    have hps' : |p 2 - a| ≤ b / 2 := hps
    obtain ⟨τ, hu, hpe, -⟩ := hpc p hpT
    have htb : |(p 2 - c 2) / (2 * b) * L| ≤ 1 / 2 := by
      have : (p 2 - c 2) / (2 * b) * L = (p 2 - a) * L / (2 * b) := by rw [hc2]; ring
      rw [this, abs_div, abs_mul, abs_of_pos hLpos, abs_of_pos h2b, div_le_iff₀ h2b]
      have := mul_le_mul hps' hL32 hLnn (by positivity)
      linarith
    obtain ⟨y, hy, hd⟩ := rmap_near_axis (a := a) hb hLpos hθ hθ1 hbm0 hbm hv hv2 hu hpe.le htb
    refine mem_cthickening_of_dist_le _ y _ _ hy (hd.trans ?_)
    rw [div_le_div_iff_of_pos_right hθ]
    linarith
  · -- the contraction of the old tube towards `c` goes into the new tube
    intro p hpT
    obtain ⟨τ, hu, hpe, hpa⟩ := hpc p hpT
    have hu' : c + (b / 2) • (p - c) - c =
        (b / 2 * (τ - τc)) • v + (b / 2) • (p - (x + τ • v)) := by
      rw [add_sub_cancel_left, hu]
      module
    have he' : ‖(b / 2) • (p - (x + τ • v))‖ ≤ b / 2 * δ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      exact mul_le_mul_of_nonneg_left hpe.le (by positivity)
    have hP2 : (c + (b / 2) • (p - c)) 2 - c 2 = b / 2 * (p 2 - a) := by
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, hc2]
      ring
    have htb : |((c + (b / 2) • (p - c)) 2 - c 2) / (2 * b) * L| ≤ 1 / 2 := by
      have : ((c + (b / 2) • (p - c)) 2 - c 2) / (2 * b) * L = (p 2 - a) * L / 4 := by
        rw [hP2]
        field_simp
        ring
      rw [this, abs_div, abs_mul, abs_of_pos hLpos, abs_of_pos (by norm_num : (0 : ℝ) < 4),
        div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
      have := mul_le_mul hpa.le hL32 hLnn (by norm_num)
      linarith
    obtain ⟨y, hy, hd⟩ := rmap_near_axis (a := a) hb hLpos hθ hθ1 hbm0 hbm hv hv2 hu' he' htb
    rw [mem_preimage, Tube, mem_thickening_iff]
    refine ⟨y, hy, lt_of_le_of_lt hd ?_⟩
    rw [div_lt_div_iff_of_pos_right hθ]
    have := mul_le_mul_of_nonneg_right hb4 hδ.le
    linarith

end WangZahlLot.Obl.wz_grains_nonsingular_slices
