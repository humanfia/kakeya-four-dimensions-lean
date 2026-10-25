-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_c2_slope_normalization.ZoomRotate.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_c2_slope_normalization.ZoomGrains

/-!
# Rotations about the vertical axis

The rotation `rotZ θ` fixes every horizontal plane.  A family with slope `h` becomes a family
with slope `(h cos θ + sin θ) / (cos θ - h sin θ)`, and each twisted slice is dilated by
`cos θ + G sin θ`, where `G` is the new slope.  A dilation by a factor at most two costs a
factor two in the covering constant.
-/

namespace WangZahlLot.Obl.wz_c2_slope_normalization

open Set Metric MeasureTheory
open scoped ENNReal RealInnerProductSpace

noncomputable section

/-- A dilation by a factor in `[1, 2]` keeps the minimum scale and doubles the constant. -/
theorem Assouad.dilate_image {d α C l : ℝ} {B : Set ℝ} (hd : 0 < d) (hα : 0 ≤ α)
    (hC : 1 / 2 ≤ C) (hl1 : 1 ≤ l) (hl2 : l ≤ 2) (h : Assouad d α C B) :
    Assouad d α (2 * C) ((fun x => l * x) '' B) := by
  intro r R a hdr hrR
  have hl0 : 0 < l := by linarith
  have hr : 0 < r := hd.trans_le hdr
  have hRr : 1 ≤ R / r := by rw [le_div_iff₀ hr]; linarith
  have hpow1 : 1 ≤ (R / r) ^ α := Real.one_le_rpow hRr hα
  by_cases hcase : l * d ≤ r
  · obtain ⟨m, c, hc, hm⟩ := h (r / l) (R / l) (a / l)
      ((le_div_iff₀ hl0).mpr (by linarith)) (div_le_div_of_nonneg_right hrR hl0.le)
    refine ⟨m, fun j => l * c j, ?_, ?_⟩
    · rintro _ ⟨⟨u, hu, rfl⟩, hlo, hhi⟩
      have huI : u ∈ Icc (a / l) (a / l + R / l) := by
        constructor
        · rw [div_le_iff₀ hl0]; linarith
        · rw [← add_div, le_div_iff₀ hl0]; linarith
      obtain ⟨j, hj⟩ := mem_iUnion.mp (hc ⟨hu, huI⟩)
      refine mem_iUnion.mpr ⟨j, ?_⟩
      rw [mem_closedBall, Real.dist_eq] at hj ⊢
      rw [← mul_sub, abs_mul, abs_of_pos hl0]
      calc l * |u - c j| ≤ l * (r / l) := mul_le_mul_of_nonneg_left hj hl0.le
        _ = r := by field_simp
    · have he : R / l / (r / l) = R / r := by field_simp
      rw [he] at hm
      have hC0 : 0 ≤ C := by linarith
      nlinarith [mul_le_mul_of_nonneg_right (show C ≤ 2 * C by linarith)
        (Real.rpow_nonneg (div_nonneg (hr.le.trans hrR) hr.le) α)]
  · replace hcase := not_le.mp hcase
    by_cases hR : d ≤ R / l
    · obtain ⟨m, c, hc, hm⟩ := h d (R / l) (a / l) le_rfl hR
      refine ⟨m + m, Fin.append (fun j => l * (c j - d / 2)) (fun j => l * (c j + d / 2)),
        ?_, ?_⟩
      · rintro _ ⟨⟨u, hu, rfl⟩, hlo, hhi⟩
        have huI : u ∈ Icc (a / l) (a / l + R / l) := by
          constructor
          · rw [div_le_iff₀ hl0]; linarith
          · rw [← add_div, le_div_iff₀ hl0]; linarith
        obtain ⟨j, hj⟩ := mem_iUnion.mp (hc ⟨hu, huI⟩)
        rw [mem_closedBall, Real.dist_eq] at hj
        have hld : l * (d / 2) ≤ r := by nlinarith
        rcases le_total u (c j) with hu' | hu'
        · refine mem_iUnion.mpr ⟨Fin.castAdd m j, ?_⟩
          rw [Fin.append_left, mem_closedBall, Real.dist_eq]
          have : |u - (c j - d / 2)| ≤ d / 2 := by
            rw [abs_le]; constructor <;> linarith [(abs_le.mp hj).1]
          rw [← mul_sub, abs_mul, abs_of_pos hl0]
          nlinarith
        · refine mem_iUnion.mpr ⟨Fin.natAdd m j, ?_⟩
          rw [Fin.append_right, mem_closedBall, Real.dist_eq]
          have : |u - (c j + d / 2)| ≤ d / 2 := by
            rw [abs_le]; constructor <;> linarith [(abs_le.mp hj).2]
          rw [← mul_sub, abs_mul, abs_of_pos hl0]
          nlinarith
      · have hmono : (R / l / d) ^ α ≤ (R / r) ^ α := by
          apply Real.rpow_le_rpow
            (div_nonneg (div_nonneg (hr.le.trans hrR) hl0.le) hd.le)
          · rw [div_div, div_le_div_iff₀ (by positivity) hr]
            nlinarith [hd.le.trans hdr]
          · exact hα
        push_cast
        nlinarith
    · replace hR := not_le.mp hR
      refine ⟨1, fun _ => a + R / 2, ?_, ?_⟩
      · rintro u ⟨-, hlo, hhi⟩
        refine mem_iUnion.mpr ⟨0, ?_⟩
        rw [mem_closedBall, Real.dist_eq, abs_le]
        have hR2 : R / 2 ≤ r := by
          have : R < l * d := by rwa [div_lt_iff₀ hl0, mul_comm] at hR
          nlinarith
        constructor <;> linarith
      · push_cast
        nlinarith

/-- The coordinate formula of the rotation about the vertical axis. -/
def rotZfun (θ : ℝ) (p : Space) : Space :=
  WithLp.toLp 2 ![Real.cos θ * p 0 - Real.sin θ * p 1, Real.sin θ * p 0 + Real.cos θ * p 1, p 2]

theorem rotZfun_zero (θ : ℝ) (p : Space) :
    rotZfun θ p 0 = Real.cos θ * p 0 - Real.sin θ * p 1 := rfl

theorem rotZfun_one (θ : ℝ) (p : Space) :
    rotZfun θ p 1 = Real.sin θ * p 0 + Real.cos θ * p 1 := rfl

theorem rotZfun_two (θ : ℝ) (p : Space) : rotZfun θ p 2 = p 2 := rfl

theorem rotZfun_neg (θ : ℝ) (p : Space) : rotZfun (-θ) (rotZfun θ p) = p := by
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, rotZfun_zero, rotZfun_one, Real.cos_neg,
      Real.sin_neg]
    linear_combination p 0 * Real.sin_sq_add_cos_sq θ
  · simp only [Fin.mk_one, Fin.isValue, rotZfun_zero, rotZfun_one, Real.cos_neg, Real.sin_neg]
    linear_combination p 1 * Real.sin_sq_add_cos_sq θ
  · rfl

theorem rotZfun_neg' (θ : ℝ) (p : Space) : rotZfun θ (rotZfun (-θ) p) = p := by
  have := rotZfun_neg (-θ) p
  rwa [neg_neg] at this

theorem norm_rotZfun (θ : ℝ) (p : Space) : ‖rotZfun θ p‖ = ‖p‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, rotZfun_zero, rotZfun_one,
    rotZfun_two]
  linear_combination (p 0 ^ 2 + p 1 ^ 2) * Real.sin_sq_add_cos_sq θ

/-- The rotation about the vertical axis, as a linear isometry equivalence. -/
def rotZ (θ : ℝ) : Space ≃ₗᵢ[ℝ] Space where
  toFun := rotZfun θ
  invFun := rotZfun (-θ)
  map_add' p q := by
    ext i; fin_cases i <;> simp [rotZfun] <;> ring
  map_smul' a p := by
    ext i; fin_cases i <;> simp [rotZfun] <;> ring
  left_inv := rotZfun_neg θ
  right_inv := rotZfun_neg' θ
  norm_map' := norm_rotZfun θ

theorem rotZ_apply (θ : ℝ) (p : Space) : rotZ θ p = rotZfun θ p := rfl

/-- A rotation about the vertical axis maps twisted slices to dilated twisted slices. -/
theorem projectedSlice_rotZ {θ z G H : ℝ} {g h : ℝ → ℝ} (E : Set Space)
    (hg : g z = G) (hh : h z = H)
    (hG : G * Real.cos θ - Real.sin θ = H * (Real.cos θ + G * Real.sin θ)) :
    ProjectedSlice g (rotZ θ '' E) z =
      (fun u => (Real.cos θ + G * Real.sin θ) * u) '' ProjectedSlice h E z := by
  ext u
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, he⟩
    obtain ⟨hu, hz⟩ := Prod.mk.inj he
    simp only [rotZ_apply, rotZfun_two] at hz
    refine ⟨p 0 + h (p 2) * p 1, ⟨p, hp, by simp only [hz]⟩, ?_⟩
    simp only [rotZ_apply, rotZfun_zero, rotZfun_one, rotZfun_two, hz, hg, hh] at hu ⊢
    rw [← hu]
    linear_combination -(p 1 * hG)
  · rintro ⟨w, ⟨p, hp, he⟩, rfl⟩
    obtain ⟨hw, hz⟩ := Prod.mk.inj he
    refine ⟨rotZ θ p, ⟨p, hp, rfl⟩, ?_⟩
    apply Prod.ext
    · simp only [rotZ_apply, rotZfun_zero, rotZfun_one, rotZfun_two, hz, hg]
      simp only [hz, hh] at hw
      rw [← hw]
      linear_combination p 1 * hG
    · simp only [rotZ_apply, rotZfun_two, hz]

end

end WangZahlLot.Obl.wz_c2_slope_normalization
