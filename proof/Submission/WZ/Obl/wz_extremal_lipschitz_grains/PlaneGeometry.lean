-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.PlaneGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.WeakPlaneMap

/-!
# Geometry for the Lipschitz plane map

`near_normal_of_two`: a unit vector almost orthogonal to two unit directions with
`s ≤ ‖a × b‖` is within `4 e / s` (up to sign) of the normalized cross product.  This is the
step of sticky Lemma 4.5 where a plane map is pinned down by two transverse coarse tubes.
-/

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal

/-- Vector triple product `V × (a × b) = ⟪V, b⟫ a - ⟪V, a⟫ b`. -/
theorem cross_cross_eq (V a b : Space) :
    cross V (cross a b) = inner ℝ V b • a - inner ℝ V a • b := by
  simp only [cross, WithLp.ofLp_toLp, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  ext k
  simp only [PiLp.toLp_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  simp only [crossProduct, LinearMap.mk₂_apply, dotProduct, Fin.sum_univ_three]
  fin_cases k <;> simp <;> ring

/-- A unit vector almost orthogonal to two unit vectors spanning a definite angle is close, up to
sign, to their normalized cross product. -/
theorem near_normal_of_two {a b V : Space} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hV : ‖V‖ = 1)
    {s e : ℝ} (hs : 0 < s) (hab : s ≤ ‖cross a b‖) (hVa : |inner ℝ V a| ≤ e)
    (hVb : |inner ℝ V b| ≤ e) :
    min ‖V - ‖cross a b‖⁻¹ • cross a b‖ ‖V + ‖cross a b‖⁻¹ • cross a b‖ ≤ 4 * e / s := by
  set c := cross a b with hc
  have hc0 : 0 < ‖c‖ := lt_of_lt_of_le hs hab
  set N := ‖c‖⁻¹ • c with hN
  have hNn : ‖N‖ = 1 := norm_smul_inv_norm (norm_pos_iff.1 hc0)
  have he : 0 ≤ e := (abs_nonneg _).trans hVa
  -- Lagrange identity for `V` and `c`
  have hlag := cross_norm_sq V c
  rw [hV, one_pow, one_mul, cross_cross_eq] at hlag
  have hsmall : ‖inner ℝ V b • a - inner ℝ V a • b‖ ≤ 2 * e := by
    calc ‖inner ℝ V b • a - inner ℝ V a • b‖ ≤ ‖inner ℝ V b • a‖ + ‖inner ℝ V a • b‖ :=
          norm_sub_le _ _
      _ = |inner ℝ V b| + |inner ℝ V a| := by
          rw [norm_smul, norm_smul, ha, hb, Real.norm_eq_abs, Real.norm_eq_abs, mul_one, mul_one]
      _ ≤ 2 * e := by linarith
  have hVN : inner ℝ V N = ‖c‖⁻¹ * inner ℝ V c := by rw [hN, inner_smul_right]
  -- the inner product with `N` is close to `±1`
  have hx : 1 - (2 * e / ‖c‖) ^ 2 ≤ inner ℝ V N ^ 2 := by
    rw [hVN, mul_pow, div_pow]
    have h1 : inner ℝ V c ^ 2 ≥ ‖c‖ ^ 2 - (2 * e) ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) hsmall 2
      nlinarith
    rw [inv_pow]
    have hc2 : 0 < ‖c‖ ^ 2 := by positivity
    rw [sub_le_iff_le_add, ← sub_le_iff_le_add', div_eq_mul_inv]
    calc 1 - (‖c‖ ^ 2)⁻¹ * inner ℝ V c ^ 2 = (‖c‖ ^ 2)⁻¹ * (‖c‖ ^ 2 - inner ℝ V c ^ 2) := by
          field_simp
      _ ≤ (‖c‖ ^ 2)⁻¹ * (2 * e) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
      _ = (2 * e) ^ 2 * (‖c‖ ^ 2)⁻¹ := by ring
  -- distances to `±N`
  have hd : ∀ σ : ℝ, σ ^ 2 = 1 → ‖V - σ • N‖ ^ 2 = 2 - 2 * σ * inner ℝ V N := by
    intro σ hσ
    rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, hV, hNn, mul_one,
      sq_abs, hσ]
    ring
  have ht1 : |inner ℝ V N| ≤ 1 := by
    have := abs_real_inner_le_norm V N
    rwa [hV, hNn, one_mul] at this
  have hbound : ∀ σ : ℝ, σ ^ 2 = 1 → σ * inner ℝ V N = |inner ℝ V N| →
      ‖V - σ • N‖ ≤ 4 * e / s := by
    intro σ hσ hσt
    have h2 := hd σ hσ
    rw [mul_assoc, hσt] at h2
    have hsq : ‖V - σ • N‖ ^ 2 ≤ (4 * e / s) ^ 2 := by
      rw [h2]
      have hxle : (2 * e / ‖c‖) ^ 2 ≤ (2 * e / s) ^ 2 := by
        apply pow_le_pow_left₀ (by positivity)
        exact div_le_div_of_nonneg_left (by positivity) hs hab
      have hsqt : |inner ℝ V N| ^ 2 = inner ℝ V N ^ 2 := sq_abs _
      have ht0 : 0 ≤ |inner ℝ V N| := abs_nonneg _
      have : 2 - 2 * |inner ℝ V N| ≤ 2 * (2 * e / s) ^ 2 := by nlinarith
      have h4 : 2 * (2 * e / s) ^ 2 ≤ (4 * e / s) ^ 2 := by
        have h5 : (4 * e / s) ^ 2 = 16 * (e / s) ^ 2 := by ring
        have h6 : (2 * e / s) ^ 2 = 4 * (e / s) ^ 2 := by ring
        rw [h5, h6]
        nlinarith [sq_nonneg (e / s)]
      linarith
    exact le_of_sq_le_sq hsq (by positivity)
  by_cases hpos : 0 ≤ inner ℝ V N
  · exact (min_le_left _ _).trans (by
      have := hbound 1 (by norm_num) (by rw [one_mul, abs_of_nonneg hpos])
      simpa using this)
  · push Not at hpos
    exact (min_le_right _ _).trans (by
      have := hbound (-1) (by norm_num) (by rw [abs_of_neg hpos]; ring)
      simpa [sub_eq_add_neg, neg_smul] using this)

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
