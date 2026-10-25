-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.RescaleDualGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.RescaleGeometry

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open LeanEval.Analysis.WangZahlKakeya
open wz_affine_robust_cluster_estimate

/-- The transverse dilation is self-adjoint. -/
theorem inner_stretch (t : ℝ) (u v : Space) :
    inner ℝ u (stretch t v) = inner ℝ (stretch t u) v := by
  simp only [inner_coords, stretch_zero, stretch_one, stretch_two]
  ring

theorem stretch_stretch (s t : ℝ) (u : Space) :
    stretch s (stretch t u) = stretch (s * t) u := by
  ext i
  fin_cases i <;> simp <;> ring

theorem stretch_one_eq (u : Space) : stretch 1 u = u := by
  ext i
  fin_cases i <;> simp

/-- A transverse contraction is bounded by its axial coordinate plus the
contracted full norm. -/
theorem norm_stretch_contract_le {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (u : Space) :
    ‖stretch t u‖ ≤ |u 0| + t * ‖u‖ := by
  have he : stretch t u = ((1 - t) * u 0) • axis + t • u := by
    ext i
    fin_cases i <;> simp [axis] <;> ring
  rw [he]
  calc
    _ ≤ ‖((1 - t) * u 0) • axis‖ + ‖t • u‖ := norm_add_le _ _
    _ = (1 - t) * |u 0| + t * ‖u‖ := by
      rw [norm_smul, norm_smul, norm_axis, mul_one, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_mul, abs_of_nonneg (sub_nonneg.mpr ht1), abs_of_nonneg ht]
    _ ≤ _ := by nlinarith [abs_nonneg (u 0)]

theorem abs_axial_coord_of_projective_cap {q v : Space} {ρ τ : ℝ}
    (hcap : pd v axis < 4 * ρ) (hnormal : |inner ℝ q v| ≤ τ) :
    |q 0| ≤ τ + 4 * ρ * ‖q‖ := by
  have haxis : inner ℝ q axis = q 0 := by simp [inner_coords, axis]
  rcases min_lt_iff.mp hcap with h | h
  · have he : inner ℝ q axis = inner ℝ q v - inner ℝ q (v - axis) := by
      rw [inner_sub_right]; ring
    calc
      |q 0| = |inner ℝ q v - inner ℝ q (v - axis)| := by rw [← haxis, he]
      _ ≤ |inner ℝ q v| + |inner ℝ q (v - axis)| := abs_sub _ _
      _ ≤ τ + ‖q‖ * ‖v - axis‖ := add_le_add hnormal (abs_real_inner_le_norm _ _)
      _ ≤ _ := by nlinarith [norm_nonneg q]
  · have he : inner ℝ q axis = inner ℝ q (v + axis) - inner ℝ q v := by
      rw [inner_add_right]; ring
    calc
      |q 0| = |inner ℝ q (v + axis) - inner ℝ q v| := by rw [← haxis, he]
      _ ≤ |inner ℝ q (v + axis)| + |inner ℝ q v| := abs_sub _ _
      _ ≤ ‖q‖ * ‖v + axis‖ + τ := add_le_add (abs_real_inner_le_norm _ _) hnormal
      _ ≤ _ := by nlinarith [norm_nonneg q]

/-- A normal almost perpendicular to a normalized covered direction has a
substantial transverse component. Its dual stretch has norm at least
`1 / (10 rho)`, allowing a rescaled thin slab to pull back to thickness O(delta). -/
theorem dual_stretch_norm_lower (e : Space ≃ₗᵢ[ℝ] Space) {w : Space}
    (hew : e w = axis) {ρ τ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {v u : Space} (hv : ‖v‖ = 1) (hu : ‖u‖ = 1)
    (hvw : pd v w < 4 * ρ) (hτ : τ ≤ 1 / 10)
    (hnormal : |inner ℝ u (rescaledDir e ρ v)| ≤ τ) :
    1 / (10 * ρ) ≤ ‖stretch ρ⁻¹ u‖ := by
  let q := stretch ρ⁻¹ u
  have hvne := stretch_dir_ne_zero e hρ hρ1 hv
  have hL := stretch_dir_norm_le e hew hρ hρ1 hvw
  have htau : 0 ≤ τ := (abs_nonneg _).trans hnormal
  have hqv : |inner ℝ q (e v)| ≤ 5 * τ := by
    change |inner ℝ (stretch ρ⁻¹ u) (e v)| ≤ _
    rw [← inner_stretch]
    conv_lhs => rw [← norm_smul_unit hvne]
    rw [inner_smul_right, abs_mul, abs_of_nonneg (norm_nonneg _)]
    change ‖stretch ρ⁻¹ (e v)‖ * |inner ℝ u (rescaledDir e ρ v)| ≤ _
    exact mul_le_mul hL hnormal (abs_nonneg _) (by norm_num)
  have hcap : pd (e v) axis < 4 * ρ := by rw [← hew, pd_isometry]; exact hvw
  have hq0 := abs_axial_coord_of_projective_cap hcap hqv
  have hcontract := norm_stretch_contract_le hρ.le hρ1 q
  have hinv : stretch ρ q = u := by
    dsimp [q]
    rw [stretch_stretch, mul_inv_cancel₀ hρ.ne', stretch_one_eq]
  rw [hinv, hu] at hcontract
  apply (div_le_iff₀ (by positivity : 0 < 10 * ρ)).mpr
  change 1 ≤ ‖q‖ * (10 * ρ)
  nlinarith

/-- The unnormalized physical normal of a plane in the rescaled space. -/
noncomputable def pullbackNormal (e : Space ≃ₗᵢ[ℝ] Space) (ρ : ℝ) (u : Space) : Space :=
  e.symm (stretch ρ⁻¹ u)

theorem norm_pullbackNormal (e : Space ≃ₗᵢ[ℝ] Space) (ρ : ℝ) (u : Space) :
    ‖pullbackNormal e ρ u‖ = ‖stretch ρ⁻¹ u‖ := e.symm.norm_map _

theorem pullbackNormal_ne_zero (e : Space ≃ₗᵢ[ℝ] Space) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {u : Space} (hu : ‖u‖ = 1) :
    pullbackNormal e ρ u ≠ 0 := by
  have hh := norm_le_stretch ((one_le_inv₀ hρ).mpr hρ1) u
  rw [hu, ← norm_pullbackNormal e] at hh
  exact norm_ne_zero_iff.mp (by linarith)

theorem inner_pullbackNormal (e : Space ≃ₗᵢ[ℝ] Space) (ρ : ℝ) (u p : Space) :
    inner ℝ (pullbackNormal e ρ u) p = inner ℝ u (stretch ρ⁻¹ (e p)) := by
  rw [inner_stretch]
  rw [← e.inner_map_map (pullbackNormal e ρ u) p]
  simp only [pullbackNormal, e.apply_symm_apply]

theorem inner_rescaleMap_sub (e : Space ≃ₗᵢ[ℝ] Space) (y w : Space)
    {κ ρ : ℝ} (hκ : 0 < κ) (hρ : 0 < ρ) (u p q : Space) :
    inner ℝ u (rescaleMap e y w hκ hρ p - rescaleMap e y w hκ hρ q) =
      κ * inner ℝ (pullbackNormal e ρ u) (p - q) := by
  rw [rescaleMap_sub, inner_smul_right, inner_pullbackNormal]

/-- Exact pullback of a slab, expressed about an arbitrary physical center. -/
theorem rescaled_slab_pullback (e : Space ≃ₗᵢ[ℝ] Space) (y w : Space)
    {κ ρ : ℝ} (hκ : 0 < κ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {u : Space} (hu : ‖u‖ = 1) (p p₀ : Space) (t a : ℝ)
    (hslab : |inner ℝ u (rescaleMap e y w hκ hρ p) - t| ≤ a) :
    |inner ℝ (unit (pullbackNormal e ρ u)) (p - p₀) -
      (t - inner ℝ u (rescaleMap e y w hκ hρ p₀)) /
        (κ * ‖pullbackNormal e ρ u‖)| ≤ a / (κ * ‖pullbackNormal e ρ u‖) := by
  have hN : 0 < ‖pullbackNormal e ρ u‖ := norm_pos_iff.mpr (pullbackNormal_ne_zero e hρ hρ1 hu)
  have hinner := inner_rescaleMap_sub e y w hκ hρ u p p₀
  rw [inner_sub_right] at hinner
  have he : inner ℝ (unit (pullbackNormal e ρ u)) (p - p₀) -
      (t - inner ℝ u (rescaleMap e y w hκ hρ p₀)) / (κ * ‖pullbackNormal e ρ u‖) =
      (inner ℝ u (rescaleMap e y w hκ hρ p) - t) / (κ * ‖pullbackNormal e ρ u‖) := by
    rw [unit, real_inner_smul_left]
    field_simp
    nlinarith [hinner]
  rw [he, abs_div, abs_of_pos (mul_pos hκ hN)]
  exact div_le_div_of_nonneg_right hslab (by positivity)

/-- The normalized pullback normal has a controlled component in every
original direction whose rescaled normal component is small. -/
theorem normalized_pullback_direction (e : Space ≃ₗᵢ[ℝ] Space) {w : Space}
    (hew : e w = axis) {ρ τ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {v u : Space} (hv : ‖v‖ = 1) (hu : ‖u‖ = 1)
    (hvw : pd v w < 4 * ρ) (hτ : τ ≤ 1 / 10)
    (hnormal : |inner ℝ u (rescaledDir e ρ v)| ≤ τ) :
    |inner ℝ (unit (pullbackNormal e ρ u)) v| ≤ 50 * ρ * τ := by
  have hN : 0 < ‖pullbackNormal e ρ u‖ := norm_pos_iff.mpr (pullbackNormal_ne_zero e hρ hρ1 hu)
  have hlow := dual_stretch_norm_lower e hew hρ hρ1 hv hu hvw hτ hnormal
  rw [← norm_pullbackNormal e] at hlow
  have hNinv : ‖pullbackNormal e ρ u‖⁻¹ ≤ 10 * ρ := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hN).mpr
    have hh := (div_le_iff₀ (by positivity : 0 < 10 * ρ)).mp hlow
    nlinarith
  have hvne := stretch_dir_ne_zero e hρ hρ1 hv
  have hL := stretch_dir_norm_le e hew hρ hρ1 hvw
  have htau : 0 ≤ τ := (abs_nonneg _).trans hnormal
  have hinner : |inner ℝ (pullbackNormal e ρ u) v| ≤ 5 * τ := by
    rw [inner_pullbackNormal]
    conv_lhs => rw [← norm_smul_unit hvne]
    rw [inner_smul_right, abs_mul, abs_of_nonneg (norm_nonneg _)]
    change ‖stretch ρ⁻¹ (e v)‖ * |inner ℝ u (rescaledDir e ρ v)| ≤ _
    exact mul_le_mul hL hnormal (abs_nonneg _) (by norm_num)
  rw [unit, real_inner_smul_left, abs_mul, abs_of_nonneg (inv_nonneg.mpr hN.le)]
  calc
    _ ≤ (10 * ρ) * (5 * τ) := mul_le_mul hNinv hinner (abs_nonneg _) (by positivity)
    _ = _ := by ring

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
