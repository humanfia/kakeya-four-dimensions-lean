-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.GGGrainSlab.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.GGSlab
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.GGCovering

/-!
# Local grains of the fine family give AD slabs of the rescaled fibre

Prop. 4.1, Step 1 of the sticky Kakeya paper, (4.33) ⟹ (4.34): the fibre of a coarse tube
of radius `ρ0` is rescaled by `φ = resc w c0 A b` with `A = 1 / (100 ρ0)`. A slab of height
`h = b ρ0` of the rescaled fibre comes from a ball of radius `5 ρ0` of the fine union, on
which the plane map at one point gives an AD projection at scale `25 ρ0²`. After rescaling,
the projection on the unit vector `V̂ ⊥ w` is AD at scale `h`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open Set Metric MeasureTheory
open scoped ENNReal Pointwise Classical RealInnerProductSpace
open WangZahlLot.Obl.wz_separated_cover_refinement (Tube Dilate)

/-- The height of a rescaled point is the rescaled height. -/
theorem inner_resc_self {w c0 : Space} (hw : ‖w‖ = 1) (A b : ℝ) (p : Space) :
    ⟪resc w c0 A b p, w⟫ = b * ⟪p - c0, w⟫ := by
  have hww : ⟪w, w⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hw]; norm_num
  have hc : ⟪w, p - c0⟫ = ⟪p - c0, w⟫ := real_inner_comm _ _
  rw [resc, aniso_apply]
  simp only [real_inner_smul_left, inner_add_left, hww, hc]
  ring

/-- The rescaled projection on a direction orthogonal to `w`. -/
theorem inner_resc_perp {w c0 V : Space} (hw : ‖w‖ = 1) (A b : ℝ) (p : Space) :
    ⟪V - ⟪V, w⟫ • w, resc w c0 A b p⟫ =
      b * A * ⟪V, p⟫ - b * A * ⟪V, c0⟫ - A * ⟪V, w⟫ * ⟪resc w c0 A b p, w⟫ := by
  have hww : ⟪w, w⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hw]; norm_num
  rw [inner_resc_self hw]
  have hc : ⟪w, p - c0⟫ = ⟪p - c0, w⟫ := real_inner_comm _ _
  rw [resc, aniso_apply]
  simp only [real_inner_smul_right, inner_add_right, inner_sub_left, real_inner_smul_left, hww,
    hc]
  have h1 : ⟪V, p - c0⟫ = ⟪V, p⟫ - ⟪V, c0⟫ := inner_sub_right _ _ _
  rw [h1]
  ring

/-- Two points of a coarse tube whose rescaled heights are close are close. -/
theorem dist_of_same_slab {ρ0 b h : ℝ} (hb : 0 < b) {p q : Space}
    {z0 w0 c : Space} (hw0 : ‖w0‖ = 1) (hp : p ∈ tube ρ0 z0 w0) (hq : q ∈ tube ρ0 z0 w0)
    (hpq : |⟪resc w0 c (1 / 100 / ρ0) b p, w0⟫ - ⟪resc w0 c (1 / 100 / ρ0) b q, w0⟫| < h) :
    ‖p - q‖ < h / b + 4 * ρ0 := by
  rw [inner_resc_self hw0, inner_resc_self hw0, ← mul_sub, abs_mul, abs_of_pos hb] at hpq
  have hpq' : |⟪p - c, w0⟫ - ⟪q - c, w0⟫| < h / b := by rw [lt_div_iff₀ hb]; linarith
  obtain ⟨s, -, hs⟩ := exists_param_of_mem_Tube hp
  obtain ⟨t, -, ht⟩ := exists_param_of_mem_Tube hq
  have hw1 : ∀ u : Space, |⟪u, w0⟫| ≤ ‖u‖ := fun u => by
    have := abs_real_inner_le_norm u w0
    rwa [hw0, mul_one] at this
  have hww : ⟪w0, w0⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hw0]; norm_num
  have e1 : ⟪p - c, w0⟫ - ⟪q - c, w0⟫ = (s - t) + ⟪p - (z0 + s • w0), w0⟫ -
      ⟪q - (z0 + t • w0), w0⟫ := by
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left, hww]
    ring
  have h1 := hw1 (p - (z0 + s • w0))
  have h2 := hw1 (q - (z0 + t • w0))
  have hst : |s - t| < h / b + 2 * ρ0 := by
    rw [e1] at hpq'
    have := abs_sub_abs_le_abs_sub (s - t) (⟪q - (z0 + t • w0), w0⟫ - ⟪p - (z0 + s • w0), w0⟫)
    have e2 : s - t - (⟪q - (z0 + t • w0), w0⟫ - ⟪p - (z0 + s • w0), w0⟫) =
        s - t + ⟪p - (z0 + s • w0), w0⟫ - ⟪q - (z0 + t • w0), w0⟫ := by ring
    rw [e2] at this
    have h3 : |⟪q - (z0 + t • w0), w0⟫ - ⟪p - (z0 + s • w0), w0⟫| < 2 * ρ0 := by
      calc _ ≤ |⟪q - (z0 + t • w0), w0⟫| + |⟪p - (z0 + s • w0), w0⟫| := abs_sub _ _
        _ < ρ0 + ρ0 := by linarith
        _ = 2 * ρ0 := by ring
    linarith
  have e3 : p - q = (s - t) • w0 + (p - (z0 + s • w0)) - (q - (z0 + t • w0)) := by module
  rw [e3]
  calc ‖(s - t) • w0 + (p - (z0 + s • w0)) - (q - (z0 + t • w0))‖
      ≤ ‖(s - t) • w0‖ + ‖p - (z0 + s • w0)‖ + ‖q - (z0 + t • w0)‖ := by
        have := norm_sub_le ((s - t) • w0 + (p - (z0 + s • w0))) (q - (z0 + t • w0))
        have := norm_add_le ((s - t) • w0) (p - (z0 + s • w0))
        linarith
    _ < (h / b + 2 * ρ0) + ρ0 + ρ0 := by
        rw [norm_smul, hw0, mul_one, Real.norm_eq_abs]
        linarith
    _ = h / b + 4 * ρ0 := by ring

/-- The component of `V` orthogonal to a unit vector has norm at least `1/2` when `V` is a
unit vector almost orthogonal to it. -/
theorem norm_perp_ge {V w : Space} (hV : ‖V‖ = 1) (hw : ‖w‖ = 1) (hVw : |⟪V, w⟫| ≤ 1 / 2) :
    1 / 2 ≤ ‖V - ⟪V, w⟫ • w‖ := by
  have hww : ⟪w, w⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hw]; norm_num
  have hVV : ⟪V, V⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hV]; norm_num
  have hsq : ‖V - ⟪V, w⟫ • w‖ ^ 2 = 1 - ⟪V, w⟫ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      hww, hVV, real_inner_comm V w]
    ring
  have h1 : ⟪V, w⟫ ^ 2 ≤ 1 / 4 := by
    have := sq_abs ⟪V, w⟫
    nlinarith [abs_nonneg ⟪V, w⟫]
  nlinarith [norm_nonneg (V - ⟪V, w⟫ • w)]

/-- The rescaled slab of a fibre is AD at the slab height in the direction of the
normalized orthogonal component of the plane map at a point of the slab. -/
theorem slab_covering {σ C ρ0 b : ℝ} (hρ0 : 0 < ρ0) (hρ01 : ρ0 ≤ 1 / 100) (hb : 0 < b)
    {E F : Set Space} {V : Space → Space} {z0 w0 c : Space} (hw0 : ‖w0‖ = 1)
    (hFE : F ⊆ E) (hFt : F ⊆ tube ρ0 z0 w0)
    {p0 : Space} (hp0 : p0 ∈ F) (hV1 : ‖V p0‖ = 1) (hVw : |⟪V p0, w0⟫| ≤ 5 * ρ0)
    (hloc : Covering ((5 * ρ0) ^ 2) (1 - σ) C
      ((fun q => ⟪V p0, q⟫) '' (E ∩ ball p0 (5 * ρ0))))
    (hσ : σ ≤ 1) (hC : 0 ≤ C)
    (z : ℤ) (hp0z : resc w0 c (1 / 100 / ρ0) b p0 ∈ slab w0 (b * ρ0) z) :
    Covering (b * ρ0) (1 - σ) (4 ^ (1 - σ) * C)
      ((fun q => ⟪‖V p0 - ⟪V p0, w0⟫ • w0‖⁻¹ • (V p0 - ⟪V p0, w0⟫ • w0), q⟫) ''
        (resc w0 c (1 / 100 / ρ0) b '' F ∩ slab w0 (b * ρ0) z)) := by
  set A : ℝ := 1 / 100 / ρ0 with hA
  set h : ℝ := b * ρ0 with hh
  have hApos : 0 < A := by positivity
  have hhpos : 0 < h := by positivity
  set φ := resc w0 c A b with hφ
  set U : Space := V p0 - ⟪V p0, w0⟫ • w0 with hU
  have hnU : 1 / 2 ≤ ‖U‖ := norm_perp_ge hV1 hw0 (by linarith)
  have hnU0 : 0 < ‖U‖ := by linarith
  -- the affine image of the local grain
  set K : ℝ := -(b * A * ⟪V p0, c⟫) - A * ⟪V p0, w0⟫ * (h * z) with hK
  have hbA : b * A * (5 * ρ0) ^ 2 = h / 4 := by rw [hA, hh]; field_simp; ring
  have hB' := hloc.affine (l := b * A) (by positivity) K
  rw [hbA] at hB'
  -- the orthogonal projection of the rescaled slab is close to it
  have hT : Covering (2 * (h / 4)) (1 - σ) (4 ^ (1 - σ) * C)
      ((fun q => ⟪U, q⟫) '' (φ '' F ∩ slab w0 h z)) := by
    apply hB'.of_close (by positivity) (by linarith) hC
    rintro _ ⟨_, ⟨⟨p, hpF, rfl⟩, hpz⟩, rfl⟩
    refine ⟨b * A * ⟪V p0, p⟫ + K, ⟨⟪V p0, p⟫, ⟨p, ⟨hFE hpF, ?_⟩, rfl⟩, rfl⟩, ?_⟩
    · -- the point is in the ball of radius `5 ρ0`
      rw [mem_ball, dist_eq_norm]
      have hd : |⟪φ p, w0⟫ - ⟪φ p0, w0⟫| < h := by
        obtain ⟨h1, h2⟩ := hpz
        obtain ⟨h3, h4⟩ := hp0z
        rw [abs_lt]; constructor <;> linarith
      have := dist_of_same_slab hb hw0 (hFt hpF) (hFt hp0) hd
      have he : h / b + 4 * ρ0 = 5 * ρ0 := by rw [hh]; field_simp; ring
      linarith
    · -- the height term is small
      have hval := inner_resc_perp (c0 := c) (V := V p0) hw0 A b p
      rw [Real.dist_eq]
      simp only at hval ⊢
      rw [hval, hK]
      have hz1 : h * z ≤ ⟪φ p, w0⟫ := hpz.1
      have hz2 : ⟪φ p, w0⟫ < h * (z + 1) := hpz.2
      have e1 : b * A * ⟪V p0, p⟫ - b * A * ⟪V p0, c⟫ - A * ⟪V p0, w0⟫ * ⟪φ p, w0⟫ -
          (b * A * ⟪V p0, p⟫ + (-(b * A * ⟪V p0, c⟫) - A * ⟪V p0, w0⟫ * (h * z))) =
          -(A * ⟪V p0, w0⟫ * (⟪φ p, w0⟫ - h * z)) := by ring
      rw [e1, abs_neg, abs_mul, abs_mul, abs_of_pos hApos,
        abs_of_nonneg (by linarith : 0 ≤ ⟪φ p, w0⟫ - h * z)]
      have h5 : ⟪φ p, w0⟫ - h * z ≤ h := by linarith
      calc A * |⟪V p0, w0⟫| * (⟪φ p, w0⟫ - h * z) ≤ A * (5 * ρ0) * h := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hVw hApos.le) h5 (by linarith)
              (by positivity)
        _ = h / 20 := by rw [hA]; field_simp; ring
        _ ≤ h / 4 := by linarith
  -- normalization of the direction
  have hT' := hT.affine (l := ‖U‖⁻¹) (by positivity) 0
  have himg : (fun u => ‖U‖⁻¹ * u + 0) '' ((fun q => ⟪U, q⟫) '' (φ '' F ∩ slab w0 h z)) =
      (fun q => ⟪‖U‖⁻¹ • U, q⟫) '' (φ '' F ∩ slab w0 h z) := by
    rw [Set.image_image]
    congr 1
    funext q
    rw [real_inner_smul_left, add_zero]
  rw [himg] at hT'
  apply hT'.mono_scale
  have h2 : ‖U‖⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hnU0 (by norm_num)]; linarith
  calc ‖U‖⁻¹ * (2 * (h / 4)) ≤ 2 * (2 * (h / 4)) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = h := by ring

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
