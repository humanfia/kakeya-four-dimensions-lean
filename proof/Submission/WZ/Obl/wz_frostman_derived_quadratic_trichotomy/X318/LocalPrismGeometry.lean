-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.LocalPrismGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.CoarseParentNeighbors
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.AxialSlack

-- Copied from session x0318 (x0210 lineage) (o070 branch, commit 7b9811e, file LocalPrismGeometry.lean), namespace renamed.
namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open Set Metric

/-- Exact unit-segment containment controls the unoriented axis as well as the
midpoint. -/
theorem axes_near_of_tube_subset {δ ρ : ℝ} (hδ : 0 < δ) {x v z w : Space}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hsub : Tube δ x v ⊆ Tube ρ z w) :
    UnorientedNear (4 * ρ) v w := by
  have hseg := (self_subset_thickening hδ (segment ℝ x (x + v))).trans hsub
  obtain ⟨p, hp, hxp⟩ := mem_thickening_iff.mp (hseg (left_mem_segment ℝ x (x + v)))
  obtain ⟨q, hq, hxq⟩ := mem_thickening_iff.mp (hseg (right_mem_segment ℝ x (x + v)))
  rw [segment_eq_image'] at hp hq
  obtain ⟨a, ha, rfl⟩ := hp
  obtain ⟨b, hb, rfl⟩ := hq
  simp only [add_sub_cancel_left, dist_eq_norm] at hxp hxq
  have hvw : ‖v - (b - a) • w‖ < 2 * ρ := by
    have he : v - (b - a) • w =
        (x + v - (z + b • w)) - (x - (z + a • w)) := by module
    rw [he]
    exact (norm_sub_le _ _).trans_lt (by linarith)
  have hgap : 1 - |b - a| < 2 * ρ := by
    have hh := norm_sub_norm_le v ((b - a) • w)
    rw [hv, norm_smul, hw, Real.norm_eq_abs, mul_one] at hh
    exact hh.trans_lt hvw
  have hbound : |b - a| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
  rcases le_total 0 (b - a) with hpos | hneg
  · left
    have he : v - w = (v - (b - a) • w) + (b - a - 1) • w := by module
    have ht : ‖(b - a - 1) • w‖ < 2 * ρ := by
      rw [norm_smul, hw, Real.norm_eq_abs, mul_one,
        abs_of_nonpos (by linarith [(abs_le.mp hbound).2] : b - a - 1 ≤ 0)]
      rw [abs_of_nonneg hpos] at hgap
      linarith
    rw [he]
    exact (norm_add_le _ _).trans (by linarith)
  · right
    have he : v + w = (v - (b - a) • w) + (b - a + 1) • w := by module
    have ht : ‖(b - a + 1) • w‖ < 2 * ρ := by
      rw [norm_smul, hw, Real.norm_eq_abs, mul_one,
        abs_of_nonneg (by linarith [(abs_le.mp hbound).1] : 0 ≤ b - a + 1)]
      rw [abs_of_nonpos hneg] at hgap
      linarith
    rw [he]
    exact (norm_add_le _ _).trans (by linarith)

lemma axis_projection_of_endpoints {a : ℝ} {e c x v : Space}
    (hleft : |inner ℝ e (x - c)| ≤ a)
    (hright : |inner ℝ e (x + v - c)| ≤ a) : |inner ℝ e v| ≤ 2 * a := by
  rw [abs_le] at hleft hright ⊢
  simp only [inner_sub_right, inner_add_right] at hleft hright
  constructor <;> linarith [hleft.1, hleft.2, hright.1, hright.2]

/-- A thin transverse rectangle containing a unit tube determines its long
axis to within four times the wider transverse width. -/
theorem tube_axis_near_of_transverse {δ a b : ℝ} (hδ : 0 < δ) (hab : a ≤ b)
    {x v c e₁ e₂ e₃ : Space} (hv : ‖v‖ = 1)
    (he : Orthonormal ℝ ![e₁, e₂, e₃])
    (hsub : Tube δ x v ⊆ {y | |inner ℝ e₁ (y - c)| ≤ a ∧ |inner ℝ e₂ (y - c)| ≤ b}) :
    UnorientedNear (4 * b) v e₃ := by
  have hleft := hsub (self_subset_thickening hδ _ (left_mem_segment ℝ x (x + v)))
  have hright := hsub (self_subset_thickening hδ _ (right_mem_segment ℝ x (x + v)))
  have h₁ := axis_projection_of_endpoints hleft.1 hright.1
  have h₂ := axis_projection_of_endpoints hleft.2 hright.2
  obtain ⟨s, hs, hclose⟩ := unit_axis_close_of_transverse he hv
    (h₁.trans (by linarith : 2 * a ≤ 2 * b)) h₂
  have hbound : ‖v - s • e₃‖ ≤ 4 * b := by linarith
  rcases hs with rfl | rfl
  · exact Or.inl (by simpa only [one_smul] using hbound)
  · exact Or.inr (by simpa only [neg_one_smul, sub_neg_eq_add] using hbound)

noncomputable def axialRecenter (c o e : Space) : Space := c + inner ℝ e (o - c) • e

lemma axial_recenter_transverse {c o e f y : Space} (hef : inner ℝ f e = 0) :
    inner ℝ f (y - axialRecenter c o e) = inner ℝ f (y - c) := by
  simp [axialRecenter, inner_sub_right, inner_add_right, inner_smul_right, hef]

lemma axial_recenter_longitudinal {c o e y : Space} (he : inner ℝ e e = 1) :
    inner ℝ e (y - axialRecenter c o e) = inner ℝ e (y - o) := by
  simp only [axialRecenter, inner_sub_right, inner_add_right, inner_smul_right, he, mul_one]
  ring

/-- Recentring the long coordinate at the coarse tube midpoint retains all old
transverse incidences, and one contained unit tube controls the new center and
axis relative to the parent. -/
theorem recentered_local_prism {δ ρ a b : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1 / 2) (hab : a ≤ b) (hbρ : b ≤ ρ)
    {x v z w c e₁ e₂ e₃ : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (he : Orthonormal ℝ ![e₁, e₂, e₃])
    (hparent : Tube δ x v ⊆ Tube ρ z w)
    (htrans : Tube δ x v ⊆ {y | |inner ℝ e₁ (y - c)| ≤ a ∧ |inner ℝ e₂ (y - c)| ≤ b}) :
    ∃ c' : Space,
      (Tube ρ z w ∩ {y | |inner ℝ e₁ (y - c)| ≤ a ∧ |inner ℝ e₂ (y - c)| ≤ b} ⊆
        Prism a b c' e₁ e₂ e₃) ∧
      ‖c' - center z w‖ ≤ 6 * ρ ∧ UnorientedNear (8 * ρ) e₃ w := by
  let o := center z w
  let c' := axialRecenter c o e₃
  have h₁₃ : inner ℝ e₁ e₃ = 0 := by
    simpa using orthonormal_iff_ite.mp he (0 : Fin 3) 2
  have h₂₃ : inner ℝ e₂ e₃ = 0 := by
    simpa using orthonormal_iff_ite.mp he (1 : Fin 3) 2
  have h₃₃ : inner ℝ e₃ e₃ = 1 := by
    simpa using orthonormal_iff_ite.mp he (2 : Fin 3) 2
  have hn₁ : ‖e₁‖ = 1 := by simpa using he.norm_eq_one (0 : Fin 3)
  have hn₂ : ‖e₂‖ = 1 := by simpa using he.norm_eq_one (1 : Fin 3)
  have hn₃ : ‖e₃‖ = 1 := by simpa using he.norm_eq_one (2 : Fin 3)
  refine ⟨c', ?_, ?_, ?_⟩
  · rintro y ⟨hy, hy₁, hy₂⟩
    change |inner ℝ e₁ (y - c')| ≤ a ∧ |inner ℝ e₂ (y - c')| ≤ b ∧
      |inner ℝ e₃ (y - c')| ≤ 1
    change |inner ℝ e₁ (y - axialRecenter c o e₃)| ≤ a ∧
      |inner ℝ e₂ (y - axialRecenter c o e₃)| ≤ b ∧
      |inner ℝ e₃ (y - axialRecenter c o e₃)| ≤ 1
    rw [axial_recenter_transverse h₁₃, axial_recenter_transverse h₂₃,
      axial_recenter_longitudinal h₃₃]
    exact ⟨hy₁, hy₂, (tube_projection_about_center hw hn₃ hy).le.trans (by linarith)⟩
  · have hmid : center x v ∈ Tube δ x v := by
      apply self_subset_thickening hδ
      rw [segment_eq_image']
      exact ⟨1 / 2, by norm_num, by simp [center]⟩
    have hmidtrans := htrans hmid
    have hmidparent := (center_near_of_tube_subset hδ hv hw hparent).le
    have hbound (e : Space) (hne : ‖e‖ = 1)
        (ht : |inner ℝ e (center x v - c)| ≤ b) : |inner ℝ e (c - o)| ≤ 3 * ρ := by
      have hprox : |inner ℝ e (center x v - o)| ≤ 2 * ρ :=
        (abs_real_inner_le_norm _ _).trans (by simpa only [hne, one_mul] using hmidparent)
      have hident : inner ℝ e (c - o) =
          inner ℝ e (center x v - o) - inner ℝ e (center x v - c) := by
        simp only [inner_sub_right]
        ring
      rw [hident]
      exact (abs_sub _ _).trans (by linarith)
    have hc₁ : inner ℝ e₁ (c' - o) = inner ℝ e₁ (c - o) := by
      simp [c', axialRecenter, inner_sub_right, inner_add_right, inner_smul_right, h₁₃]
    have hc₂ : inner ℝ e₂ (c' - o) = inner ℝ e₂ (c - o) := by
      simp [c', axialRecenter, inner_sub_right, inner_add_right, inner_smul_right, h₂₃]
    have hc₃ : inner ℝ e₃ (c' - o) = 0 := by
      simp only [c', axialRecenter, inner_sub_right, inner_add_right, inner_smul_right, h₃₃, mul_one]
      ring
    have hs₁ : (inner ℝ e₁ (c' - o)) ^ 2 ≤ (3 * ρ) ^ 2 := by
      rw [hc₁]
      exact (sq_le_sq).mpr (by
        simpa only [abs_of_nonneg (by positivity : 0 ≤ 3 * ρ)] using
          (hbound e₁ hn₁ (hmidtrans.1.trans hab)))
    have hs₂ : (inner ℝ e₂ (c' - o)) ^ 2 ≤ (3 * ρ) ^ 2 := by
      rw [hc₂]
      exact (sq_le_sq).mpr (by
        simpa only [abs_of_nonneg (by positivity : 0 ≤ 3 * ρ)] using
          (hbound e₂ hn₂ hmidtrans.2))
    obtain ⟨B, hB₁, hB₂, hB₃⟩ := basis_of_frame he
    have hnorm := B.sum_sq_inner_right (c' - o)
    simp only [Fin.sum_univ_three, hB₁, hB₂, hB₃, hc₃, zero_pow (by norm_num : 2 ≠ 0), add_zero] at hnorm
    change ‖c' - o‖ ≤ 6 * ρ
    nlinarith [norm_nonneg (c' - o)]
  · exact ((tube_axis_near_of_transverse hδ hab hv he htrans).symm.trans
      (axes_near_of_tube_subset hδ hv hw hparent)).mono (by linarith)

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
