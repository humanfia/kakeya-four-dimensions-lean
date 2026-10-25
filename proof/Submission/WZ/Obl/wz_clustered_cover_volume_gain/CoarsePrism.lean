-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.CoarsePrism.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.CoarseNormals
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.OrthogonalPair
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.TubeBoxes
import Submission.WZ.Obl.wz_transverse_cell_weighted_cover.Basic

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Metric
open WangZahlLot.Obl.wz_flat_factored_improvement (Space)
open WangZahlLot.Obl.wz_regular_transverse_affine_cells (orthogonalBox)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (unit norm_unit)

lemma linear_box_enclosure (A : Space →ₗ[ℝ] Space)
    (v u : OrthonormalBasis (Fin 3) ℝ Space) (z : Space)
    {a b c K L C : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hshort : ∀ p, inner ℝ (u 0) (A p) = K * inner ℝ (v 0) p)
    (hmiddle : inner ℝ (u 1) (A (v 2)) = 0)
    (hA0 : ‖A (v 0)‖ ≤ L) (hA1 : ‖A (v 1)‖ ≤ L) (hA2 : ‖A (v 2)‖ ≤ C) :
    A '' orthogonalBox ![a, b, c] z v ⊆
      orthogonalBox ![K * a, L * (a + b), L * (a + b) + C * c] (A z) u := by
  rintro _ ⟨p, hp, rfl⟩ j
  rw [← map_sub]
  have hp0 : |inner ℝ (v 0) (p - z)| ≤ a := hp 0
  have hp1 : |inner ℝ (v 1) (p - z)| ≤ b := hp 1
  have hp2 : |inner ℝ (v 2) (p - z)| ≤ c := hp 2
  have he : A (p - z) = inner ℝ (v 0) (p - z) • A (v 0) +
      inner ℝ (v 1) (p - z) • A (v 1) + inner ℝ (v 2) (p - z) • A (v 2) := by
    conv_lhs => rw [WangZahlLot.Obl.wz_transverse_cell_weighted_cover.eq_sum_frame v.orthonormal (p - z)]
    simp only [map_add, map_smul]
  have hnorm : ‖A (p - z)‖ ≤ L * (a + b) + C * c := by
    rw [he]
    have h0 := mul_le_mul hp0 hA0 (norm_nonneg _) ha
    have h1 := mul_le_mul hp1 hA1 (norm_nonneg _) hb
    have h2 := mul_le_mul hp2 hA2 (norm_nonneg _) hc
    calc
      _ ≤ ‖inner ℝ (v 0) (p - z) • A (v 0)‖ +
          ‖inner ℝ (v 1) (p - z) • A (v 1)‖ + ‖inner ℝ (v 2) (p - z) • A (v 2)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ _ := by
        simp only [norm_smul, Real.norm_eq_abs]
        nlinarith
  fin_cases j
  · change |inner ℝ (u 0) (A (p - z))| ≤ K * a
    rw [hshort, abs_mul, abs_of_nonneg hK]
    exact mul_le_mul_of_nonneg_left hp0 hK
  · change |inner ℝ (u 1) (A (p - z))| ≤ L * (a + b)
    have hi0 : |inner ℝ (u 1) (A (v 0))| ≤ L := by
      simpa only [u.norm_eq_one, one_mul] using (abs_real_inner_le_norm (u 1) (A (v 0))).trans
        (by simpa only [u.norm_eq_one, one_mul] using hA0)
    have hi1 : |inner ℝ (u 1) (A (v 1))| ≤ L := by
      simpa only [u.norm_eq_one, one_mul] using (abs_real_inner_le_norm (u 1) (A (v 1))).trans
        (by simpa only [u.norm_eq_one, one_mul] using hA1)
    rw [he, inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
      inner_smul_right, hmiddle, mul_zero, add_zero]
    have hh := abs_add_le (inner ℝ (v 0) (p - z) * inner ℝ (u 1) (A (v 0)))
      (inner ℝ (v 1) (p - z) * inner ℝ (u 1) (A (v 1)))
    rw [abs_mul, abs_mul] at hh
    have h0 := mul_le_mul hp0 hi0 (abs_nonneg _) ha
    have h1 := mul_le_mul hp1 hi1 (abs_nonneg _) hb
    nlinarith
  · change |inner ℝ (u 2) (A (p - z))| ≤ L * (a + b) + C * c
    have hh := abs_real_inner_le_norm (u 2) (A (p - z))
    rw [u.norm_eq_one, one_mul] at hh
    exact hh.trans hnorm

/-- The normalized image of a rectangular grain fits in another rectangular
prism with its short axis equal to the transported normal. -/
lemma coarse_prism_enclosure {θ a b c C : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ θ * c) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (v : OrthonormalBasis (Fin 3) ℝ Space) (z : Space)
    (haxis : ‖coarseLinear θ (v 2)‖ ≤ C) :
    ∃ u : OrthonormalBasis (Fin 3) ℝ Space,
      u 0 = unit (dualLinear θ (v 0)) ∧
      u 2 = unit (coarseLinear θ (v 2)) ∧
      coarseLinear θ '' orthogonalBox ![a, b, c] z v ⊆
        orthogonalBox ![a / θ, 2 * b / θ, (C + 2) * c] (coarseLinear θ z) u := by
  have hn0 : v 0 ≠ 0 := by intro hz; have hh := v.norm_eq_one 0; simp [hz] at hh
  have hl0 : coarseLinear θ (v 2) ≠ 0 := by
    intro hz
    have hh := congrArg (dualLinear θ) hz
    rw [dual_coarse hθ, map_zero] at hh
    have hv := v.norm_eq_one 2
    simp [hh] at hv
  obtain ⟨u, hu0, hu2⟩ := basis_of_orthogonal_pair
    (norm_unit (norm_ne_zero_iff.mp (dualLinear_norm_pos hθ hθ1 hn0).ne')) (norm_unit hl0)
    (normal_transport_orthogonal hθ (by simp [v.inner_eq_ite]))
  have hdpos := dualLinear_norm_pos hθ hθ1 hn0
  have hshort : ∀ p, inner ℝ (u 0) (coarseLinear θ p) =
      ‖dualLinear θ (v 0)‖⁻¹ * inner ℝ (v 0) p := by
    intro p
    rw [hu0, unit, real_inner_smul_left, dual_inner_coarse hθ]
  have hmiddle : inner ℝ (u 1) (coarseLinear θ (v 2)) = 0 := by
    have he : coarseLinear θ (v 2) = ‖coarseLinear θ (v 2)‖ • u 2 := by
      rw [hu2]
      exact (WangZahlLot.Obl.wz_affine_robust_cluster_estimate.norm_smul_unit hl0).symm
    rw [he, inner_smul_right]
    simp [u.inner_eq_ite]
  have hAnorm (j : Fin 3) : ‖coarseLinear θ (v j)‖ ≤ θ⁻¹ := by
    simpa only [v.norm_eq_one, mul_one] using coarseLinear_norm_le hθ hθ1 (v j)
  have hbox := linear_box_enclosure (coarseLinear θ) v u z ha (ha.trans hab) hc
    (inv_pos.mpr hdpos).le (inv_pos.mpr hθ).le hC hshort hmiddle (hAnorm 0) (hAnorm 1) haxis
  refine ⟨u, hu0, hu2, hbox.trans ?_⟩
  intro p hp j
  have hK : ‖dualLinear θ (v 0)‖⁻¹ ≤ θ⁻¹ := by
    apply inv_anti₀ hθ
    simpa only [v.norm_eq_one, mul_one] using dualLinear_norm_lower hθ hθ1 (v 0)
  have hab' : a + b ≤ 2 * b := by linarith
  have hmid : θ⁻¹ * (a + b) ≤ 2 * b / θ := by
    have hh := mul_le_mul_of_nonneg_left hab' (inv_pos.mpr hθ).le
    simpa only [div_eq_mul_inv, mul_comm] using hh
  have hlong : θ⁻¹ * (a + b) + C * c ≤ (C + 2) * c := by
    have hh : b / θ ≤ c := (div_le_iff₀ hθ).mpr (by simpa [mul_comm] using hbc)
    simp only [div_eq_mul_inv] at hmid hh
    nlinarith
  have hi := hp j
  fin_cases j
  · apply hi.trans
    change ‖dualLinear θ (v 0)‖⁻¹ * a ≤ a / θ
    simpa only [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_right hK ha
  · exact hi.trans hmid
  · exact hi.trans hlong

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
