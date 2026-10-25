-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.PacketNormalization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.TubeStretch
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BoxCover

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_flat_factored_improvement
open WangZahlLot.Obl.wz_regular_transverse_affine_cells (orthogonalBox)

/-- An anisotropic packet normalization keeps the long direction macroscopic.
The two transverse scales may be arbitrarily small. -/
theorem anisotropic_packet_normalization {n : ℕ} {A B c r C : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hc : 0 < c) (hC : 0 < C)
    (hAC : A ≤ C) (hBC : B ≤ C) (hcC : 8 * c ≤ C)
    (u : OrthonormalBasis (Fin 3) ℝ Space) (z₀ : Space)
    (U : Fin n → Set Space) (z v : Fin n → Space)
    (hbox : ∀ i, U i ⊆ orthogonalBox ![A / 4, B / 4, 2 * c] z₀ u)
    (hball : ∀ i, ball (z i) r ⊆ U i)
    (hends : ∀ i, z i + (c / 2) • v i ∈ U i ∧ z i - (c / 2) • v i ∈ U i)
    (hlong : ∀ i, 1 / 2 ≤ |inner ℝ (u 2) (v i)|) :
    ∃ f : Space ≃ᵃ[ℝ] Space,
      (∀ Q, volume (f '' Q) = ENNReal.ofReal (1 / (8 * A * B * c)) * volume Q) ∧
      (∀ i, f '' U i ⊆ ball (0 : Space) 1) ∧
      (∀ i, ball (f (z i)) (r / C) ⊆ f '' U i) ∧
      (∀ i, ∃ p ∈ f '' U i, ∃ q ∈ f '' U i, (1 / 16 : ℝ) ≤ dist p q) := by
  let s : Fin 3 → ℝ := ![A⁻¹, B⁻¹, (8 * c)⁻¹]
  have hs (j : Fin 3) : 0 < s j := by
    fin_cases j <;> dsimp [s] <;> positivity
  let f := coordinateAffine (tubeFrame u z₀) s (fun j => (hs j).ne')
  have hcoord (p : Space) (j : Fin 3) : f p j = s j * inner ℝ (u j) (p - z₀) := by
    simp only [f, coordinateAffine_apply, diagonalMap_apply, tubeFrame_symm_apply,
      OrthonormalBasis.repr_apply_apply]
  have hprod : (∏ j, s j) = 1 / (8 * A * B * c) := by
    simp [Fin.prod_univ_three, s]
    field_simp
    <;> ring
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · intro Q
    simpa only [hprod] using coordinateAffine_volume (tubeFrame u z₀) s hs Q
  · intro i p hp
    obtain ⟨q, hq, rfl⟩ := hp
    have hb := hbox i hq
    have hj (j : Fin 3) : |f q j| ≤ 1 / 4 := by
      rw [hcoord, abs_mul, abs_of_pos (hs j)]
      have hh := mul_le_mul_of_nonneg_left (hb j) (hs j).le
      fin_cases j
      · convert hh using 1 <;> dsimp [s] <;> field_simp <;> ring
      · convert hh using 1 <;> dsimp [s] <;> field_simp <;> ring
      · convert hh using 1 <;> dsimp [s] <;> field_simp <;> ring
    have hn := norm_le_coord_sum (f q)
    rw [mem_ball_zero_iff]
    linarith [hj 0, hj 1, hj 2]
  · have hlow (j : Fin 3) : C⁻¹ ≤ |s j| := by
      rw [abs_of_pos (hs j)]
      fin_cases j
      · exact inv_anti₀ hA hAC
      · exact inv_anti₀ hB hBC
      · exact inv_anti₀ (by positivity) hcC
    intro i p hp
    refine ⟨f.symm p, ?_, f.apply_symm_apply p⟩
    apply hball i
    have hl := coordinateAffine_dist_lower (tubeFrame u z₀) (fun j => (hs j).ne')
      (inv_pos.mpr hC).le hlow (f.symm p) (z i)
    change C⁻¹ * dist (f.symm p) (z i) ≤ dist (f (f.symm p)) (f (z i)) at hl
    rw [f.apply_symm_apply] at hl
    rw [mem_ball] at hp ⊢
    have hh := hl.trans_lt hp
    calc
      dist (f.symm p) (z i) = C * (C⁻¹ * dist (f.symm p) (z i)) := by field_simp
      _ < C * (r / C) := mul_lt_mul_of_pos_left hh hC
      _ = r := by field_simp
  · intro i
    let p := z i + (c / 2) • v i
    let q := z i - (c / 2) • v i
    refine ⟨f p, mem_image_of_mem f (hends i).1, f q,
      mem_image_of_mem f (hends i).2, ?_⟩
    have he : f p 2 - f q 2 = inner ℝ (u 2) (v i) / 8 := by
      rw [hcoord, hcoord]
      change (8 * c)⁻¹ * inner ℝ (u 2) (p - z₀) -
        (8 * c)⁻¹ * inner ℝ (u 2) (q - z₀) = _
      dsimp only [p, q]
      simp only [inner_sub_right, inner_add_right, inner_smul_right]
      field_simp
      ring
    have hn := PiLp.norm_apply_le (f p - f q) 2
    change ‖f p 2 - f q 2‖ ≤ ‖f p - f q‖ at hn
    rw [he, Real.norm_eq_abs, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 8)] at hn
    rw [dist_eq_norm]
    linarith [hlong i]

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
