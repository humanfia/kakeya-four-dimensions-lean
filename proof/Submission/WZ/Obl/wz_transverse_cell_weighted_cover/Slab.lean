-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_transverse_cell_weighted_cover.Slab.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_transverse_cell_weighted_cover.Basic

/-!
# Slabs

Volume of a slab in a ball, of the intersection of two slabs in a ball, and the separation of
the normals of two slabs that meet near two separated points.
-/

namespace WangZahlLot.Obl.wz_transverse_cell_weighted_cover

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

noncomputable section

/-- A slab of half-width `A` in a ball of radius `R`. -/
theorem slab_ball_volume_le {n y : Space} (hn : ‖n‖ = 1) {A R : ℝ} (hA : 0 ≤ A) (hR : 0 ≤ R) :
    volume ({q | |inner ℝ n (q - y)| ≤ A} ∩ ball y R) ≤ ENNReal.ofReal (8 * A * R ^ 2) := by
  obtain ⟨b, hb⟩ := WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.exists_basis_first hn
  have h := volume_le_of_coords b.orthonormal (fun _ => y) ![A, R, R]
    ({q | |inner ℝ n (q - y)| ≤ A} ∩ ball y R) ?_
  · convert h using 2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    ring
  · rintro q ⟨hq1, hq2⟩ k
    have hq1' : |inner ℝ n (q - y)| ≤ A := hq1
    have hqy : ‖q - y‖ < R := by rwa [mem_ball, dist_eq_norm] at hq2
    have hk : ∀ j : Fin 3, |inner ℝ (b j) (q - y)| ≤ R := by
      intro j
      calc |inner ℝ (b j) (q - y)| ≤ ‖b j‖ * ‖q - y‖ := abs_real_inner_le_norm _ _
        _ = ‖q - y‖ := by rw [b.norm_eq_one, one_mul]
        _ ≤ R := hqy.le
    fin_cases k
    · simpa [hb] using hq1'
    · simpa using hk 1
    · simpa using hk 2

/-- Two slabs of half-width `A` with normals at distance `s ∈ (0, 1]`, inside a ball of radius
`R`: volume at most `32 A² R / s`. -/
theorem two_slab_volume_le {n₁ n₂ y₁ y₂ : Space} (hn₁ : ‖n₁‖ = 1) (hn₂ : ‖n₂‖ = 1) {A R : ℝ}
    (hA : 0 ≤ A) (hR : 0 ≤ R) (hs : 0 < ‖n₁ - n₂‖) (hs1 : ‖n₁ - n₂‖ ≤ 1) :
    volume ({q | |inner ℝ n₁ (q - y₁)| ≤ A} ∩ {q | |inner ℝ n₂ (q - y₂)| ≤ A} ∩ ball y₁ R) ≤
      ENNReal.ofReal (32 * A ^ 2 * R / ‖n₁ - n₂‖) := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, inner ℝ n₁ n₂ = c := ⟨_, rfl⟩
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, ‖n₁ - n₂‖ = s := ⟨_, rfl⟩
  rw [hs_def] at hs hs1 ⊢
  have hc' : inner ℝ n₂ n₁ = c := by rw [real_inner_comm]; exact hc
  have hs2 : s ^ 2 = 2 - 2 * c := by
    rw [← hs_def, norm_sub_sq_real, hn₁, hn₂, hc]; ring
  have hc1 : |c| ≤ 1 := by
    have h := abs_real_inner_le_norm n₁ n₂
    rwa [hn₁, hn₂, hc, one_mul] at h
  -- the component of `n₂` orthogonal to `n₁`
  set m : Space := n₂ - c • n₁ with hm_def
  have hm_inner : inner ℝ n₁ m = 0 := by
    rw [hm_def, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hn₁, hc]
    ring
  have hm2 : ‖m‖ ^ 2 = 1 - c ^ 2 := by
    rw [hm_def, norm_sub_sq_real, norm_smul, real_inner_smul_right, hn₁, hn₂, hc',
      Real.norm_eq_abs, mul_one, sq_abs]
    ring
  set σ : ℝ := ‖m‖ with hσ_def
  have hσ0 : 0 ≤ σ := norm_nonneg _
  -- `σ² = s² (1 - s² / 4) ≥ s² / 4`
  have hσs : s / 2 ≤ σ := by
    have h1 : (s / 2) ^ 2 ≤ σ ^ 2 := by
      rw [hm2]
      have hc_eq : c = 1 - s ^ 2 / 2 := by linarith
      rw [hc_eq]
      have hs2' : s ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg s]
    exact (pow_le_pow_iff_left₀ (by linarith) hσ0 (by norm_num)).mp h1
  have hσ : 0 < σ := lt_of_lt_of_le (by linarith) hσs
  -- the unit vector along `m`
  set g : Space := σ⁻¹ • m with hg_def
  have hg : ‖g‖ = 1 := by
    rw [hg_def, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hσ, inv_mul_cancel₀ hσ.ne']
  have hn₁g : inner ℝ n₁ g = 0 := by
    rw [hg_def, real_inner_smul_right, hm_inner, mul_zero]
  have hn₂eq : n₂ = c • n₁ + σ • g := by
    rw [hg_def, smul_smul, mul_inv_cancel₀ hσ.ne', one_smul, hm_def]
    abel
  obtain ⟨w, hw⟩ := exists_frame hn₁ hg hn₁g
  clear_value g σ m
  set t : ℝ := inner ℝ n₂ (y₁ - y₂) with ht_def
  have h := volume_le_of_coords hw ![y₁, y₁, y₁ - (t / σ) • g] ![A, R, 2 * A / σ]
    ({q | |inner ℝ n₁ (q - y₁)| ≤ A} ∩ {q | |inner ℝ n₂ (q - y₂)| ≤ A} ∩ ball y₁ R) ?_
  · refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [show 8 * (A * R * (2 * A / σ)) = 16 * A ^ 2 * R / σ by ring,
      div_le_div_iff₀ hσ hs]
    have h0 : 0 ≤ 16 * A ^ 2 * R := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hσs h0]
  · rintro q ⟨⟨hq1, hq2⟩, hq3⟩ k
    have hq1' : |inner ℝ n₁ (q - y₁)| ≤ A := hq1
    have hq2' : |inner ℝ n₂ (q - y₂)| ≤ A := hq2
    have hqy : ‖q - y₁‖ < R := by rwa [mem_ball, dist_eq_norm] at hq3
    fin_cases k
    · simpa using hq1'
    · have hw1 : ‖w‖ = 1 := by simpa using hw.1 1
      have h := abs_real_inner_le_norm w (q - y₁)
      rw [hw1, one_mul] at h
      simpa using h.trans hqy.le
    · simp only [Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      -- the coordinate along `g`, measured from the shifted base point
      have key : σ * inner ℝ g (q - (y₁ - (t / σ) • g)) =
          inner ℝ n₂ (q - y₂) - c * inner ℝ n₁ (q - y₁) := by
        have e1 : q - (y₁ - (t / σ) • g) = (q - y₁) + (t / σ) • g := by abel
        have e2 : q - y₂ = (q - y₁) + (y₁ - y₂) := by abel
        rw [e1, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hg, e2,
          inner_add_right, ← ht_def, hn₂eq, inner_add_left, real_inner_smul_left,
          real_inner_smul_left]
        field_simp
        ring
      have hca : |c * inner ℝ n₁ (q - y₁)| ≤ A := by
        rw [abs_mul]
        calc |c| * |inner ℝ n₁ (q - y₁)| ≤ 1 * A :=
              mul_le_mul hc1 hq1' (abs_nonneg _) zero_le_one
          _ = A := one_mul A
      rw [le_div_iff₀ hσ, mul_comm, ← abs_of_pos hσ, ← abs_mul, abs_of_pos hσ, key]
      have a1 := abs_le.mp hca
      have a2 := abs_le.mp hq2'
      rw [abs_le]
      constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]

/-- If two slabs meet near `y₁`, the offset of `y₂` along the first normal is controlled by the
distance between the normals. -/
theorem inner_sep_of_meet {n₁ n₂ y₁ y₂ q : Space} {A R : ℝ}
    (h₁ : |inner ℝ n₁ (q - y₁)| ≤ A) (h₂ : |inner ℝ n₂ (q - y₂)| ≤ A) (hq : ‖q - y₁‖ ≤ R) :
    |inner ℝ n₁ (y₂ - y₁)| ≤ 2 * A + ‖n₁ - n₂‖ * (R + ‖y₂ - y₁‖) := by
  have e : inner ℝ n₁ (y₂ - y₁) =
      inner ℝ n₁ (q - y₁) - inner ℝ n₂ (q - y₂) - inner ℝ (n₁ - n₂) (q - y₂) := by
    have h : y₂ - y₁ = (q - y₁) - (q - y₂) := by abel
    rw [h, inner_sub_right, inner_sub_left]
    ring
  have h3 : |inner ℝ (n₁ - n₂) (q - y₂)| ≤ ‖n₁ - n₂‖ * (R + ‖y₂ - y₁‖) := by
    calc |inner ℝ (n₁ - n₂) (q - y₂)| ≤ ‖n₁ - n₂‖ * ‖q - y₂‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖n₁ - n₂‖ * (R + ‖y₂ - y₁‖) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        have h : q - y₂ = (q - y₁) - (y₂ - y₁) := by abel
        rw [h]
        exact (norm_sub_le _ _).trans (by linarith)
  rw [e, abs_le]
  have a1 := abs_le.mp h₁
  have a2 := abs_le.mp h₂
  have a3 := abs_le.mp h3
  constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2]

end

end WangZahlLot.Obl.wz_transverse_cell_weighted_cover
