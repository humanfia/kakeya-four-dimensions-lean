-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_rescaled_fibre_alternatives.PowerLoss.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.DenseSelection

namespace WangZahlLot.Obl.wz_rescaled_fibre_alternatives

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_nonflat_factored_improvement (power_density_bound exists_small_rpow)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (axis)

lemma count_power_absorption {d θ ν C : ℝ} (hd : 0 < d) (hd1 : d ≤ 1)
    (hν : ν ≤ θ / 2) (hC : 0 < C) (hc : d ^ (θ / 2) ≤ C⁻¹) :
    C * d ^ (-ν) ≤ d ^ (-θ) := by
  have hh := power_density_bound hd hd1 hν hc
  rw [Real.rpow_neg hd.le, Real.rpow_neg hd.le, ← div_eq_mul_inv, inv_eq_one_div]
  apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hd _) (Real.rpow_pos_of_pos hd _)).mpr
  have h := mul_le_mul_of_nonneg_left hh hC.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hC.ne', one_mul] using h

lemma selected_mass {s lam L : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (hlam : 0 < lam) (hL : 0 < L) {n M : ℕ}
    (x v : Fin n → Space) (Y : Fin n → Set Space) (j : Fin M → Fin n)
    (hv : ∀ i, ‖v i‖ = 1) (hYT : ∀ i, Y i ⊆ tube s (x i) (v i))
    (hden : ∀ i, ENNReal.ofReal (lam / 2 * s ^ 2) ≤ volume (Y (j i)))
    (hcard : selectedFraction * (lam / L) * n ≤ (M : ℝ)) :
    ENNReal.ofReal (selectedFraction * lam ^ 2 / (112 * L)) * (∑ i, volume (Y i)) ≤
      ∑ i, volume (Y (j i)) := by
  have hup : (∑ i, volume (Y i)) ≤ ENNReal.ofReal (56 * n * s ^ 2) := by
    calc
      _ ≤ ∑ _i : Fin n, ENNReal.ofReal (56 * s ^ 2) := Finset.sum_le_sum fun i _ =>
        (measure_mono (hYT i)).trans
          (WangZahlLot.Obl.wz_nonflat_factored_improvement.tube_volume_upper hs.le hs1 _ _ (hv i))
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
        congr 1
        ring
  have hlo : ENNReal.ofReal (lam / 2 * M * s ^ 2) ≤ ∑ i, volume (Y (j i)) := by
    calc
      _ = ∑ _i : Fin M, ENNReal.ofReal (lam / 2 * s ^ 2) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg M)]
        congr 1
        ring
      _ ≤ _ := Finset.sum_le_sum fun i _ => hden i
  calc
    _ ≤ ENNReal.ofReal (selectedFraction * lam ^ 2 / (112 * L)) *
        ENNReal.ofReal (56 * n * s ^ 2) := mul_le_mul_right hup _
    _ = ENNReal.ofReal (lam / 2 * (selectedFraction * (lam / L) * n) * s ^ 2) := by
      rw [← ENNReal.ofReal_mul (by have := selectedFraction_pos; positivity)]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (lam / 2 * M * s ^ 2) := by
      apply ENNReal.ofReal_le_ofReal
      gcongr
    _ ≤ _ := hlo

lemma radius_eq_ratio (r s : ℝ) : normalizedRadius r s = (4 * contraction) * (s / r) := by
  dsimp [normalizedRadius]
  ring

lemma normalize_with_power_loss {θ : ℝ} (hθ : 0 < θ) :
    ∃ η₀ c : ℝ, 0 < η₀ ∧ 0 < c ∧ c ≤ 1 ∧
      ∀ η r s : ℝ, 0 < η → η ≤ η₀ → 0 < s → s ≤ c * r → r ≤ 1 →
      ∀ (y w : Space) (e : Space ≃ₗᵢ[ℝ] Space), ‖w‖ = 1 → e w = axis →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Fibre r s η y w x v Y → ∃ hr : 0 < r,
      ∃ (M : ℕ) (j : Fin M → Fin n) (z u : Fin M → Space),
        Function.Injective j ∧
        Admissible (normalizedRadius r s) θ ((normalizedRadius r s) ^ (-θ))
          ((normalizedRadius r s) ^ (-θ)) z u (fun i => normalize e y w r hr '' Y (j i)) ∧
        (∀ i, normalize e y w r hr '' tube s (x (j i)) (v (j i)) ⊆
          tube (normalizedRadius r s) (z i) (u i)) ∧
        (∀ i, z i + (1 / 2 : ℝ) • u i = normalize e y w r hr (x (j i) + (1 / 2 : ℝ) • v (j i))) ∧
        (normalizedRadius r s) ^ θ * n ≤ (M : ℝ) ∧
        ENNReal.ofReal ((normalizedRadius r s) ^ θ) * (∑ i, volume (Y i)) ≤
          ∑ i, volume (Y (j i)) := by
  let b := min (contraction / 32) (min (selectedFraction / 112)
    (min (contraction / 16) (contraction ^ 3 * selectedFraction)))
  have hb : 0 < b := by
    have := selectedFraction_pos
    dsimp [b, contraction]
    positivity
  obtain ⟨c₀, hc₀, Hc⟩ := exists_small_rpow (by positivity : 0 < θ / 2) hb
  let c := min 1 c₀
  have hc : 0 < c := lt_min one_pos hc₀
  refine ⟨θ / 12, c, by positivity, hc, min_le_left _ _, ?_⟩
  intro η r s hη hηθ hs hsr hr1 y w e hw hew n x v Y hF
  have hr : 0 < r := (mul_pos_iff_of_pos_left hc).mp (hs.trans_le hsr)
  have hd : 0 < s / r := div_pos hs hr
  have hdc : s / r ≤ c := (div_le_iff₀ hr).mpr hsr
  have hd1 : s / r ≤ 1 := hdc.trans (min_le_left _ _)
  have hsr' : s ≤ r := (div_le_one hr).mp hd1
  have hsmall : (s / r) ^ (θ / 2) ≤ b := Hc _ hd (hdc.trans (min_le_right _ _))
  have hn : 0 < n := hF.1
  have hlam : 0 < (s / r) ^ η := Real.rpow_pos_of_pos hd _
  have hL : 0 < (s / r) ^ (-η) := Real.rpow_pos_of_pos hd _
  obtain ⟨M, j, z, u, hM, hj, hu, hball, hsep, hcover, hmid, hden, hcard⟩ :=
    normalize_dense e hew hr hr1 hs hsr' hL hlam hn x v Y
      (fun i => (hF.2.1 i).1) (fun i => (hF.2.1 i).2.1) (fun i => (hF.2.1 i).2.2.2)
      hF.2.2.1 hF.2.2.2.1
  have hR : 0 < normalizedRadius r s := normalizedRadius_pos hr hs
  have hRle : normalizedRadius r s ≤ s / r := by
    rw [radius_eq_ratio]
    exact mul_le_of_le_one_left hd.le (by norm_num)
  have hpow : (normalizedRadius r s) ^ θ ≤ (s / r) ^ θ :=
    Real.rpow_le_rpow hR.le hRle hθ.le
  have hpowneg : (s / r) ^ (-θ) ≤ (normalizedRadius r s) ^ (-θ) :=
    Real.rpow_le_rpow_of_nonpos hR hRle (by linarith)
  have hdensity : (normalizedRadius r s) ^ θ ≤ contraction * ((s / r) ^ η / 2) / 16 := by
    have hh := power_density_bound hd hd1 (by linarith : η ≤ θ / 2)
      (hsmall.trans (min_le_left _ _))
    convert hpow.trans hh using 1 <;> ring
  have hcard' : (s / r) ^ θ * n ≤ (M : ℝ) := by
    have hh := power_density_bound hd hd1 (by linarith : 2 * η ≤ θ / 2)
      (hsmall.trans ((min_le_right _ _).trans (min_le_left _ _)))
    have he : (s / r) ^ η / (s / r) ^ (-η) = (s / r) ^ (2 * η) := by
      rw [← Real.rpow_sub hd]
      congr 1
      ring
    rw [he] at hcard
    have hb1 : selectedFraction / 112 ≤ selectedFraction := by have := selectedFraction_pos; linarith
    exact (mul_le_mul_of_nonneg_right (hh.trans
      (mul_le_mul_of_nonneg_right hb1 (Real.rpow_nonneg hd.le _))) (Nat.cast_nonneg n)).trans hcard
  have hmraw := normalized_convex_count e y w hr hs hL.le x v z u j hj hcover hF.2.2.2.1
  have hmle : 16 * (s / r) ^ (-η) / contraction ≤ (normalizedRadius r s) ^ (-θ) := by
    have hh := count_power_absorption hd hd1 (by linarith : η ≤ θ / 2)
      (by norm_num : 0 < 16 / contraction)
      (by convert hsmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))) using 1 <;> norm_num)
    convert hh.trans hpowneg using 1 <;> ring
  have hsraw := normalized_slab_count e hew hw hr hr1 hM x v z u j hj
    (fun i => (hF.2.1 i).2.1) hcover hF.2.2.2.2
  have hlle : (s / r) ^ (-η) * n / (contraction ^ 3 * M) ≤
      (normalizedRadius r s) ^ (-θ) := by
    have hcoef : (s / r) ^ (-η) * n / (contraction ^ 3 * M) ≤
        (contraction ^ 3 * selectedFraction)⁻¹ * (s / r) ^ (-(3 * η)) := by
      have hMc : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
      apply (div_le_iff₀ (by positivity : 0 < contraction ^ 3 * M)).mpr
      have hfrac : (s / r) ^ η / (s / r) ^ (-η) = (s / r) ^ (2 * η) := by
        rw [← Real.rpow_sub hd]
        congr 1
        ring
      have hcard2 := hcard
      rw [hfrac] at hcard2
      have he : (s / r) ^ (-(3 * η)) * (s / r) ^ (2 * η) = (s / r) ^ (-η) := by
        rw [← Real.rpow_add hd]
        congr 1
        ring
      calc
        (s / r) ^ (-η) * n = ((s / r) ^ (-(3 * η)) / selectedFraction) *
            (selectedFraction * (s / r) ^ (2 * η) * n) := by
              rw [← he]
              field_simp [selectedFraction_pos.ne']
        _ ≤ ((s / r) ^ (-(3 * η)) / selectedFraction) * M :=
          mul_le_mul_of_nonneg_left hcard2 (div_nonneg (Real.rpow_nonneg hd.le _) selectedFraction_pos.le)
        _ = _ := by field_simp
    have hh := count_power_absorption hd hd1 (by linarith : 3 * η ≤ θ / 2)
      (by have := selectedFraction_pos; positivity : 0 < (contraction ^ 3 * selectedFraction)⁻¹)
      (by simpa only [inv_inv] using (hsmall.trans
        ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
    exact hcoef.trans (hh.trans hpowneg)
  refine ⟨hr, M, j, z, u, hj, ?_, hcover, hmid,
    (mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg n)).trans hcard', ?_⟩
  · refine ⟨hM, fun i => ⟨hu i, hball i, ?_, (Set.image_mono (hF.2.1 (j i)).2.2.2).trans (hcover i)⟩,
      hsep, normalized_density e y w hr hs (div_nonneg hlam.le (by norm_num)) _ hden hdensity,
      convexCount_mono hmle hmraw, ?_⟩
    · exact (normalize e y w r hr).toHomeomorph.measurableEmbedding.measurableSet_image.mpr (hF.2.1 (j i)).2.2.1
    · intro a t ρ ha hρ
      exact (hsraw a t ρ ha hρ).trans (mul_le_mul_left
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hlle (Nat.cast_nonneg M))) _)
  · have hmass := selected_mass hs (hsr'.trans hr1) hlam hL x v Y j
      (fun i => (hF.2.1 i).1) (fun i => (hF.2.1 i).2.2.2) hden hcard
    have he : selectedFraction * ((s / r) ^ η) ^ 2 / (112 * (s / r) ^ (-η)) =
        (selectedFraction / 112) * (s / r) ^ (3 * η) := by
      calc
        _ = (selectedFraction / 112) * (((s / r) ^ η) ^ 2 / (s / r) ^ (-η)) := by ring
        _ = _ := by
          rw [← Real.rpow_mul_natCast hd.le, ← Real.rpow_sub hd]
          congr 1
          norm_num
          ring
    rw [he] at hmass
    have hh := power_density_bound hd hd1 (by linarith : 3 * η ≤ θ / 2)
      (hsmall.trans ((min_le_right _ _).trans (min_le_left _ _)))
    exact (mul_le_mul_left (ENNReal.ofReal_le_ofReal (hpow.trans hh)) _).trans hmass

end WangZahlLot.Obl.wz_rescaled_fibre_alternatives
