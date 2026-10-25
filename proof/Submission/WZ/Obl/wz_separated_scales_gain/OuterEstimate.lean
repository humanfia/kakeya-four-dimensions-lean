-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_scales_gain.OuterEstimate.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_scales_gain.OuterNet
import Submission.WZ.Obl.wz_separated_scales_gain.Counts
import Submission.WZ.Obl.wz_separated_scales_gain.Weight

namespace WangZahlLot.Obl.wz_separated_scales_gain

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_nonflat_factored_improvement

/-- The outer Frostman family satisfies the normalized `E` bound even when its tubes
lie only in the fixed ambient ball containing all the parent tubes. -/
theorem outer_estimate {σ u : ℝ} (hσ : 0 ≤ σ) (hE : EstimateE σ u)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A η : ℝ, 0 < A ∧ 0 < η ∧
      ∀ δ lam L : ℝ, 0 < δ → δ ≤ 1 → 0 ≤ lam → 1 ≤ L →
      (fineRadius δ 1) ^ η ≤ fineContraction * lam / 16 →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      0 < n → (∀ i, ‖v i‖ = 1) →
      (∀ i, tube δ (x i) (v i) ⊆ ball (0 : Space) 5) →
      (∀ i j, i ≠ j → volume (tube δ (x i) (v i) ∩ tube δ (x j) (v j)) ≤
        (1 / 2 : ENNReal) * volume (tube δ (x i) (v i))) →
      (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ tube δ (x i) (v i)) →
      (∀ i, ENNReal.ofReal (lam * δ ^ 2) ≤ volume (Y i)) → RelativeCount 1 L δ x v →
      ENNReal.ofReal (A * δ ^ (u + ε) * L⁻¹ * ((n : ℝ) * δ ^ 4) ^ (σ / 2)) ≤
        volume (⋃ i, Y i) := by
  obtain ⟨A, hA, η, hη, H⟩ := hE ε hε
  let B := A * retainedFraction * (4 * fineContraction) ^ (u + ε) * fineScaleConstant ^ (-σ)
  have hB : 0 < B := by dsimp [B]; have := retainedFraction_pos; have := fineScaleConstant_pos; positivity
  refine ⟨B / 56, η, by positivity, hη, ?_⟩
  intro δ lam L hδ hδ1 hlam hL hden n x v Y hn hv hball hover hYm hYT hind hrel
  have hκ : 0 < fineContraction := by norm_num
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  let r := fineRadius δ 1
  let J := fineContraction ^ 3
  let m := 56 * L * n * δ ^ 2
  let m' := 16 * m / fineContraction
  have hr : 0 < r := by dsimp [r, fineRadius]; positivity
  have hr100 : r ≤ 1 / 100 := by dsimp [r, fineRadius, fineContraction]; norm_num; linarith
  have hJ : 0 < J := by dsimp [J]; positivity
  have hm : 1 ≤ m := by
    simpa only [div_one] using relative_coefficient_lower (by norm_num : (0 : ℝ) < 1)
      hL0.le hδ hδ1 hn hv hrel
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  have hm' : 1 ≤ m' := by dsimp [m', fineContraction]; linarith
  have hconv : ConvexCount δ m x v := by
    apply convexCount_mono _ (convexCount_of_relative (by norm_num : (0 : ℝ) < 1) hrel)
    dsimp [m]
    simp only [div_one]
    have hh : 0 ≤ L * n * δ ^ 2 := by positivity
    nlinarith only [hh]
  obtain ⟨M, j, z, w, hM, hj, hw, hball', hsep, hcover, hsize⟩ :=
    outer_tube_net hδ hδ1 hn x v hv hball hover
  have hMc : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  have hMn : (M : ℝ) ≤ n := by exact_mod_cast (show M ≤ n by simpa using Fintype.card_le_of_injective j hj)
  let l := (L * n / J) / M
  have hl : 1 ≤ l := by
    apply (le_div_iff₀ hMc).mpr
    apply (le_div_iff₀ hJ).mpr
    have hJ1 : J ≤ 1 := by norm_num [J]
    have hh := mul_le_mul_of_nonneg_left hJ1 hMc.le
    have hh' := mul_le_mul_of_nonneg_right hL (Nat.cast_nonneg n)
    nlinarith only [hh, hh', hMn]
  let Z : Fin M → Set Space := fun i => outerAffine '' Y (j i)
  have hZmeas : ∀ i, MeasurableSet (Z i) := fun i =>
    outerAffine.toContinuousAffineEquiv.toHomeomorph.measurableEmbedding.measurableSet_image.mpr (hYm (j i))
  have hZsub : ∀ i, Z i ⊆ tube r (z i) (w i) :=
    fun i => (image_mono (hYT (j i))).trans (hcover i)
  have hZden : ∀ i, ENNReal.ofReal (r ^ η * r ^ 2) ≤ volume (Z i) := by
    intro i
    rw [show volume (Z i) = ENNReal.ofReal J * volume (Y (j i)) from outerAffine_volume _]
    calc
      _ ≤ ENNReal.ofReal ((fineContraction * lam / 16) * r ^ 2) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hden (sq_nonneg r))
      _ = ENNReal.ofReal J * ENNReal.ofReal (lam * δ ^ 2) := by
        rw [← ENNReal.ofReal_mul hJ.le]
        congr 1
        simp only [r, J, fineRadius, inv_one, mul_one]
        ring
      _ ≤ _ := mul_le_mul' le_rfl (hind (j i))
  have hrawconv := affine_count_transport outerAffine hJ (sq_pos_of_pos hδ) hm0.le
    outerAffine_volume x v z w j hj hcover hconv
  have hc : ConvexCount r m' z w := by
    have hh := convexCount_of_raw_count (by positivity : 0 ≤ m / (δ ^ 2 * J)) z w hrawconv
    have he : m / (δ ^ 2 * J) * r ^ 2 = m' := by
      dsimp [r, J, m', fineRadius]
      field_simp
      ring
    rwa [he] at hh
  have hrawrel := affine_count_transport outerAffine hJ (by norm_num : (0 : ℝ) < 1 ^ 2)
    (by positivity : 0 ≤ L * n) outerAffine_volume x v z w j hj hcover hrel
  have hs : SlabCount r l z w := by
    simpa only [one_pow, one_mul] using slabCount_of_raw_count hM z w hrawrel
  have hbound := H r hr hr100 m' l hm' hl M z w Z hM hw hball' hsep hZmeas hZsub
    (subfamily_density hr.le (fun i => i) hZden) hc hs
  have hU : volume (⋃ i, Z i) ≤ ENNReal.ofReal J * volume (⋃ i, Y i) := by
    rw [← outerAffine_volume]
    apply measure_mono
    intro p hp
    obtain ⟨i, q, hq, rfl⟩ := mem_iUnion.mp hp
    exact ⟨q, mem_iUnion.mpr ⟨j i, hq⟩, rfl⟩
  have hlprod : m' ^ (-(3 / 2 : ℝ)) * l * ((M : ℝ) * r) =
      m' ^ (-(3 / 2 : ℝ)) * (L * n / J) * r := by dsimp [l]; field_simp
  dsimp only at hbound
  rw [hlprod] at hbound
  have hsmall : ENNReal.ofReal ((A * retainedFraction) * r ^ (u + ε) * m'⁻¹ *
      ((n : ℝ) * r ^ 2) * (m' ^ (-(3 / 2 : ℝ)) * (L * n / J) * r) ^ (-σ)) ≤
      ENNReal.ofReal J * volume (⋃ i, Y i) := by
    apply le_trans (b := ENNReal.ofReal (A * r ^ (u + ε) * m'⁻¹ * ((M : ℝ) * r ^ 2) *
      (m' ^ (-(3 / 2 : ℝ)) * (L * n / J) * r) ^ (-σ))) _ (hbound.trans hU)
    apply ENNReal.ofReal_le_ofReal
    have hh := mul_le_mul_of_nonneg_left hsize (by positivity :
      0 ≤ A * r ^ (u + ε) * m'⁻¹ * r ^ 2 *
        (m' ^ (-(3 / 2 : ℝ)) * (L * n / J) * r) ^ (-σ))
    nlinarith only [hh]
  have hscale := fine_scale_identity (a := 1) (b := 1) (δ := δ) (m := m) (L := L) (N := n)
    (by norm_num) (by norm_num) hδ hm0 hL0.le (Nat.cast_nonneg n) σ (u + ε) (A * retainedFraction)
  simp only [inv_one, one_pow, mul_one, one_mul, div_one] at hscale
  change _ = J * (B * δ ^ (u + ε) * m⁻¹ * ((n : ℝ) * δ ^ 2) *
    (m ^ (-(3 / 2 : ℝ)) * L * ((n : ℝ) * δ)) ^ (-σ)) at hscale
  rw [hscale] at hsmall
  have hnormal := ofReal_cancel_factor hJ hsmall
  apply (ENNReal.ofReal_le_ofReal ?_).trans hnormal
  have hwgt := frostman_weight_lower (C := 56) (by norm_num) hL (Nat.cast_pos.mpr hn) hδ hσ
  have hh := mul_le_mul_of_nonneg_left hwgt (by positivity : 0 ≤ B * δ ^ (u + ε))
  dsimp [m]
  convert hh using 1 <;> ring

end WangZahlLot.Obl.wz_separated_scales_gain
