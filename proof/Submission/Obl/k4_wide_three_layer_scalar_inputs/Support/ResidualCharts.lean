import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.ResidualGeometry
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.ResidualTarget
import Submission.Obl.k4_conditional_common_affine_field.GridField

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

open Set
open MeasureTheory Filter
open Submission.Obl.k4_critical_conditional_row_preparation

noncomputable section

/-- A fine output base cell and a fine original velocity bin meet only subpower many
original charts. The estimate uses the actual physical time interval. -/
theorem residual_chart_menu (F : Frame) {K σ δv χ : ℝ}
    (hK : 1 ≤ K) (hq : 0 < F.q) (hσ : 0 < σ) (hδv : 0 < δv) (hχ : 0 < χ)
    (hχ₁ : χ ≤ 1) (hqσ : F.q * σ ≤ χ) (hδχ : δv ≤ χ) (hc₁ : |F.c 1| ≤ K)
    (z : Fin 2 → ℤ) (w : ℤ) :
    ∃ Ch : Finset (ℤ × ℤ), (Ch.card : ℝ) ≤ 48 * K ∧
      ∀ (b : Fin 6 → ℝ) (t : ℝ), t ∈ Icc (0 : ℝ) 1 → |b 3| ≤ K →
        (![⌊F.zt t / σ⌋, ⌊F.zZ b t / σ⌋] : Fin 2 → ℤ) = z →
        vbin δv (b 3) = w → (⌊b 3 / χ⌋, ⌊b 0 / χ⌋) ∈ Ch := by
  classical
  let tt := F.t₀ + F.q * ((z 0 : ℝ) * σ)
  let vc := (w : ℝ) * δv
  let center := F.c 0 + tt * F.c 1 + F.q * ((z 1 : ℝ) * σ) - tt * vc
  let V := floorBand χ vc δv
  let Z := floorBand χ center ((2 * K + 3) * χ)
  have hK₀ : 0 ≤ K := zero_le_one.trans hK
  have hV : (V.card : ℝ) ≤ 4 := by
    have hdiv : δv / χ ≤ 1 := (div_le_one hχ).mpr hδχ
    apply (floorBand_card hχ hδv.le).trans
    rw [mul_div_assoc]
    linarith
  have hZ : (Z.card : ℝ) ≤ 12 * K := by
    calc
      _ ≤ 2 * ((2 * K + 3) * χ) / χ + 2 := floorBand_card hχ (by positivity)
      _ = 4 * K + 8 := by field_simp; ring
      _ ≤ _ := by linarith
  refine ⟨V ×ˢ Z, ?_, ?_⟩
  · rw [Finset.card_product, Nat.cast_mul]
    exact (mul_le_mul hV hZ (by positivity) (by norm_num)).trans_eq (by ring)
  · intro b t ht hb hbase hw
    have ht₁ : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    have h0 : ⌊F.zt t / σ⌋ = z 0 := by have h := congrFun hbase 0; simpa using h
    have h1 : ⌊F.zZ b t / σ⌋ = z 1 := by have h := congrFun hbase 1; simpa using h
    have hτ := Submission.Obl.k4_conditional_common_affine_field.abs_sub_floor_mul_le hσ h0
    have hZnorm := Submission.Obl.k4_conditional_common_affine_field.abs_sub_floor_mul_le hσ h1
    have hv := Submission.Obl.k4_conditional_common_affine_field.abs_sub_floor_mul_le hδv hw
    have htime : |t - tt| ≤ F.q * σ := by
      have hid : t - tt = F.q * (F.zt t - (z 0 : ℝ) * σ) := by
        dsimp only [tt]
        unfold Frame.zt
        field_simp
        ring
      rw [hid, abs_mul, abs_of_pos hq]
      exact mul_le_mul_of_nonneg_left hτ hq.le
    have htt : |tt| ≤ 2 := by
      calc
        _ = |t - (t - tt)| := by congr 1; ring
        _ ≤ |t| + |t - tt| := abs_sub _ _
        _ ≤ 1 + F.q * σ := add_le_add ht₁ htime
        _ ≤ _ := by linarith
    have hvel : |F.c 1 - b 3| ≤ 2 * K := (abs_sub _ _).trans (by linarith)
    have hintercept : |b 0 - center| ≤ (2 * K + 3) * χ := by
      have hid : b 0 - center = (t - tt) * (F.c 1 - b 3) +
          F.q * (F.zZ b t - (z 1 : ℝ) * σ) - tt * (b 3 - vc) := by
        dsimp only [center]
        unfold Frame.zZ
        field_simp
        ring
      rw [hid]
      calc
        _ ≤ |t - tt| * |F.c 1 - b 3| + F.q * |F.zZ b t - (z 1 : ℝ) * σ| +
            |tt| * |b 3 - vc| := by
          simpa only [abs_mul, abs_of_pos hq] using
            (abs_sub ((t - tt) * (F.c 1 - b 3) + F.q * (F.zZ b t - (z 1 : ℝ) * σ))
              (tt * (b 3 - vc))).trans
                (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ (F.q * σ) * (2 * K) + F.q * σ + 2 * δv := by gcongr
        _ ≤ χ * (2 * K) + χ + 2 * χ := by gcongr
        _ = _ := by ring
    exact Finset.mem_product.mpr ⟨mem_floorBand hχ hv, mem_floorBand hχ hintercept⟩

/-- The same menu bound expressed directly for an original incidence law. -/
theorem residual_chart_menus_ae {α : Type} [MeasurableSpace α]
    (F : Frame) (b : α → Fin 6 → ℝ) (θ : Measure (α × ℝ)) {K σ δv χ : ℝ}
    (hK : 1 ≤ K) (hq : 0 < F.q) (hσ : 0 < σ) (hδv : 0 < δv) (hχ : 0 < χ)
    (hχ₁ : χ ≤ 1) (hqσ : F.q * σ ≤ χ) (hδχ : δv ≤ χ) (hc₁ : |F.c 1| ≤ K)
    (htime : ∀ᵐ p ∂θ, p.2 ∈ Icc (0 : ℝ) 1) (hvel : ∀ᵐ p ∂θ, |b p.1 3| ≤ K) :
    ∀ (z : Fin 2 → ℤ) (w : ℤ), ∃ Ch : Finset (ℤ × ℤ), (Ch.card : ℝ) ≤ 48 * K ∧
      ∀ᵐ p ∂θ, (![⌊F.zt p.2 / σ⌋, ⌊F.zZ (b p.1) p.2 / σ⌋] : Fin 2 → ℤ) = z →
        vbin δv (b p.1 3) = w → (⌊b p.1 3 / χ⌋, ⌊b p.1 0 / χ⌋) ∈ Ch := by
  intro z w
  obtain ⟨Ch, hcard, hmem⟩ := residual_chart_menu F hK hq hσ hδv hχ hχ₁ hqσ hδχ hc₁ z w
  refine ⟨Ch, hcard, ?_⟩
  filter_upwards [htime, hvel] with p ht hv
  exact hmem (b p.1) p.2 ht hv

/-- The fixed output and velocity horizons may both be chosen above the original
chart horizon. Every dyadic true-block length is at most one. -/
theorem residual_chart_menus_at {α : Type} [MeasurableSpace α]
    (F : Frame) (b : α → Fin 6 → ℝ) (θ : Measure (α × ℝ))
    {N K M m v' : ℝ} (hN : 1 ≤ N) (hK : 1 ≤ K) (hq : 0 < F.q) (hq₁ : F.q ≤ 1)
    (hM : 0 ≤ M) (hm : M ≤ m) (hv' : M ≤ v') (hc₁ : |F.c 1| ≤ K)
    (htime : ∀ᵐ p ∂θ, p.2 ∈ Icc (0 : ℝ) 1) (hvel : ∀ᵐ p ∂θ, |b p.1 3| ≤ K) :
    ∀ (z : Fin 2 → ℤ) (w : ℤ), ∃ Ch : Finset (ℤ × ℤ), (Ch.card : ℝ) ≤ 48 * K ∧
      ∀ᵐ p ∂θ,
        (![⌊F.zt p.2 / (N ^ (-m))⌋, ⌊F.zZ (b p.1) p.2 / (N ^ (-m))⌋] : Fin 2 → ℤ) = z →
        vbin (N ^ (-v')) (b p.1 3) = w →
          (⌊b p.1 3 / (N ^ (-M))⌋, ⌊b p.1 0 / (N ^ (-M))⌋) ∈ Ch := by
  have hN₀ : 0 < N := zero_lt_one.trans_le hN
  apply residual_chart_menus_ae F b θ hK hq
    (Real.rpow_pos_of_pos hN₀ _) (Real.rpow_pos_of_pos hN₀ _) (Real.rpow_pos_of_pos hN₀ _)
    (Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith))
    _ (Real.rpow_le_rpow_of_exponent_le hN (by linarith)) hc₁ htime hvel
  calc
    _ ≤ 1 * N ^ (-m) := mul_le_mul_of_nonneg_right hq₁ (Real.rpow_nonneg hN₀.le _)
    _ ≤ N ^ (-M) := by
      rw [one_mul]
      exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
