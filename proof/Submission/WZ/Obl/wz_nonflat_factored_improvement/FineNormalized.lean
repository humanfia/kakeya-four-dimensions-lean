-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonflat_factored_improvement.FineNormalized.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonflat_factored_improvement.FineEstimate

namespace WangZahlLot.Obl.wz_nonflat_factored_improvement

open MeasureTheory Set Metric

noncomputable abbrev fineScaleConstant : ℝ :=
  (16 / fineContraction) ^ (-(3 / 2 : ℝ)) * (4 / fineContraction ^ 2)

theorem fineScaleConstant_pos : 0 < fineScaleConstant := by
  apply mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
  norm_num

theorem fine_scale_identity {a b δ m L N : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hδ : 0 < δ) (hm : 0 < m) (hL : 0 ≤ L) (hN : 0 ≤ N)
    (σ w A : ℝ) :
    A * (fineRadius δ b) ^ w * (16 * m / fineContraction)⁻¹ *
      (N * (fineRadius δ b) ^ 2) *
      ((16 * m / fineContraction) ^ (-(3 / 2 : ℝ)) *
        (L * N / (a * b * (fineContraction ^ 3 * b⁻¹ ^ 2))) * fineRadius δ b) ^ (-σ) =
    (fineContraction ^ 3 * b⁻¹ ^ 2) *
      ((A * (4 * fineContraction) ^ w * fineScaleConstant ^ (-σ)) * (δ / b) ^ w *
        m⁻¹ * (N * δ ^ 2) * (m ^ (-(3 / 2 : ℝ)) * L * (N * δ / a)) ^ (-σ)) := by
  have hκ : 0 < fineContraction := by norm_num
  have hr : fineRadius δ b = (4 * fineContraction) * (δ / b) := by
    dsimp [fineRadius]
    ring
  have hrpow : (fineRadius δ b) ^ w =
      (4 * fineContraction) ^ w * (δ / b) ^ w := by
    rw [hr, Real.mul_rpow (by positivity) (by positivity)]
  have hm' : 16 * m / fineContraction = (16 / fineContraction) * m := by ring
  have hbr : (16 * m / fineContraction) ^ (-(3 / 2 : ℝ)) *
        (L * N / (a * b * (fineContraction ^ 3 * b⁻¹ ^ 2))) * fineRadius δ b =
      fineScaleConstant * (m ^ (-(3 / 2 : ℝ)) * L * (N * δ / a)) := by
    rw [hm', Real.mul_rpow (by positivity) hm.le]
    dsimp [fineScaleConstant, fineRadius]
    field_simp
  have hbrpow : ((16 * m / fineContraction) ^ (-(3 / 2 : ℝ)) *
        (L * N / (a * b * (fineContraction ^ 3 * b⁻¹ ^ 2))) * fineRadius δ b) ^ (-σ) =
      fineScaleConstant ^ (-σ) * (m ^ (-(3 / 2 : ℝ)) * L * (N * δ / a)) ^ (-σ) := by
    rw [hbr, Real.mul_rpow fineScaleConstant_pos.le (by positivity)]
  have hfront : (16 * m / fineContraction)⁻¹ * (N * (fineRadius δ b) ^ 2) =
      (fineContraction ^ 3 * b⁻¹ ^ 2) * (m⁻¹ * (N * δ ^ 2)) := by
    dsimp [fineRadius]
    field_simp
    ring
  calc
    _ = (A * (fineRadius δ b) ^ w) *
        ((16 * m / fineContraction)⁻¹ * (N * (fineRadius δ b) ^ 2)) *
        ((16 * m / fineContraction) ^ (-(3 / 2 : ℝ)) *
          (L * N / (a * b * (fineContraction ^ 3 * b⁻¹ ^ 2))) * fineRadius δ b) ^ (-σ) := by ring
    _ = _ := by rw [hrpow, hfront, hbrpow]; ring

theorem ofReal_cancel_factor {J F : ℝ} (hJ : 0 < J) {V : ENNReal}
    (h : ENNReal.ofReal (J * F) ≤ ENNReal.ofReal J * V) : ENNReal.ofReal F ≤ V := by
  have hJ0 : ENNReal.ofReal J ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hJ)
  calc
    _ = (ENNReal.ofReal J)⁻¹ * ENNReal.ofReal (J * F) := by
      rw [ENNReal.ofReal_mul hJ.le, ← mul_assoc,
        ENNReal.inv_mul_cancel hJ0 ENNReal.ofReal_ne_top, one_mul]
    _ ≤ (ENNReal.ofReal J)⁻¹ * (ENNReal.ofReal J * V) := mul_le_mul' le_rfl h
    _ = V := by rw [← mul_assoc, ENNReal.inv_mul_cancel hJ0 ENNReal.ofReal_ne_top, one_mul]

/-- The fine estimate expressed in the original volume units. -/
theorem fine_estimate_normalized {σ u : ℝ} (hE : EstimateE σ u) {ε : ℝ} (hε : 0 < ε) :
    ∃ A η : ℝ, 0 < A ∧ 0 < η ∧
      ∀ a b δ lam m L : ℝ, 0 < δ → δ ≤ a → a ≤ b → b ≤ 1 →
      1 ≤ m → 1 ≤ L → 0 ≤ lam →
      (fineRadius δ b) ^ η ≤ fineContraction * lam / 16 →
      ∀ (e : AffineIsometryEquiv ℝ Space Space) (n : ℕ) (x v : Fin n → Space)
        (Y : Fin n → Set Space),
      0 < n → (∀ i, ‖v i‖ = 1) → (∀ i, tube δ (x i) (v i) ⊆ e '' standardPrism a b) →
      (∀ i j, i ≠ j → volume (tube δ (x i) (v i) ∩ tube δ (x j) (v j)) ≤
        (1 / 2 : ENNReal) * volume (tube δ (x i) (v i))) →
      (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ tube δ (x i) (v i)) →
      (∀ i, ENNReal.ofReal (lam * δ ^ 2) ≤ volume (Y i)) → ConvexCount δ m x v →
      (∀ U : Set Space, Convex ℝ U →
        ENNReal.ofReal ((Set.ncard {i | tube δ (x i) (v i) ⊆ U} : ℝ) * (a * b)) ≤
          ENNReal.ofReal (L * n) * volume U) →
      ENNReal.ofReal (A * (δ / b) ^ (u + ε) * m⁻¹ * ((n : ℝ) * δ ^ 2) *
        (m ^ (-(3 / 2 : ℝ)) * L * ((n : ℝ) * δ / a)) ^ (-σ)) ≤ volume (⋃ i, Y i) := by
  obtain ⟨A, η, hA, hη, H⟩ := fine_estimate hE hε
  refine ⟨A * (4 * fineContraction) ^ (u + ε) * fineScaleConstant ^ (-σ), η,
    by positivity, hη, ?_⟩
  intro a b δ lam m L hδ hδa hab hb1 hm hL hlam hden e n x v Y
    hn hv hT hover hYm hYT hind hconv hrel
  have ha : 0 < a := hδ.trans_le hδa
  have hb : 0 < b := ha.trans_le hab
  have hh := H a b δ lam m L hδ hδa hab hb1 hm hL hlam hden e n x v Y
    hn hv hT hover hYm hYT hind hconv hrel
  rw [fine_scale_identity ha hb hδ (zero_lt_one.trans_le hm)
    (zero_le_one.trans hL) (Nat.cast_nonneg n)] at hh
  exact ofReal_cancel_factor (by positivity) hh

end WangZahlLot.Obl.wz_nonflat_factored_improvement
