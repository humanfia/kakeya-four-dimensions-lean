-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonflat_factored_improvement.SaturationPacking.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonflat_factored_improvement.AffineNet
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Packets

namespace WangZahlLot.Obl.wz_nonflat_factored_improvement

open MeasureTheory Set Metric

theorem prism_packing_bound {a b δ : ℝ} (ha : 0 < a) (hb : 0 < b) (hδ : 0 < δ)
    (e : AffineIsometryEquiv ℝ Space Space) {n : ℕ} (x v : Fin n → Space)
    (hv : ∀ i, ‖v i‖ = 1)
    (hover : ∀ i j, i ≠ j → volume (tube δ (x i) (v i) ∩ tube δ (x j) (v j)) ≤
      (1 / 2 : ENNReal) * volume (tube δ (x i) (v i))) :
    (Set.ncard {i | tube δ (x i) (v i) ⊆ e '' standardPrism a b} : ℝ) * δ ^ 4 ≤
      256000000 * (a * b) ^ 2 := by
  let W := e '' standardPrism a b
  let g := packetIndex δ x v W
  have hg := packetIndex_injective δ x v W
  have hW : volume W = ENNReal.ofReal (16 * a * b) := prism_volume ha.le hb.le ⟨e, rfl⟩
  have hWfin : volume W ≠ ⊤ := by rw [hW]; exact ENNReal.ofReal_ne_top
  have hh := WangZahlLot.Obl.wz_convex_container_tube_packing.packing hδ
    (fun i => x (g i)) (fun i => v (g i)) hWfin (fun i => hv (g i))
    (packetIndex_contained δ x v W) (fun i j hij => hover (g i) (g j) (hg.ne hij))
  rw [hW, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by norm_num)] at hh
  have hh' := (ENNReal.ofReal_le_ofReal_iff
    (by positivity : 0 ≤ (1000000 : ℝ) * (16 * a * b) ^ 2)).mp hh
  change (packetSize δ x v W : ℝ) * δ ^ 4 ≤ _ at hh'
  rw [packetSize_eq] at hh'
  dsimp [W] at hh'
  nlinarith only [hh']

theorem saturation_coefficient_bound {a b δ lam c : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hδ : 0 < δ) (hlam : 0 < lam)
    (e : AffineIsometryEquiv ℝ Space Space) {n : ℕ} (x v : Fin n → Space)
    (hv : ∀ i, ‖v i‖ = 1)
    (hover : ∀ i j, i ≠ j → volume (tube δ (x i) (v i) ∩ tube δ (x j) (v j)) ≤
      (1 / 2 : ENNReal) * volume (tube δ (x i) (v i)))
    (hsat : lam * c * a * b ≤
      (Set.ncard {i | tube δ (x i) (v i) ⊆ e '' standardPrism a b} : ℝ) * δ ^ 2) :
    c ≤ 256000000 * lam⁻¹ * (b / δ) ^ 2 := by
  have hb : 0 < b := ha.trans_le hab
  have hp := prism_packing_bound ha hb hδ e x v hv hover
  have hs := mul_le_mul_of_nonneg_right hsat (sq_nonneg δ)
  have hh : lam * c * a * b * δ ^ 2 ≤ 256000000 * (a * b) ^ 2 := by nlinarith only [hs, hp]
  have hc : c ≤ 256000000 * lam⁻¹ * (a * b / δ ^ 2) := by
    apply (mul_le_mul_iff_right₀ (by positivity : 0 < lam * a * b * δ ^ 2)).mp
    have he : (lam * a * b * δ ^ 2) * (256000000 * lam⁻¹ * (a * b / δ ^ 2)) =
        256000000 * (a * b) ^ 2 := by field_simp
    rw [he]
    nlinarith only [hh]
  apply hc.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [div_pow]
  exact div_le_div_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_right hab hb.le]) (sq_nonneg δ)

end WangZahlLot.Obl.wz_nonflat_factored_improvement
