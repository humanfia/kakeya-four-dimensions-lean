-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_translation_model.Coefficient.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nsp_translation_model.Counting
import Submission.WZ.Obl.wz_affine_packet_counting_transfer

namespace WangZahlLot.Obl.wz_nsp_translation_model

open Set Metric MeasureTheory LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

/-- A nonempty unit-tube family forces an absolute lower bound on its count coefficient. -/
lemma coefficient_lower {r L : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    {K n : ℕ} (x v : Fin n → Space) (g : Fin n → Fin K)
    (hv : ∀ i, ‖v i‖ = 1)
    (hcount : ∀ (k : Fin K) (W : Set Space), Convex ℝ W →
      ENNReal.ofReal ((ncard {i : Fin n | g i = k ∧ Tube r (x i) (v i) ⊆ W} : ℝ) * r ^ 2)
        ≤ ENNReal.ofReal L * volume W)
    (i₀ : Fin n) : 1 ≤ 384 * L := by
  let W := Tube r (x i₀) (v i₀)
  have hcard : (1 : ℝ) ≤ (ncard {i : Fin n | g i = g i₀ ∧ Tube r (x i) (v i) ⊆ W} : ℝ) := by
    have hh : 0 < ncard {i : Fin n | g i = g i₀ ∧ Tube r (x i) (v i) ⊆ W} :=
      (ncard_pos (Set.toFinite _)).mpr ⟨i₀, rfl, Subset.rfl⟩
    exact_mod_cast hh
  have hvol : volume W ≤ ENNReal.ofReal (384 * r ^ 2) :=
    WangZahlLot.Obl.wz_affine_packet_counting_transfer.tube_volume_upper hr hr1 (x i₀) (v i₀) (hv i₀)
  have hbound : ENNReal.ofReal (r ^ 2) ≤ ENNReal.ofReal L * ENNReal.ofReal (384 * r ^ 2) := by
    calc
      _ ≤ ENNReal.ofReal ((ncard {i : Fin n | g i = g i₀ ∧ Tube r (x i) (v i) ⊆ W} : ℝ) * r ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        simpa using mul_le_mul_of_nonneg_right hcard (sq_nonneg r)
      _ ≤ ENNReal.ofReal L * volume W :=
        hcount (g i₀) W ((convex_segment _ _).thickening r)
      _ ≤ _ := by gcongr
  have hLpos : 0 < L := by
    by_contra! hL
    rw [ENNReal.ofReal_of_nonpos hL, zero_mul] at hbound
    have hh := ENNReal.ofReal_eq_zero.mp (le_antisymm hbound bot_le)
    nlinarith [sq_pos_of_pos hr]
  rw [← ENNReal.ofReal_mul hLpos.le] at hbound
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hbound
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hr)).mp
  nlinarith only [hreal]

end WangZahlLot.Obl.wz_nsp_translation_model
