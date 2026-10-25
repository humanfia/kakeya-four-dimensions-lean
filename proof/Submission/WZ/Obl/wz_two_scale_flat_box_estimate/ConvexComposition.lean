-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_two_scale_flat_box_estimate.ConvexComposition.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.Interfaces
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.Basic
import Submission.WZ.Obl.wz_flat_factored_improvement.BodyTransport

namespace WangZahlLot.Obl.wz_two_scale_flat_box_estimate

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_flat_factored_improvement (BodyConvexCount)

/-- Relative convex counting in one box yields raw convex counting for any
selected subfamily assigned to that box. -/
lemma relative_convex_count {n m : ℕ} (T : Fin n → Set Space) (P : Fin n → Prop)
    (U : Set Space) {w L : ℝ} (hw : 0 < w) (hL : 0 ≤ L)
    (hvol : volume U = ENNReal.ofReal w) (hTU : ∀ i, P i → T i ⊆ U)
    (h : ∀ W, Convex ℝ W →
      ENNReal.ofReal (Set.ncard {i | P i ∧ T i ⊆ U ∩ W} : ℝ) * volume U ≤
        ENNReal.ofReal (L * Set.ncard {i | P i}) * volume (U ∩ W))
    (j : Fin m → Fin n) (hj : Function.Injective j) (hPj : ∀ i, P (j i)) :
    ∀ W, Convex ℝ W →
      ENNReal.ofReal (Set.ncard {i | T (j i) ⊆ W} : ℝ) ≤
        ENNReal.ofReal (L * Set.ncard {i | P i} / w) * volume W := by
  intro W hW
  have hc : Set.ncard {i | T (j i) ⊆ W} ≤ Set.ncard {i | P i ∧ T i ⊆ U ∩ W} := by
    refine (Set.ncard_mono (b := {i | P (j i) ∧ T (j i) ⊆ U ∩ W}) ?_).trans
      (WangZahlLot.Obl.wz_rescaled_fibre_alternatives.count_subfamily j hj
        (fun i => P i ∧ T i ⊆ U ∩ W))
    intro i hi
    exact ⟨hPj i, fun p hp => ⟨hTU (j i) (hPj i) hp, hi hp⟩⟩
  have hh : ENNReal.ofReal (Set.ncard {i | T (j i) ⊆ W} : ℝ) * ENNReal.ofReal w ≤
      ENNReal.ofReal (L * Set.ncard {i | P i}) * volume W := by
    rw [← hvol]
    exact (mul_le_mul' (ENNReal.ofReal_le_ofReal (Nat.cast_le.mpr hc)) le_rfl).trans
      ((h W hW).trans (mul_le_mul' le_rfl (measure_mono inter_subset_right)))
  have hw0 : ENNReal.ofReal w ≠ 0 := (ENNReal.ofReal_pos.mpr hw).ne'
  calc
    _ = (ENNReal.ofReal (Set.ncard {i | T (j i) ⊆ W} : ℝ) * ENNReal.ofReal w) *
        (ENNReal.ofReal w)⁻¹ := by
      rw [mul_assoc, ENNReal.mul_inv_cancel hw0 ENNReal.ofReal_ne_top, mul_one]
    _ ≤ (ENNReal.ofReal (L * Set.ncard {i | P i}) * volume W) * (ENNReal.ofReal w)⁻¹ :=
      mul_le_mul_left hh _
    _ = _ := by
      rw [mul_right_comm, ← ENNReal.ofReal_inv_of_pos hw,
        ← ENNReal.ofReal_mul' (inv_nonneg.mpr hw.le), div_eq_mul_inv]

lemma raw_convex_count_enlarge {n : ℕ} (T U : Fin n → Set Space) {K w : ℝ}
    (hK : 0 ≤ K) (hw : 0 ≤ w) (hTU : ∀ i, T i ⊆ U i)
    (h : ∀ W, Convex ℝ W → ENNReal.ofReal (Set.ncard {i | T i ⊆ W} : ℝ) ≤
      ENNReal.ofReal K * volume W) : BodyConvexCount U w (K * w) := by
  intro W hW
  have hc : Set.ncard {i | U i ⊆ W} ≤ Set.ncard {i | T i ⊆ W} :=
    ncard_mono (fun i hi => (hTU i).trans hi)
  rw [ENNReal.ofReal_mul' hw, ENNReal.ofReal_mul hK]
  exact (mul_le_mul' (ENNReal.ofReal_le_ofReal (Nat.cast_le.mpr hc)) le_rfl).trans
    ((mul_le_mul_left (h W hW) (ENNReal.ofReal w)).trans_eq (by ring))

end WangZahlLot.Obl.wz_two_scale_flat_box_estimate
