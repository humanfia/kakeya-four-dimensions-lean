-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_two_scale_flat_box_estimate.DenseFine.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.Interfaces
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Selection
import Submission.WZ.Obl.wz_nonflat_factored_improvement.CoarseGeometry

namespace WangZahlLot.Obl.wz_two_scale_flat_box_estimate

open MeasureTheory Set Metric

lemma select_dense_fine {δ lam : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hlam : 0 < lam)
    {n : ℕ} (hn : 0 < n) (x v : Fin n → Space) (Y : Fin n → Set Space)
    (hv : ∀ i, ‖v i‖ = 1) (hYT : ∀ i, Y i ⊆ Tube δ (x i) (v i))
    (hYB : ∀ i, Y i ⊆ ball (0 : Space) 1)
    (hmass : ENNReal.ofReal (lam * n * δ ^ 2) ≤ ∑ i, volume (Y i)) :
    ∃ (m : ℕ) (j : Fin m → Fin n), 0 < m ∧ Function.Injective j ∧
      lam / 112 * n ≤ m ∧
      ∀ i, ENNReal.ofReal (lam / 2 * δ ^ 2) ≤ volume (Y (j i)) := by
  have hfin (i : Fin n) : volume (Y i) ≠ ⊤ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono (hYB i))
  have hu (i : Fin n) : volume.real (Y i) ≤ 56 * δ ^ 2 := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      ((measure_mono (hYT i)).trans
        (WangZahlLot.Obl.wz_nonflat_factored_improvement.tube_volume_upper hδ.le hδ1 (x i) (v i) (hv i)))
    simpa only [measureReal_def, ENNReal.toReal_ofReal (by positivity : 0 ≤ 56 * δ ^ 2)] using hh
  have hs : lam * n * δ ^ 2 ≤ ∑ i, volume.real (Y i) := by
    have hh := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr (fun i _ => hfin i)) hmass
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ lam * n * δ ^ 2),
      ENNReal.toReal_sum (fun i _ => hfin i), measureReal_def] using hh
  obtain ⟨m, j, hm, hj, hret, hind⟩ :=
    WangZahlLot.Obl.wz_nonflat_factored_improvement.dense_index_subfamily hn
      (fun i => volume.real (Y i)) (by positivity : 0 < lam / 2 * δ ^ 2)
      (by positivity : 0 < 56 * δ ^ 2) hu (by nlinarith only [hs])
  refine ⟨m, j, hm, hj, ?_, ?_⟩
  · convert hret using 1 <;> field_simp <;> ring
  · intro i
    exact (ENNReal.ofReal_le_iff_le_toReal (hfin (j i))).mpr (hind i)

end WangZahlLot.Obl.wz_two_scale_flat_box_estimate
