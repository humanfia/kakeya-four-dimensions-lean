-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_essentially_distinct_tube_count.Packing.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
open Set Metric MeasureTheory
open LeanEval.Analysis.WangZahlKakeya

namespace WangZahlLot.Obl.wz_essentially_distinct_tube_count

/-- A packing estimate in the six-dimensional space of tube parameters. -/
lemma parameter_ball_packing {n : ℕ} {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (p : Fin n → Space × Space) (hp : ∀ i, ‖p i‖ ≤ 1)
    (hd : Pairwise (fun i j => Disjoint (ball (p i) r) (ball (p j) r))) :
    (n : ℝ) * r ^ 6 ≤ 2 ^ 6 := by
  let μ : Measure (Space × Space) := (volume : Measure Space).prod volume
  have hdim : Module.finrank ℝ (Space × Space) = 6 := by
    simp [Module.finrank_prod, Space, finrank_euclideanSpace]
  have hsub : (⋃ i, ball (p i) r) ⊆ ball (0 : Space × Space) 2 := by
    intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    have hi' : dist z (p i) < r := hi
    have hpi : dist (p i) 0 ≤ 1 := by simpa using hp i
    have ht := dist_triangle z (p i) 0
    show dist z 0 < 2
    linarith
  have hmeasure : (n : ENNReal) * ENNReal.ofReal (r ^ 6) * μ (ball 0 1) ≤
      ENNReal.ofReal ((2 : ℝ) ^ 6) * μ (ball 0 1) := by
    have h := measure_mono (μ := μ) hsub
    rw [measure_iUnion hd (fun _ => measurableSet_ball), tsum_fintype] at h
    simp_rw [Measure.addHaar_ball μ _ hr.le, hdim] at h
    rw [Measure.addHaar_ball μ 0 (by norm_num : (0 : ℝ) ≤ 2), hdim] at h
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_assoc] using h
  have hpos : 0 < μ (ball (0 : Space × Space) 1) := measure_ball_pos μ 0 (by norm_num)
  have hfin : μ (ball (0 : Space × Space) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have h := (ENNReal.mul_le_mul_iff_left hpos.ne' hfin).mp hmeasure
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

end WangZahlLot.Obl.wz_essentially_distinct_tube_count
