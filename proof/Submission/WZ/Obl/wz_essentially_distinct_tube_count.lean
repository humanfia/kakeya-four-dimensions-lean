-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_essentially_distinct_tube_count.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_essentially_distinct_tube_count.Geometry
import Submission.WZ.Obl.wz_essentially_distinct_tube_count.Packing
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_essentially_distinct_tube_count`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_essentially_distinct_tube_count`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_essentially_distinct_tube_count/`
belong to this obligation.
-/

open Set Metric MeasureTheory
open LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_essentially_distinct_tube_count

theorem WangZahlLot.wz_essentially_distinct_tube_count : ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ (1 / 100 : ℝ) → ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space), (∀ i : Fin n, ‖v i‖ = 1) → (∀ i : Fin n, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1) → (∀ i j : Fin n, i ≠ j → MeasureTheory.volume (Metric.thickening δ (segment ℝ (x i) (x i + v i)) ∩ Metric.thickening δ (segment ℝ (x j) (x j + v j))) ≤ (1 / 2 : ENNReal) * MeasureTheory.volume (Metric.thickening δ (segment ℝ (x i) (x i + v i)))) → (n : ℝ) * δ ^ 6 ≤ C := by
  refine ⟨(80 : ℝ) ^ 6, by norm_num, ?_⟩
  intro δ hδ hδ1 n x v hv hT hsep
  let p : Fin n → Space × Space := fun i => (x i, v i)
  have hx : ∀ i, ‖x i‖ < 1 := by
    intro i
    have hi := hT i (self_subset_thickening hδ _ (left_mem_segment ℝ (x i) (x i + v i)))
    simpa only [mem_ball, dist_zero_right] using hi
  have hp : ∀ i, ‖p i‖ ≤ 1 := by
    intro i
    change max ‖x i‖ ‖v i‖ ≤ 1
    exact max_le (hx i).le (hv i).le
  have hd : Pairwise (fun i j => Disjoint (ball (p i) (δ / 40))
      (ball (p j) (δ / 40))) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro z hzi hzj
    have hi : dist (p i) z < δ / 40 := by
      simpa only [mem_ball, dist_comm] using hzi
    have hj : dist z (p j) < δ / 40 := hzj
    have hdist : dist (p i) (p j) < δ / 20 := by
      have ht := dist_triangle (p i) z (p j)
      linarith
    change max (dist (x i) (x j)) (dist (v i) (v j)) < δ / 20 at hdist
    exact not_close_of_half_overlap hδ (hT i) (hsep i j hij)
      ⟨(max_lt_iff.mp hdist).1.le, (max_lt_iff.mp hdist).2.le⟩
  have hpack := parameter_ball_packing (by positivity : 0 < δ / 40)
    (by linarith : δ / 40 ≤ 1) p hp hd
  calc
    (n : ℝ) * δ ^ 6 = ((n : ℝ) * (δ / 40) ^ 6) * (40 : ℝ) ^ 6 := by ring
    _ ≤ (2 : ℝ) ^ 6 * (40 : ℝ) ^ 6 := by gcongr
    _ = (80 : ℝ) ^ 6 := by norm_num
