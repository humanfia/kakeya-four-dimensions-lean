-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_fibre_slab_dichotomy.Tubes.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_direction_density_transfer.Geometry
import Submission.WZ.Obl.wz_affine_packet_counting_transfer.Basic

/-!
# Closed tubes

The greedy slab extraction of o067 works with compact convex sets; we use the closures of the
open `δ`-tubes. Slabs are closed, so a tube lies in a slab iff its closure does.
-/

set_option linter.unusedVariables false

namespace WangZahlLot.Obl.wz_coarse_fibre_slab_dichotomy

open MeasureTheory Set Metric
open scoped ENNReal

local notation "Sp" => LeanEval.Analysis.WangZahlKakeya.Space

/-- The closed tube: closure of the open `δ`-tube. -/
def tubeU (δ : ℝ) (x v : Sp) : Set Sp := closure (thickening δ (segment ℝ x (x + v)))

lemma subset_tubeU (δ : ℝ) (x v : Sp) : thickening δ (segment ℝ x (x + v)) ⊆ tubeU δ x v :=
  subset_closure

lemma tubeU_convex (δ : ℝ) (x v : Sp) : Convex ℝ (tubeU δ x v) :=
  ((convex_segment _ _).thickening δ).closure

lemma tubeU_subset_closedBall {δ : ℝ} {x v : Sp}
    (hT : thickening δ (segment ℝ x (x + v)) ⊆ ball (0 : Sp) 1) :
    tubeU δ x v ⊆ closedBall (0 : Sp) 1 :=
  (closure_mono hT).trans closure_ball_subset_closedBall

lemma tubeU_compact {δ : ℝ} {x v : Sp}
    (hT : thickening δ (segment ℝ x (x + v)) ⊆ ball (0 : Sp) 1) : IsCompact (tubeU δ x v) :=
  (isBounded_ball.subset hT).isCompact_closure

lemma ball_subset_tubeU {δ : ℝ} (hδ : 0 < δ) (x v : Sp) : ball x δ ⊆ tubeU δ x v :=
  (ball_subset_thickening (left_mem_segment ℝ x (x + v)) δ).trans (subset_tubeU δ x v)

lemma tubeU_subset_iff {δ : ℝ} {x v : Sp} {Q : Set Sp} (hQ : IsClosed Q) :
    tubeU δ x v ⊆ Q ↔ thickening δ (segment ℝ x (x + v)) ⊆ Q :=
  ⟨fun h => (subset_tubeU δ x v).trans h, fun h => closure_minimal h hQ⟩

lemma volume_tubeU_ge {δ : ℝ} (hδ : 0 < δ) (x : Sp) {v : Sp} (hv : ‖v‖ = 1) :
    ENNReal.ofReal (δ ^ 2) ≤ volume (tubeU δ x v) :=
  (WangZahlLot.Obl.wz_direction_density_transfer.tube_volume_lower hδ x v hv).trans
    (measure_mono (subset_tubeU δ x v))

lemma volume_tubeU_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) (x : Sp) {v : Sp} (hv : ‖v‖ = 1) :
    volume (tubeU δ x v) ≤ ENNReal.ofReal (1536 * δ ^ 2) := by
  have h1 : tubeU δ x v ⊆ thickening (2 * δ) (segment ℝ x (x + v)) :=
    (closure_thickening_subset_cthickening δ _).trans
      (cthickening_subset_thickening' (by linarith) (by linarith) _)
  calc volume (tubeU δ x v) ≤ volume (thickening (2 * δ) (segment ℝ x (x + v))) := measure_mono h1
    _ ≤ ENNReal.ofReal (384 * (2 * δ) ^ 2) :=
        WangZahlLot.Obl.wz_affine_packet_counting_transfer.tube_volume_upper (by linarith)
          (by linarith) x v hv
    _ = ENNReal.ofReal (1536 * δ ^ 2) := by ring_nf

lemma volume_tubeU_ne_zero {δ : ℝ} (hδ : 0 < δ) (x : Sp) {v : Sp} (hv : ‖v‖ = 1) :
    volume (tubeU δ x v) ≠ 0 := by
  have := volume_tubeU_ge hδ x hv
  intro h
  rw [h] at this
  have : δ ^ 2 ≤ 0 := ENNReal.ofReal_eq_zero.mp (le_antisymm this bot_le)
  nlinarith [sq_nonneg δ, pow_pos hδ 2]

lemma volume_tubeU_ne_top {δ : ℝ} {x v : Sp}
    (hT : thickening δ (segment ℝ x (x + v)) ⊆ ball (0 : Sp) 1) :
    volume (tubeU δ x v) ≠ ⊤ :=
  (tubeU_compact hT).measure_lt_top.ne

end WangZahlLot.Obl.wz_coarse_fibre_slab_dichotomy
