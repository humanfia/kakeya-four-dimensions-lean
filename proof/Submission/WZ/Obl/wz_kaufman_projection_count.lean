-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_kaufman_projection_count.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_kaufman_projection_count.Kaufman
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_kaufman_projection_count`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_kaufman_projection_count`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_kaufman_projection_count/`
belong to this obligation.
-/

theorem WangZahlLot.wz_kaufman_projection_count : ∀ ε : ℝ, 0 < ε → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ C d : ℝ, 0 < δ → δ ≤ δ₀ → 1 ≤ C → 0 < d → ∀ (F Λ : Set (EuclideanSpace ℝ (Fin 2))) (H : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))), F.Finite → Λ.Finite → (∀ θ ∈ Λ, ‖θ‖ = 1) → (∀ (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ), δ ≤ r → ((F ∩ Metric.closedBall x r).ncard : ℝ) ≤ C * r * F.ncard ∧ ((Λ ∩ Metric.closedBall x r).ncard : ℝ) ≤ C * r * Λ.ncard) → H ⊆ Λ ×ˢ F → H.Nonempty → d * Λ.ncard * F.ncard ≤ H.ncard → ∃ θ ∈ Λ, ∀ (m : ℕ) (cc : Fin m → ℝ), {t : ℝ | ∃ a, (θ, a) ∈ H ∧ t = inner ℝ θ a} ⊆ (⋃ j, Metric.closedBall (cc j) δ) → d ^ 3 * δ ^ (ε - 1) ≤ C ^ 2 * m := by
  exact WangZahlLot.Obl.wz_kaufman_projection_count.kaufman_projection_count
