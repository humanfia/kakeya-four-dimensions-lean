-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.DenseWindowLeaf
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_furstenberg_katz_tao_high`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_furstenberg_katz_tao_high/`
belong to this obligation.
-/

theorem WangZahlLot.wz_furstenberg_katz_tao_high : ∀ s : ℝ, 1 / 2 < s → s < 1 → ∃ ε₀ η r₀ : ℝ, 0 < ε₀ ∧ 0 < η ∧ 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ → ∀ (P : Set (EuclideanSpace ℝ (Fin 2))) (D : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))), P.Finite → P.Nonempty → D.Finite → (∀ p ∈ P, ‖p‖ ≤ 4) → (∀ p ∈ P, ∀ p' ∈ P, p ≠ p' → r ≤ dist p p') → r ^ (η - 1) ≤ (P.ncard : ℝ) → (∀ (x : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ), r ≤ ρ → ((P ∩ Metric.closedBall x ρ).ncard : ℝ) ≤ r ^ (-η) * (ρ / r)) → (∀ q ∈ D, q.1 ∈ P ∧ ‖q.2‖ = 1) → (∀ p ∈ P, r ^ (η - s) ≤ ({e | (p, e) ∈ D}.ncard : ℝ)) → (∀ p e e', (p, e) ∈ D → (p, e') ∈ D → e ≠ e' → r ≤ dist e e') → (∀ p ∈ P, ∀ u : EuclideanSpace ℝ (Fin 2), ‖u‖ = 1 → ∀ ρ : ℝ, r ≤ ρ → ({e | (p, e) ∈ D ∧ dist e u ≤ ρ}.ncard : ℝ) ≤ r ^ (-η) * (ρ / r) ^ s) → ∃ J ⊆ D, (∀ q ∈ J, ∀ q' ∈ J, q ≠ q' → (r ≤ dist q.2 q'.2 ∧ r ≤ dist q.2 (-q'.2)) ∨ r ≤ |inner ℝ (q.1 - q'.1) q.2|) ∧ r ^ (-(2 * s) - ε₀) ≤ (J.ncard : ℝ) := by
  intro s hslo hs1
  exact WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.high_range hslo hs1
