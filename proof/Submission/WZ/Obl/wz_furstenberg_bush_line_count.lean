-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_bush_line_count.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_furstenberg_bush_line_count.FromHalf
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_furstenberg_bush_line_count`

Glue of the split of o157. `furstenberg_of_half_and_open` (FromHalf.lean and its import
closure: Katz--Tao and separation extraction, the low range `σ < 1/2`, exponent stability and
compactness in the exponent) derives the frozen statement from the fixed-exponent Katz--Tao
estimate at `s = 1/2` (child `wz_furstenberg_katz_tao_half`) and at every `s` in `(1/2, 1)`
(child `wz_furstenberg_katz_tao_high`).
-/

theorem WangZahlLot.wz_furstenberg_bush_line_count : ∀ ε : ℝ, 0 < ε → ∃ ε₀ η r₀ : ℝ, 0 < ε₀ ∧ 0 < η ∧ 0 < r₀ ∧ ∀ r σ : ℝ, 0 < r → r ≤ r₀ → 1 / 4 ≤ σ → σ ≤ 1 - ε → ∀ (P : Set (EuclideanSpace ℝ (Fin 2))) (D : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))), P.Finite → P.Nonempty → D.Finite → (∀ p ∈ P, ‖p‖ ≤ 4) → (∀ (x : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ), r ≤ ρ → ((P ∩ Metric.closedBall x ρ).ncard : ℝ) ≤ r ^ (-η) * ρ * P.ncard) → (∀ q ∈ D, q.1 ∈ P ∧ ‖q.2‖ = 1) → (∀ p ∈ P, r ^ (η - σ) ≤ ({e | (p, e) ∈ D}.ncard : ℝ)) → (∀ p e e', (p, e) ∈ D → (p, e') ∈ D → e ≠ e' → r ≤ dist e e') → (∀ p ∈ P, ∀ u : EuclideanSpace ℝ (Fin 2), ‖u‖ = 1 → ∀ ρ : ℝ, r ≤ ρ → ({e | (p, e) ∈ D ∧ dist e u ≤ ρ}.ncard : ℝ) ≤ r ^ (-η) * (ρ / r) ^ σ) → ∃ J ⊆ D, (∀ q ∈ J, ∀ q' ∈ J, q ≠ q' → (r ≤ dist q.2 q'.2 ∧ r ≤ dist q.2 (-q'.2)) ∨ r ≤ |inner ℝ (q.1 - q'.1) q.2|) ∧ r ^ (-(2 * σ) - ε₀) ≤ (J.ncard : ℝ) := by
  exact WangZahlLot.Obl.wz_furstenberg_bush_line_count.furstenberg_of_half_and_open
    WangZahlLot.wz_furstenberg_katz_tao_half WangZahlLot.wz_furstenberg_katz_tao_high
