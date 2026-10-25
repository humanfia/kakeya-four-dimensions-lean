-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.FromHalf.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.FromKatzTao

/-!
# What remains once the case `s = 1/2` is proved

`furstenberg_of_half_and_open`: the literal frozen statement of o157 follows from the
fixed-exponent estimate at `s = 1/2` (the output of `half_core`) together with the
fixed-exponent estimates for every `s` in the open range `(1/2, 1)`.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half

/-- The fixed-exponent estimate at one exponent. -/
def FixedKatzTaoAt (s : ℝ) : Prop :=
  ∃ ε₀ η r₀ : ℝ, 0 < ε₀ ∧ 0 < η ∧ 0 < r₀ ∧
    ∀ r : ℝ, 0 < r → r ≤ r₀ → KatzTaoFurstenbergAt r s ε₀ η

theorem fixed_katz_tao_of_half_and_open (hhalf : FixedKatzTaoAt (1 / 2))
    (hopen : ∀ s : ℝ, 1 / 2 < s → s < 1 → FixedKatzTaoAt s) : FixedKatzTaoCore := by
  intro s hs hs1
  rcases eq_or_lt_of_le hs with h | h
  · rw [← h]; exact hhalf
  · exact hopen s h hs1

/-- The literal frozen statement of o157 from the case `s = 1/2` and the open high range. -/
theorem furstenberg_of_half_and_open (hhalf : FixedKatzTaoAt (1 / 2))
    (hopen : ∀ s : ℝ, 1 / 2 < s → s < 1 → FixedKatzTaoAt s) : ∀ ε : ℝ, 0 < ε → ∃ ε₀ η r₀ : ℝ, 0 < ε₀ ∧ 0 < η ∧ 0 < r₀ ∧ ∀ r σ : ℝ, 0 < r → r ≤ r₀ → 1 / 4 ≤ σ → σ ≤ 1 - ε → ∀ (P : Set (EuclideanSpace ℝ (Fin 2))) (D : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))), P.Finite → P.Nonempty → D.Finite → (∀ p ∈ P, ‖p‖ ≤ 4) → (∀ (x : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ), r ≤ ρ → ((P ∩ Metric.closedBall x ρ).ncard : ℝ) ≤ r ^ (-η) * ρ * P.ncard) → (∀ q ∈ D, q.1 ∈ P ∧ ‖q.2‖ = 1) → (∀ p ∈ P, r ^ (η - σ) ≤ ({e | (p, e) ∈ D}.ncard : ℝ)) → (∀ p e e', (p, e) ∈ D → (p, e') ∈ D → e ≠ e' → r ≤ dist e e') → (∀ p ∈ P, ∀ u : EuclideanSpace ℝ (Fin 2), ‖u‖ = 1 → ∀ ρ : ℝ, r ≤ ρ → ({e | (p, e) ∈ D ∧ dist e u ≤ ρ}.ncard : ℝ) ≤ r ^ (-η) * (ρ / r) ^ σ) → ∃ J ⊆ D, (∀ q ∈ J, ∀ q' ∈ J, q ≠ q' → (r ≤ dist q.2 q'.2 ∧ r ≤ dist q.2 (-q'.2)) ∨ r ≤ |inner ℝ (q.1 - q'.1) q.2|) ∧ r ^ (-(2 * σ) - ε₀) ≤ (J.ncard : ℝ) :=
  furstenberg_of_fixed_katz_tao (fixed_katz_tao_of_half_and_open hhalf hopen)

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half
