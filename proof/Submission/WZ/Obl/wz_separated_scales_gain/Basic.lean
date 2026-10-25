-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_scales_gain.Basic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Basic

namespace WangZahlLot.Obl.wz_separated_scales_gain

open MeasureTheory
open WangZahlLot.Obl.wz_nonflat_factored_improvement

abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- The two nested covers and their count hypotheses, exactly as in the frozen statement. -/
abbrev SeparatedStructure (ζ₁ ζ₂ δ : ℝ) (n : ℕ) (x v : Fin n → Space) : Prop :=
  ∃ τ ρ : ℝ, δ ≤ τ ∧ τ < ρ ∧ ρ ≤ 1 ∧ τ ≤ δ ^ ζ₁ * ρ ∧
    ∃ (p : ℕ) (y u : Fin p → Space) (q : ℕ) (z w : Fin q → Space),
      (∀ j, ‖u j‖ = 1) ∧ (∀ l, ‖w l‖ = 1) ∧
      (∀ j j', j ≠ j' → volume (tube τ (y j) (u j) ∩ tube τ (y j') (u j')) ≤
        (1 / 2 : ENNReal) * volume (tube τ (y j) (u j))) ∧
      (∀ l l', l ≠ l' → volume (tube ρ (z l) (w l) ∩ tube ρ (z l') (w l')) ≤
        (1 / 2 : ENNReal) * volume (tube ρ (z l) (w l))) ∧
      (∀ i, ∃! j, tube δ (x i) (v i) ⊆ tube τ (y j) (u j)) ∧
      (∀ j, ∃ i, tube δ (x i) (v i) ⊆ tube τ (y j) (u j)) ∧
      (∀ j, ∃! l, tube τ (y j) (u j) ⊆ tube ρ (z l) (w l)) ∧
      (∀ l, ∃ j, tube τ (y j) (u j) ⊆ tube ρ (z l) (w l)) ∧
      (∀ j j', (Set.ncard {i | tube δ (x i) (v i) ⊆ tube τ (y j) (u j)} : ℝ) ≤
        δ ^ (-ζ₂) * Set.ncard {i | tube δ (x i) (v i) ⊆ tube τ (y j') (u j')}) ∧
      (∀ l l', (Set.ncard {j | tube τ (y j) (u j) ⊆ tube ρ (z l) (w l)} : ℝ) ≤
        δ ^ (-ζ₂) * Set.ncard {j | tube τ (y j) (u j) ⊆ tube ρ (z l') (w l')}) ∧
      (∀ j W, Convex ℝ W →
        ENNReal.ofReal (Set.ncard {i | tube δ (x i) (v i) ⊆ tube τ (y j) (u j) ∧
          tube δ (x i) (v i) ⊆ W} * τ ^ 2) ≤
        ENNReal.ofReal (δ ^ (-ζ₂) * Set.ncard {i | tube δ (x i) (v i) ⊆ tube τ (y j) (u j)}) * volume W) ∧
      (∀ l W, Convex ℝ W →
        ENNReal.ofReal (Set.ncard {j | tube τ (y j) (u j) ⊆ tube ρ (z l) (w l) ∧
          tube τ (y j) (u j) ⊆ W} * τ ^ 2) ≤ ENNReal.ofReal (δ ^ (-ζ₂)) * volume W) ∧
      (∀ l, δ ^ ζ₂ * (ρ / τ) ^ 2 ≤
        Set.ncard {j | tube τ (y j) (u j) ⊆ tube ρ (z l) (w l)}) ∧
      (∀ W, Convex ℝ W →
        ENNReal.ofReal (Set.ncard {l | tube ρ (z l) (w l) ⊆ W}) ≤
        ENNReal.ofReal (δ ^ (-ζ₂) * q) * volume W)

abbrev SeparatedGain (σ ω' ζ₁ : ℝ) : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∃ ζ₀ : ℝ, 0 < ζ₀ ∧
    ∀ ζ₂ : ℝ, 0 < ζ₂ → ζ₂ ≤ ζ₀ → ∀ ε : ℝ, 0 < ε →
      ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
          ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
            FamilyHypotheses η δ n x v Y
              ((∀ i, ENNReal.ofReal (δ ^ η * δ ^ 2) ≤ volume (Y i)) →
                SeparatedStructure ζ₁ ζ₂ δ n x v →
                ENNReal.ofReal (a * δ ^ (ω' - α + ε) * (n * δ ^ 4) ^ (σ / 2)) ≤
                  volume (⋃ i, Y i))

end WangZahlLot.Obl.wz_separated_scales_gain
