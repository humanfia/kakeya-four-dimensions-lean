-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_weighted_affine_packet_balancing.Basic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
set_option autoImplicit false

namespace WangZahlLot.Obl.wz_weighted_affine_packet_balancing

open MeasureTheory Metric Set LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

abbrev Tube (d : ℝ) (x v : Space) : Set Space := thickening d (segment ℝ x (x + v))
abbrev Ball : Set Space := ball (0 : Space) 1

abbrev Admissible (h ρ : ℝ) (N : ℕ) (z w : Fin N → Space)
    (Z : Fin N → Set Space) : Prop :=
  0 < N ∧ (∀ a, ‖w a‖ = 1) ∧ (∀ a, Tube ρ (z a) (w a) ⊆ Ball) ∧
  (∀ a b, a ≠ b → volume (Tube ρ (z a) (w a) ∩ Tube ρ (z b) (w b)) ≤
    (1 / 2 : ℝ≥0∞) * volume (Tube ρ (z a) (w a))) ∧
  (∀ a, MeasurableSet (Z a)) ∧ (∀ a, Z a ⊆ Tube ρ (z a) (w a)) ∧
  ENNReal.ofReal (h * (N : ℝ) * ρ ^ 2) ≤ ∑ a, volume (Z a)

abbrev SlabCount (ρ l : ℝ) (N : ℕ) (z w : Fin N → Space) : Prop :=
  ∀ (u : Space) (a r : ℝ), ‖u‖ = 1 → 0 < r →
    ENNReal.ofReal (Set.ncard {i | Tube ρ (z i) (w i) ⊆
      (Ball ∩ {p | |inner ℝ u p - a| ≤ r})} : ℝ) ≤
    ENNReal.ofReal (l * (N : ℝ)) * volume (Ball ∩ {p | |inner ℝ u p - a| ≤ r})

abbrev Certificate (δ h ρ t : ℝ) (n k N q : ℕ) (x v : Fin n → Space)
    (z w : Fin k → Fin N → Space) : Prop :=
  ∃ (F : Fin k → Fin N → Finset (Fin n)) (f : Fin k → AffineEquiv ℝ Space Space),
    (∀ j a, (F j a).card = q) ∧ (∀ j a b, a ≠ b → Disjoint (F j a) (F j b)) ∧
    h * (n : ℝ) ≤ (k : ℝ) * (N : ℝ) * (q : ℝ) ∧
    (∀ j a i, i ∈ F j a → Tube δ (x i) (v i) ⊆ f j '' Tube ρ (z j a) (w j a)) ∧
    (∀ j (Q : Set Space), Convex ℝ Q →
      volume (f j '' Q ∩ Ball) ≤ ENNReal.ofReal (t / h) * volume Q)

abbrev Weighted (δ h : ℝ) (n : ℕ) (x v : Fin n → Space)
    (Y : Fin n → Set Space) : Prop :=
  0 < n ∧ (n : ℝ) ≤ δ ^ (-100 : ℝ) ∧ ∃ m : ℕ, 0 < m ∧
    ∃ ρ : ℝ, 0 < ρ ∧ δ * h ≤ ρ ∧ ρ ≤ (1 / 100 : ℝ) ∧
    ∃ (M : Fin m → ℕ) (f : Fin m → AffineEquiv ℝ Space Space) (D : Fin m → ℝ)
      (z w : (j : Fin m) → Fin (M j) → Space)
      (Z : (j : Fin m) → Fin (M j) → Set Space)
      (F : (j : Fin m) → Fin (M j) → Finset (Fin n)),
    (∀ j, 0 < M j) ∧ (∀ j, δ ^ (100 : ℕ) ≤ D j ∧ D j ≤ δ ^ (-100 : ℝ)) ∧
    (∀ j (Q : Set Space), volume (f j '' Q) = ENNReal.ofReal (D j) * volume Q) ∧
    (∀ j a, ‖w j a‖ = 1) ∧ (∀ j a, Tube ρ (z j a) (w j a) ⊆ Ball) ∧
    (∀ j a b, a ≠ b → volume (Tube ρ (z j a) (w j a) ∩ Tube ρ (z j b) (w j b)) ≤
      (1 / 2 : ℝ≥0∞) * volume (Tube ρ (z j a) (w j a))) ∧
    (∀ j a, MeasurableSet (Z j a)) ∧ (∀ j a, Z j a ⊆ Tube ρ (z j a) (w j a)) ∧
    (∀ j a, ENNReal.ofReal (h * ρ ^ 2) ≤ volume (Z j a)) ∧
    (∀ j a, (F j a).Nonempty) ∧ (∀ j a b, a ≠ b → Disjoint (F j a) (F j b)) ∧
    (∀ j a i, i ∈ F j a → Tube δ (x i) (v i) ⊆ f j '' Tube ρ (z j a) (w j a)) ∧
    h * (n : ℝ) ≤ ∑ j, ∑ a, ((F j a).card : ℝ) ∧
    (∀ j (ν : Space) (s r : ℝ), ‖ν‖ = 1 → 0 < r →
      ENNReal.ofReal (Set.ncard {i : Fin n | ∃ a : Fin (M j), i ∈ F j a ∧
        Tube ρ (z j a) (w j a) ⊆ (Ball ∩ {p | |inner ℝ ν p - s| ≤ r})} : ℝ) ≤
      ENNReal.ofReal (h⁻¹ * ∑ a, ((F j a).card : ℝ)) *
        volume (Ball ∩ {p | |inner ℝ ν p - s| ≤ r})) ∧
    ∑ j, ENNReal.ofReal (D j) * volume (⋃ a, Z j a) ≤ volume (⋃ i, Y i)

abbrev Output (e δ : ℝ) (n : ℕ) (x v : Fin n → Space)
    (Y : Fin n → Set Space) : Prop :=
  ∃ k N q : ℕ, 0 < k ∧ 0 < N ∧ 0 < q ∧ ∃ ρ t : ℝ,
    δ ^ (1 + e) ≤ ρ ∧ ρ ≤ (1 / 100 : ℝ) ∧ 0 < t ∧
    ∃ (z w : Fin k → Fin N → Space) (Z : Fin k → Fin N → Set Space),
      Certificate δ (δ ^ e) ρ t n k N q x v z w ∧
      (∀ j, Admissible (δ ^ e) ρ N (z j) (w j) (Z j) ∧
        SlabCount ρ ((δ ^ e)⁻¹) N (z j) (w j)) ∧
      ENNReal.ofReal (δ ^ e * t) * ∑ j, volume (⋃ a, Z j a) ≤ volume (⋃ i, Y i)

end WangZahlLot.Obl.wz_weighted_affine_packet_balancing
