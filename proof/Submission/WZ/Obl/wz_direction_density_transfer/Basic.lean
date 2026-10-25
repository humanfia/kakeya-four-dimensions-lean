-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_direction_density_transfer.Basic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
namespace WangZahlLot.Obl.wz_direction_density_transfer

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

abbrev Tube (δ : ℝ) (x v : Space) : Set Space := thickening δ (segment ℝ x (x + v))

def UniformConvexCount : Prop :=
    ∃ M : ℝ, 1 ≤ M ∧ ∀ δ : ℝ, 0 < δ →
    δ ≤ (1 / 100 : ℝ) →
    ∀ (n : ℕ) (x v : Fin n →
    Space), (∀ i : Fin n, ‖v i‖ = 1) →
    (∀ i j : Fin n, i ≠ j →
    δ ≤ ‖v i - v j‖ ∧ δ ≤ ‖v i + v j‖) →
    (∀ i : Fin n, Tube δ (x i) (v i) ⊆ ball (0 : Space) 1) →
    (∀ W : Set Space, Convex ℝ W →
    ENNReal.ofReal (((ncard {i : Fin n | Tube δ (x i) (v i) ⊆ W} : ℕ) : ℝ) * δ ^ 2) ≤ ENNReal.ofReal (M) * volume W)

def Endpoint : Prop :=
    ∀ ε : ℝ, 0 < ε →
    ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ →
    δ ≤ (1 / 100 : ℝ) →
    ∀ m l : ℝ, 1 ≤ m →
    1 ≤ l →
    ∀ (n : ℕ) (x v : Fin n →
    Space) (Y : Fin n →
    Set Space), 0 < n →
    (∀ i : Fin n, ‖v i‖ = 1) →
    (∀ i : Fin n, Tube δ (x i) (v i) ⊆ ball (0 : Space) 1) →
    (∀ i j : Fin n, i ≠ j →
    volume (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)) ≤ (1 / 2 : ENNReal) * volume (Tube δ (x i) (v i))) →
    (∀ i : Fin n, MeasurableSet (Y i)) →
    (∀ i : Fin n, Y i ⊆ Tube δ (x i) (v i)) →
    ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) ≤ Finset.sum Finset.univ (fun i : Fin n => volume (Y i)) →
    (∀ W : Set Space, Convex ℝ W →
    ENNReal.ofReal (((ncard {i : Fin n | Tube δ (x i) (v i) ⊆ W} : ℕ) : ℝ) * δ ^ 2) ≤ ENNReal.ofReal (m) * volume W) →
    (∀ (u : Space) (t r : ℝ), ‖u‖ = 1 →
    0 < r →
    ENNReal.ofReal (((ncard {i : Fin n | Tube δ (x i) (v i) ⊆ (ball (0 : Space) 1 ∩ {p : Space | |inner ℝ u p - t| ≤ r})} : ℕ) : ℝ)) ≤ ENNReal.ofReal ((l) * (n : ℝ)) * volume (ball (0 : Space) 1 ∩ {p : Space | |inner ℝ u p - t| ≤ r})) →
    ENNReal.ofReal (a * δ ^ ((0) + ε) * m⁻¹ * ((n : ℝ) * δ ^ 2) * (m ^ (- (3 / 2 : ℝ)) * l * ((n : ℝ) * δ)) ^ (-((0) : ℝ))) ≤ volume (⋃ i : Fin n, Y i)

def DirectionEstimate : Prop :=
    ∀ ε : ℝ, 0 < ε →
    ∃ κ : ℝ, ∃ c : ℝ, 0 < c ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ →
    δ ≤ δ₀ →
    ∀ lam : ℝ, 0 < lam →
    lam ≤ 1 →
    ∀ (n : ℕ) (x v : Fin n →
    Space) (Y : Fin n →
    Set Space), (∀ i : Fin n, ‖v i‖ = 1) →
    (∀ i j : Fin n, i ≠ j →
    δ ≤ ‖v i - v j‖ ∧ δ ≤ ‖v i + v j‖) →
    (∀ i : Fin n, Tube δ (x i) (v i) ⊆ ball (0 : Space) 1) →
    (∀ i : Fin n, MeasurableSet (Y i)) →
    (∀ i : Fin n, Y i ⊆ Tube δ (x i) (v i)) →
    (∀ i : Fin n, ENNReal.ofReal (lam * δ ^ 2) ≤ volume (Y i)) →
    ENNReal.ofReal (c * δ ^ ε * lam ^ κ * ((n : ℝ) * δ ^ 2)) ≤ volume (⋃ i : Fin n, Y i)

/-- A fixed positive proportion of the family has small pairwise intersections. -/
def Extraction : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
    ∀ (n : ℕ) (x v : Fin n → Space), 0 < n →
    (∀ i, ‖v i‖ = 1) →
    (∀ i j, i ≠ j → δ ≤ ‖v i - v j‖ ∧ δ ≤ ‖v i + v j‖) →
    (∀ i, Tube δ (x i) (v i) ⊆ ball 0 1) →
    ∃ (k : ℕ) (e : Fin k → Fin n), 0 < k ∧ Function.Injective e ∧ (n : ℝ) ≤ C * k ∧
      ∀ i j, i ≠ j → volume (Tube δ (x (e i)) (v (e i)) ∩
        Tube δ (x (e j)) (v (e j))) ≤ (1 / 2 : ℝ≥0∞) * volume (Tube δ (x (e i)) (v (e i)))

end WangZahlLot.Obl.wz_direction_density_transfer
