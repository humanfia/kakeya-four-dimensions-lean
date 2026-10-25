-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.Types.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

open MeasureTheory

abbrev E := LeanEval.Analysis.WangZahlKakeya.Space

/-- The original open tube around a unit segment. -/
def tube (δ : ℝ) (x v : E) : Set E :=
  Metric.thickening δ (segment ℝ x (x + v))

/-- The normalized closed prism, with the fixed long half-width in the frozen type. -/
def prism (a b : ℝ) (c : E) (u : Fin 3 → E) : Set E :=
  {p | |inner ℝ (u 0) (p - c)| ≤ a ∧
       |inner ℝ (u 1) (p - c)| ≤ b ∧
       |inner ℝ (u 2) (p - c)| ≤ (1 / 1000 : ℝ)}

/-- The input predicate, including the original indexed essential distinctness condition. -/
def Admissible (d δ : ℝ) (n : ℕ) (x v : Fin n → E) (Y : Fin n → Set E) : Prop :=
  0 < n ∧
  (∀ i, ‖v i‖ = 1) ∧
  (∀ i, tube δ (x i) (v i) ⊆ Metric.ball (0 : E) 1) ∧
  (∀ i j, i ≠ j → volume (tube δ (x i) (v i) ∩ tube δ (x j) (v j)) ≤
    (1 / 2 : ENNReal) * volume (tube δ (x i) (v i))) ∧
  (∀ i, MeasurableSet (Y i)) ∧
  (∀ i, Y i ⊆ tube δ (x i) (v i)) ∧
  ENNReal.ofReal (d * (n : ℝ) * δ ^ 2) ≤ ∑ i, volume (Y i)

/-- The cell certificate in the frozen output predicate. -/
def Cells (δ h : ℝ) (n : ℕ) (x v : Fin n → E) (Y : Fin n → Set E) : Prop :=
  0 < n ∧
  (n:ℝ) ≤ δ ^ (-100:ℝ) ∧
  ∃ m:ℕ,0 < m ∧
  ∃ (I:Fin m → Finset (Fin n)) (f:Fin m → AffineEquiv ℝ E E) (D:Fin m → ℝ) (a b:ℝ) (c:Fin m → Fin n → E) (u:Fin m → Fin n → Fin 3 → E) (H:Fin m → Fin n → Set E),δ ^ (100:ℕ) ≤ a ∧
  a ≤ b ∧
  b ≤ (1/1000000:ℝ) ∧
  δ * h ≤ b ∧
  (∀ j,(I j).Nonempty) ∧
  h * (n:ℝ) ≤ Finset.sum Finset.univ (fun j => ((I j).card:ℝ)) ∧
  (∀ j,δ ^ (100:ℕ) ≤ D j ∧
  D j ≤ δ ^ (-100:ℝ)) ∧
  (∀ j (Q:Set E),MeasureTheory.volume (f j '' Q) = ENNReal.ofReal (D j) * MeasureTheory.volume Q) ∧
  (∀ j i,i ∈ I j → Orthonormal ℝ (u j i)) ∧
  (∀ j i,i ∈ I j → prism a b (c j i) (u j i) ⊆ Metric.ball (0 : E) (1/100)) ∧
  (∀ j i,i ∈ I j → tube δ (x i) (v i) ⊆ f j '' prism a b (c j i) (u j i)) ∧
  (∀ j i,i ∈ I j → MeasurableSet (H j i)) ∧
  (∀ j i,i ∈ I j → H j i ⊆ prism a b (c j i) (u j i) ∩ f j ⁻¹' (Y i)) ∧
  (∀ j i,i ∈ I j → ENNReal.ofReal h * MeasureTheory.volume (prism a b (c j i) (u j i)) ≤ MeasureTheory.volume (H j i)) ∧
  (∀ j i,i ∈ I j → ∀ p:E,p ∈ H j i → ∀ r:ℝ,a ≤ r → r ≤ 1 → ENNReal.ofReal h * MeasureTheory.volume (prism a b (c j i) (u j i) ∩ Metric.ball p r) ≤ MeasureTheory.volume (H j i ∩ Metric.ball p r)) ∧
  (∀ j (p:E),(∃ i:Fin n,i ∈ I j ∧
  p ∈ H j i) → ∃ i i':Fin n,i ∈ I j ∧
  i' ∈ I j ∧
  p ∈ H j i ∧
  p ∈ H j i' ∧
  h ≤ a / b + min ‖u j i 0 - u j i' 0‖ ‖u j i 0 + u j i' 0‖) ∧
  (∀ j (ν:E) (s r:ℝ),‖ν‖ = 1 → 0 < r → ENNReal.ofReal (Set.ncard {i:Fin n | i ∈ I j ∧
  prism a b (c j i) (u j i) ⊆ (Metric.ball (0 : E) 1 ∩ {p | |inner ℝ ν p - s| ≤ r})}:ℝ) ≤ ENNReal.ofReal (h⁻¹ * ((I j).card:ℝ)) * MeasureTheory.volume (Metric.ball (0 : E) 1 ∩ {p | |inner ℝ ν p - s| ≤ r})) ∧
  (∀ j j',j ≠ j' → Disjoint (f j '' (⋃ i ∈ I j,H j i)) (f j' '' (⋃ i ∈ I j',H j' i)))

end WangZahlLot.Obl.wz_regular_transverse_affine_cells
