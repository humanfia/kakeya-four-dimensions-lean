-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_factored_improvement.Types.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_tower_balanced_refinement
import Submission.WZ.Obl.wz_flat_factored_improvement.Scalar

namespace WangZahlLot.Obl.wz_flat_factored_improvement

open MeasureTheory Set Metric
open scoped ENNReal

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev Tube := WangZahlLot.Obl.wz_tower_balanced_refinement.Tube
abbrev ConvexCount := WangZahlLot.Obl.wz_tower_balanced_refinement.ConvexCount
abbrev SlabCount := WangZahlLot.Obl.wz_tower_balanced_refinement.SlabCount
abbrev Admissible := WangZahlLot.Obl.wz_tower_balanced_refinement.Admissible

/-- The individual density normalization is exactly the one in the frozen problem. -/
def IndividuallyDense (ν δ : ℝ) {n : ℕ} (Y : Fin n → Set Space) : Prop :=
  ∀ i, ENNReal.ofReal (δ ^ ν * δ ^ 2) ≤ volume (Y i)

/-- Balanced, saturated, almost partitioning prism cover of the retained family. -/
def PrismCover (ν δ a b c : ℝ) (n : ℕ) (x v : Fin n → Space) : Prop :=
  ∃ q : ℕ, 0 < q ∧ ∃ W : Fin q → Set Space,
    (∀ j, ∃ e : AffineIsometryEquiv ℝ Space Space,
      W j = e '' {p : Space | |p 0| ≤ a ∧ |p 1| ≤ b ∧ |p 2| ≤ 2}) ∧
    (∀ i, ∃ j, Tube δ (x i) (v i) ⊆ W j) ∧
    (∀ i, (Set.ncard {j | Tube δ (x i) (v i) ⊆ W j} : ℝ) ≤ δ ^ (-ν)) ∧
    (∀ j j', (Set.ncard {i | Tube δ (x i) (v i) ⊆ W j} : ℝ) ≤
      δ ^ (-ν) * (Set.ncard {i | Tube δ (x i) (v i) ⊆ W j'} : ℝ)) ∧
    (∀ j, δ ^ ν * c * a * b ≤
      (Set.ncard {i | Tube δ (x i) (v i) ⊆ W j} : ℝ) * δ ^ 2) ∧
    (∀ U : Set Space, Convex ℝ U →
      ENNReal.ofReal ((Set.ncard {j | W j ⊆ U} : ℝ) * a * b) ≤
        ENNReal.ofReal (δ ^ (-ν)) * volume U) ∧
    (∀ j, ∀ U : Set Space, Convex ℝ U →
      ENNReal.ofReal ((Set.ncard {i | Tube δ (x i) (v i) ⊆ W j ∧
        Tube δ (x i) (v i) ⊆ U} : ℝ) * a * b) ≤
      ENNReal.ofReal (δ ^ (-ν) *
        (Set.ncard {i | Tube δ (x i) (v i) ⊆ W j} : ℝ)) * volume U)

/-- The frozen factorization, including the retained subfamily and its own coefficient. -/
def Factorization (ν δ a b m : ℝ) (n : ℕ) (x v : Fin n → Space) : Prop :=
  ∃ (k : ℕ) (g : Fin k → Fin n), Function.Injective g ∧ 0 < k ∧
    δ ^ ν * (n : ℝ) ≤ k ∧ ∃ c : ℝ, 1 ≤ c ∧ c ≤ m ∧
    ConvexCount δ c k (x ∘ g) (v ∘ g) ∧
    PrismCover ν δ a b c k (x ∘ g) (v ∘ g)

/-- The general tube estimate assumed by o065, with the admissibility hypotheses bundled. -/
def TubeEstimate (σ u : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 < A ∧ ∃ η : ℝ, 0 < η ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ m l : ℝ, 1 ≤ m → 1 ≤ l →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
    Admissible δ η m l n x v Y →
    ENNReal.ofReal (profile σ u ε A δ m l n) ≤ volume (⋃ i, Y i)

/-- The quantitative geometric estimate required from Proposition 5.1(A).

This is a proposition, not an assumed theorem. `Aspect.lean` establishes it
from the tube estimate using the fine and coarse body bounds.
-/
def AspectRatioEstimate (σ u : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 < A ∧ ∃ η : ℝ, 0 < η ∧
    ∃ d : ℝ, 0 < d ∧ ∀ ν : ℝ, 0 < ν → ν ≤ η →
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → δ ≤ d →
    ∀ c l : ℝ, 1 ≤ c → 1 ≤ l →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
    Admissible δ ν c l n x v Y → IndividuallyDense ν δ Y →
    ∀ a b : ℝ, δ ≤ a → a ≤ b → b ≤ 2 → PrismCover ν δ a b c n x v →
    ENNReal.ofReal ((b / a) ^ u * profile σ u ε A δ c l n) ≤ volume (⋃ i, Y i)

/-- The conclusion of o065, expressed without the nested lambda abbreviations. -/
def FlatConclusion (σ u : ℝ) : Prop :=
  ∀ β : ℝ, 0 < β → ∃ α : ℝ, 0 < α ∧
    ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 < A ∧ ∃ η : ℝ, 0 < η ∧
    ∃ d : ℝ, 0 < d ∧ ∀ ν : ℝ, 0 < ν → ν ≤ η →
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → δ ≤ d → ∀ m : ℝ, 1 ≤ m →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
    Admissible δ ν m (δ ^ (-ν)) n x v Y → IndividuallyDense ν δ Y →
    ∀ a b : ℝ, δ ≤ a → a ≤ b → b ≤ 2 → Factorization ν δ a b m n x v →
    a ≤ δ ^ β * b →
    ENNReal.ofReal (profile σ (u - α) ε A δ m 1 n) ≤ volume (⋃ i, Y i)

end WangZahlLot.Obl.wz_flat_factored_improvement
