-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_balanced_small_slab_reduction.Interface.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
set_option linter.unusedVariables false

namespace WangZahlLot.Obl.wz_balanced_small_slab_reduction

abbrev Space := LeanEval.Analysis.WangZahlKakeya.Space

def B : Set Space := Metric.ball (0 : Space) 1

def T (δ : ℝ) (x v : Space) : Set Space := Metric.thickening δ (segment ℝ x (x + v))

def A : ℝ → ℝ → (n : ℕ) → (Fin n → Space) → (Fin n → Space) → (Fin n → Set Space) → Prop :=
  fun d δ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space) =>
  0 < n ∧ (∀ i, ‖v i‖ = 1) ∧ (∀ i, T δ (x i) (v i) ⊆ B) ∧
  (∀ i j, i ≠ j → MeasureTheory.volume (T δ (x i) (v i) ∩ T δ (x j) (v j)) ≤ (1/2 : ENNReal) * MeasureTheory.volume (T δ (x i) (v i))) ∧
  (∀ i, MeasurableSet (Y i)) ∧ (∀ i, Y i ⊆ T δ (x i) (v i)) ∧
  ENNReal.ofReal (d * (n : ℝ) * δ ^ 2) ≤ Finset.sum Finset.univ (fun i => MeasureTheory.volume (Y i))

def K : ℝ → ℝ → (n : ℕ) → (Fin n → Space) → (Fin n → Space) → Prop :=
  fun δ m (n : ℕ) (x v : Fin n → Space) =>
  ∀ Q : Set Space, Convex ℝ Q →
  ENNReal.ofReal ((Set.ncard {i | T δ (x i) (v i) ⊆ Q} : ℝ) * δ ^ 2) ≤ ENNReal.ofReal m * MeasureTheory.volume Q

def L : ℝ → ℝ → (n : ℕ) → (Fin n → Space) → (Fin n → Space) → Prop :=
  fun δ l (n : ℕ) (x v : Fin n → Space) =>
  ∀ (u : Space) (a r : ℝ), ‖u‖ = 1 → 0 < r →
  ENNReal.ofReal (Set.ncard {i | T δ (x i) (v i) ⊆ (B ∩ {p | |inner ℝ u p - a| ≤ r})} : ℝ) ≤
  ENNReal.ofReal (l * (n : ℝ)) * MeasureTheory.volume (B ∩ {p | |inner ℝ u p - a| ≤ r})

def R : ℝ → ℝ → ℝ → ℝ → (n k N q : ℕ) → (Fin n → Space) → (Fin n → Space) → (Fin k → Fin N → Space) → (Fin k → Fin N → Space) → Prop :=
  fun δ h ρ t (n k N q : ℕ) (x v : Fin n → Space) (z w : Fin k → Fin N → Space) =>
  ∃ (F : Fin k → Fin N → Finset (Fin n)) (f : Fin k → AffineEquiv ℝ Space Space),
  (∀ j a, (F j a).card = q) ∧
  (∀ j a b, a ≠ b → Disjoint (F j a) (F j b)) ∧
  h * (n : ℝ) ≤ (k : ℝ) * (N : ℝ) * (q : ℝ) ∧
  (∀ j a i, i ∈ F j a → T δ (x i) (v i) ⊆ f j '' T ρ (z j a) (w j a)) ∧
  (∀ j (Q : Set Space), Convex ℝ Q → MeasureTheory.volume (f j '' Q ∩ B) ≤ ENNReal.ofReal (t / h) * MeasureTheory.volume Q)

def SlabCover : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ (s : ℝ) (W : Set Space), 0 < s → Convex ℝ W → W ⊆ B →
  MeasureTheory.volume W ≤ ENNReal.ofReal s →
  (∃ x v : Space, ‖v‖ = 1 ∧ segment ℝ x (x + v) ⊆ W) →
  ∃ (u : Space) (a r : ℝ), ‖u‖ = 1 ∧ 0 < r ∧
  W ⊆ (B ∩ {p | |inner ℝ u p - a| ≤ r}) ∧
  MeasureTheory.volume (B ∩ {p | |inner ℝ u p - a| ≤ r}) ≤ ENNReal.ofReal (C * s ^ (1/2 : ℝ))

def Packing : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ (1/100 : ℝ) →
  ∀ (n : ℕ) (x v : Fin n → Space) (W : Set Space),
  Convex ℝ W → W ⊆ B → (∀ i, ‖v i‖ = 1) → (∀ i, T δ (x i) (v i) ⊆ W) →
  (∀ i j, i ≠ j → MeasureTheory.volume (T δ (x i) (v i) ∩ T δ (x j) (v j)) ≤ (1/2 : ENNReal) * MeasureTheory.volume (T δ (x i) (v i))) →
  ENNReal.ofReal ((n : ℝ) * δ ^ 4) ≤ ENNReal.ofReal C * (MeasureTheory.volume W) ^ 2

def Extraction : Prop :=
  ∀ e : ℝ, 0 < e → ∃ η : ℝ, 0 < η ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ (1/100 : ℝ) ∧
  ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
  A (δ ^ η) δ n x v Y →
  ∃ k N q : ℕ, 0 < k ∧ 0 < N ∧ 0 < q ∧ ∃ ρ t : ℝ,
  δ ^ (1 + e) ≤ ρ ∧ ρ ≤ (1/100 : ℝ) ∧ 0 < t ∧
  ∃ (z w : Fin k → Fin N → Space) (Z : Fin k → Fin N → Set Space),
  R δ (δ ^ e) ρ t n k N q x v z w ∧
  (∀ j, A (δ ^ e) ρ N (z j) (w j) (Z j) ∧ L ρ ((δ ^ e)⁻¹) N (z j) (w j)) ∧
  ENNReal.ofReal (δ ^ e * t) * Finset.sum Finset.univ (fun j => MeasureTheory.volume (⋃ a, Z j a)) ≤ MeasureTheory.volume (⋃ i, Y i)

def Counting : Prop :=
  SlabCover → Packing → ∃ C : ℝ, 1 ≤ C ∧
  ∀ δ ρ h t : ℝ, 0 < δ → δ ≤ (1/100 : ℝ) → 0 < ρ → ρ ≤ (1/100 : ℝ) → 0 < h → h ≤ 1 → 0 < t →
  ∀ n k N q : ℕ, 0 < n → 0 < k → 0 < N → 0 < q →
  ∀ (x v : Fin n → Space) (z w : Fin k → Fin N → Space),
  (∀ i, ‖v i‖ = 1) → (∀ i, T δ (x i) (v i) ⊆ B) →
  (∀ i j, i ≠ j → MeasureTheory.volume (T δ (x i) (v i) ∩ T δ (x j) (v j)) ≤ (1/2 : ENNReal) * MeasureTheory.volume (T δ (x i) (v i))) →
  (∀ j a, ‖w j a‖ = 1) → (∀ j a, T ρ (z j a) (w j a) ⊆ B) →
  R δ h ρ t n k N q x v z w → ∀ m l : ℝ, 1 ≤ m → 1 ≤ l → K δ m n x v → L δ l n x v →
  ∃ M : ℝ, 1 ≤ M ∧ (∀ j, K ρ M N (z j) (w j)) ∧
  M ≤ (C / h ^ 2) * m * ((k : ℝ) * t * (N : ℝ) * ρ ^ 2) / ((n : ℝ) * δ ^ 2) ∧
  h ^ 2 ≤ C * l * (k : ℝ) * t ^ (1/2 : ℝ) ∧
  δ ^ 2 * ((n : ℝ) / ((k : ℝ) * (N : ℝ))) ^ (1/2 : ℝ) ≤ (C / h ^ 2) * t * ρ ^ 2

def P (d δ m l : ℝ) (n : ℕ) (U : ENNReal) : Prop :=
  ∃ (x v : Fin n → Space) (Y : Fin n → Set Space),
    A d δ n x v Y ∧ K δ m n x v ∧ L δ l n x v ∧ U = MeasureTheory.volume (⋃ i, Y i)

def Reduction : Prop :=
  ∀ ζ : ℝ, 0 < ζ → ∃ η : ℝ, 0 < η ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ (1/100 : ℝ) ∧
  ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ m l : ℝ, 1 ≤ m → 1 ≤ l → ∀ (n : ℕ) (U : ENNReal),
  P (δ ^ η) δ m l n U → ∃ k N : ℕ, 0 < k ∧ 0 < N ∧ ∃ ρ t M : ℝ,
  δ ^ (1 + ζ) ≤ ρ ∧ ρ ≤ (1/100 : ℝ) ∧ 0 < t ∧ 1 ≤ M ∧ ∃ V : Fin k → ENNReal,
  (∀ j, P (δ ^ ζ) ρ M (δ ^ (-ζ)) N (V j)) ∧
  ENNReal.ofReal (δ ^ ζ * t) * Finset.sum Finset.univ V ≤ U ∧
  M ≤ δ ^ (-ζ) * m * ((k : ℝ) * t * (N : ℝ) * ρ ^ 2) / ((n : ℝ) * δ ^ 2) ∧
  δ ^ ζ ≤ l * (k : ℝ) * t ^ (1/2 : ℝ) ∧
  δ ^ 2 * ((n : ℝ) / ((k : ℝ) * (N : ℝ))) ^ (1/2 : ℝ) ≤ δ ^ (-ζ) * t * ρ ^ 2

end WangZahlLot.Obl.wz_balanced_small_slab_reduction
