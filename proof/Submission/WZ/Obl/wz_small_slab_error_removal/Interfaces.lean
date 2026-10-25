-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_small_slab_error_removal.Interfaces.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
set_option linter.unusedVariables false

namespace WangZahlLot.Obl.wz_small_slab_error_removal.Model

abbrev Tube : ℝ → LeanEval.Analysis.WangZahlKakeya.Space → LeanEval.Analysis.WangZahlKakeya.Space → Set LeanEval.Analysis.WangZahlKakeya.Space := fun δ x v => Metric.thickening δ (segment ℝ x (x + v))

def Admissible : ℝ → ℝ → (n : ℕ) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space) → Prop := fun d δ n x v Y =>
0 < n ∧ (∀ i, ‖v i‖ = 1) ∧
(∀ i, Tube δ (x i) (v i) ⊆ Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1) ∧
(∀ i j, i ≠ j → MeasureTheory.volume (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)) ≤ (1/2 : ENNReal) * MeasureTheory.volume (Tube δ (x i) (v i))) ∧
(∀ i, MeasurableSet (Y i)) ∧ (∀ i, Y i ⊆ Tube δ (x i) (v i)) ∧
ENNReal.ofReal (d * (n : ℝ) * δ ^ 2) ≤ Finset.sum Finset.univ (fun i => MeasureTheory.volume (Y i))

def Katz : ℝ → ℝ → (n : ℕ) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → Prop := fun δ m n x v => ∀ W : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W →
ENNReal.ofReal ((Set.ncard {i | Tube δ (x i) (v i) ⊆ W} : ℝ) * δ ^ 2) ≤ ENNReal.ofReal m * MeasureTheory.volume W

def Slab : ℝ → ℝ → (n : ℕ) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → Prop := fun δ l n x v => ∀ (u : LeanEval.Analysis.WangZahlKakeya.Space) (t r : ℝ), ‖u‖ = 1 → 0 < r →
ENNReal.ofReal (Set.ncard {i | Tube δ (x i) (v i) ⊆ (Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1 ∩ {p | |inner ℝ u p - t| ≤ r})} : ℝ) ≤ ENNReal.ofReal (l * (n : ℝ)) * MeasureTheory.volume (Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1 ∩ {p | |inner ℝ u p - t| ≤ r})

def Family : ℝ → ℝ → ℝ → ℝ → ℕ → ENNReal → Prop := fun d δ m l n U =>
  ∃ (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space),
  Admissible d δ n x v Y ∧ Katz δ m n x v ∧ Slab δ l n x v ∧ U = MeasureTheory.volume (⋃ i, Y i)

def Packing : Prop := ∃ C : ℝ, 1 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ (1/100 : ℝ) →
∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (W : Set LeanEval.Analysis.WangZahlKakeya.Space), Convex ℝ W →
W ⊆ Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1 → (∀ i, ‖v i‖ = 1) →
(∀ i, Tube δ (x i) (v i) ⊆ W) →
(∀ i j, i ≠ j → MeasureTheory.volume (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)) ≤ (1/2 : ENNReal) * MeasureTheory.volume (Tube δ (x i) (v i))) →
ENNReal.ofReal ((n : ℝ) * δ ^ 4) ≤ ENNReal.ofReal C * (MeasureTheory.volume W) ^ 2

def Reduction (P : ℝ → ℝ → ℝ → ℝ → ℕ → ENNReal → Prop) : Prop := ∀ ζ : ℝ, 0 < ζ → ∃ η : ℝ, 0 < η ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ (1/100 : ℝ) ∧
∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ m l : ℝ, 1 ≤ m → 1 ≤ l →
∀ (n : ℕ) (U : ENNReal), P (δ ^ η) δ m l n U →
∃ k N : ℕ, 0 < k ∧ 0 < N ∧ ∃ ρ t M : ℝ,
δ ^ (1 + ζ) ≤ ρ ∧ ρ ≤ (1/100 : ℝ) ∧ 0 < t ∧ 1 ≤ M ∧
∃ V : Fin k → ENNReal, (∀ j, P (δ ^ ζ) ρ M (δ ^ (-ζ)) N (V j)) ∧
ENNReal.ofReal (δ ^ ζ * t) * Finset.sum Finset.univ V ≤ U ∧
M ≤ δ ^ (-ζ) * m * ((k : ℝ) * t * (N : ℝ) * ρ ^ 2) / ((n : ℝ) * δ ^ 2) ∧
δ ^ ζ ≤ l * (k : ℝ) * t ^ (1/2 : ℝ) ∧
δ ^ 2 * ((n : ℝ) / ((k : ℝ) * (N : ℝ))) ^ (1/2 : ℝ) ≤ δ ^ (-ζ) * t * ρ ^ 2

def MonotoneFamily (P : ℝ → ℝ → ℝ → ℝ → ℕ → ENNReal → Prop) : Prop := ∀ d d' δ m l l' : ℝ, d' ≤ d → l ≤ l' →
∀ (n : ℕ) (U : ENNReal), P d δ m l n U → P d' δ m l' n U

def Bounds (P : ℝ → ℝ → ℝ → ℝ → ℕ → ENNReal → Prop) (C : ℝ) : Prop := ∀ d δ m l : ℝ, 0 < δ → δ ≤ (1/100 : ℝ) → 1 ≤ m →
∀ (n : ℕ) (U : ENNReal), P d δ m l n U →
0 < n ∧ (n : ℝ) * δ ^ 4 ≤ C ∧ (n : ℝ) * δ ^ 2 ≤ C * m ∧
ENNReal.ofReal (d * δ ^ 2) ≤ U

def Estimates : (ℝ → ℝ → ℝ → ℝ → Prop) → Prop := fun Q => ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧
∀ δ : ℝ, 0 < δ → δ ≤ (1/100 : ℝ) → Q ε a η δ

def Restricted (P : ℝ → ℝ → ℝ → ℝ → ℕ → ENNReal → Prop) (σ ω : ℝ) : Prop := Estimates (fun ε a η δ => ∀ m : ℝ, 1 ≤ m → ∀ (n : ℕ) (U : ENNReal),
P (δ ^ η) δ m (δ ^ (-η)) n U →
ENNReal.ofReal (a * δ ^ (ω + ε) * m⁻¹ * ((n : ℝ) * δ ^ 2) * (m ^ (-(3/2 : ℝ)) * ((n : ℝ) * δ)) ^ (-σ)) ≤ U)

def General (P : ℝ → ℝ → ℝ → ℝ → ℕ → ENNReal → Prop) (σ ω : ℝ) : Prop := Estimates (fun ε a η δ => ∀ m l : ℝ, 1 ≤ m → 1 ≤ l → ∀ (n : ℕ) (U : ENNReal),
P (δ ^ η) δ m l n U →
ENNReal.ofReal (a * δ ^ (ω + ε) * m⁻¹ * ((n : ℝ) * δ ^ 2) * (m ^ (-(3/2 : ℝ)) * l * ((n : ℝ) * δ)) ^ (-σ)) ≤ U)

end WangZahlLot.Obl.wz_small_slab_error_removal.Model
