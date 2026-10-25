-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_balanced_affine_tube_packets.Interfaces.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
/-! Concrete witness predicates for the three stages of affine packet extraction.
Their bodies are expanded in the frozen child types. -/
namespace WangZahlLot.Obl.wz_balanced_affine_tube_packets

abbrev E := LeanEval.Analysis.WangZahlKakeya.Space

def ball : Set E :=
  Metric.ball (0 : E) 1

def tube : ℝ → E → E → Set E :=
  fun δ x v => Metric.thickening δ (segment ℝ x (x + v))

def admissible : ℝ → ℝ → (n : ℕ) → (Fin n → E) → (Fin n → E) → (Fin n → Set E) → Prop :=
  fun d δ n x v Y =>
  0 < n ∧
  (∀ i, ‖v i‖ = 1) ∧
  (∀ i, tube δ (x i) (v i) ⊆ ball) ∧
  (∀ i j, i ≠ j →
    MeasureTheory.volume (tube δ (x i) (v i) ∩ tube δ (x j) (v j)) ≤
      (1/2 : ENNReal) * MeasureTheory.volume (tube δ (x i) (v i))) ∧
  (∀ i, MeasurableSet (Y i)) ∧
  (∀ i, Y i ⊆ tube δ (x i) (v i)) ∧
  ENNReal.ofReal (d * (n : ℝ) * δ ^ 2) ≤
    Finset.sum Finset.univ (fun i => MeasureTheory.volume (Y i))

def slab : ℝ → ℝ → (n : ℕ) → (Fin n → E) → (Fin n → E) → Prop :=
  fun δ l n x v =>
  ∀ (u : E) (a r : ℝ), ‖u‖ = 1 → 0 < r →
    ENNReal.ofReal (Set.ncard {i : Fin n |
      tube δ (x i) (v i) ⊆ (ball ∩ {p | |inner ℝ u p - a| ≤ r})} : ℝ) ≤
    ENNReal.ofReal (l * (n : ℝ)) *
      MeasureTheory.volume (ball ∩ {p | |inner ℝ u p - a| ≤ r})

def packet : ℝ → ℝ → ℝ → ℝ → (n k N q : ℕ) → (Fin n → E) → (Fin n → E) → (Fin k → Fin N → E) → (Fin k → Fin N → E) → Prop :=
  fun δ h ρ t n k N q x v z w =>
  ∃ (F : Fin k → Fin N → Finset (Fin n))
    (f : Fin k → AffineEquiv ℝ E E),
    (∀ j a, (F j a).card = q) ∧
    (∀ j a b, a ≠ b → Disjoint (F j a) (F j b)) ∧
    h * (n : ℝ) ≤ (k : ℝ) * (N : ℝ) * (q : ℝ) ∧
    (∀ j a i, i ∈ F j a →
      tube δ (x i) (v i) ⊆ f j '' tube ρ (z j a) (w j a)) ∧
    (∀ j (Q : Set E), Convex ℝ Q →
      MeasureTheory.volume (f j '' Q ∩ ball) ≤
        ENNReal.ofReal (t / h) * MeasureTheory.volume Q)

def prism : ℝ → ℝ → E → (Fin 3 → E) → Set E :=
  fun a b c u =>
  {p | |inner ℝ (u 0) (p - c)| ≤ a ∧
       |inner ℝ (u 1) (p - c)| ≤ b ∧
       |inner ℝ (u 2) (p - c)| ≤ (1/1000 : ℝ)}

def cells : ℝ → ℝ → (n : ℕ) → (Fin n → E) → (Fin n → E) → (Fin n → Set E) → Prop :=
  fun δ h n x v Y =>
  0 < n ∧ (n : ℝ) ≤ δ ^ (-100 : ℝ) ∧
  ∃ m : ℕ, 0 < m ∧
  ∃ (I : Fin m → Finset (Fin n))
    (f : Fin m → AffineEquiv ℝ E E)
    (D : Fin m → ℝ) (a b : ℝ)
    (c : Fin m → Fin n → E)
    (u : Fin m → Fin n → Fin 3 → E)
    (H : Fin m → Fin n → Set E),
    δ ^ (100 : ℕ) ≤ a ∧ a ≤ b ∧ b ≤ (1/1000000 : ℝ) ∧
    δ * h ≤ b ∧
    (∀ j, (I j).Nonempty) ∧
    h * (n : ℝ) ≤ Finset.sum Finset.univ (fun j => ((I j).card : ℝ)) ∧
    (∀ j, δ ^ (100 : ℕ) ≤ D j ∧ D j ≤ δ ^ (-100 : ℝ)) ∧
    (∀ j (Q : Set E), MeasureTheory.volume (f j '' Q) =
      ENNReal.ofReal (D j) * MeasureTheory.volume Q) ∧
    (∀ j i, i ∈ I j → Orthonormal ℝ (u j i)) ∧
    (∀ j i, i ∈ I j → prism a b (c j i) (u j i) ⊆ Metric.ball (0 : E) (1/100)) ∧
    (∀ j i, i ∈ I j →
      tube δ (x i) (v i) ⊆ f j '' prism a b (c j i) (u j i)) ∧
    (∀ j i, i ∈ I j → MeasurableSet (H j i)) ∧
    (∀ j i, i ∈ I j →
      H j i ⊆ prism a b (c j i) (u j i) ∩ f j ⁻¹' (Y i)) ∧
    (∀ j i, i ∈ I j →
      ENNReal.ofReal h * MeasureTheory.volume (prism a b (c j i) (u j i)) ≤
        MeasureTheory.volume (H j i)) ∧
    (∀ j i, i ∈ I j → ∀ p : E, p ∈ H j i → ∀ r : ℝ, a ≤ r → r ≤ 1 →
      ENNReal.ofReal h *
        MeasureTheory.volume (prism a b (c j i) (u j i) ∩ Metric.ball p r) ≤
      MeasureTheory.volume (H j i ∩ Metric.ball p r)) ∧
    (∀ j (p : E), (∃ i : Fin n, i ∈ I j ∧ p ∈ H j i) →
      ∃ i i' : Fin n, i ∈ I j ∧ i' ∈ I j ∧ p ∈ H j i ∧ p ∈ H j i' ∧
        h ≤ a / b + min ‖u j i 0 - u j i' 0‖ ‖u j i 0 + u j i' 0‖) ∧
    (∀ j (ν : E) (s r : ℝ), ‖ν‖ = 1 → 0 < r →
      ENNReal.ofReal (Set.ncard {i : Fin n | i ∈ I j ∧
        prism a b (c j i) (u j i) ⊆ (ball ∩ {p | |inner ℝ ν p - s| ≤ r})} : ℝ) ≤
      ENNReal.ofReal (h⁻¹ * ((I j).card : ℝ)) *
        MeasureTheory.volume (ball ∩ {p | |inner ℝ ν p - s| ≤ r})) ∧
    (∀ j j', j ≠ j' →
      Disjoint (f j '' (⋃ i ∈ I j, H j i)) (f j' '' (⋃ i ∈ I j', H j' i)))

def weighted : ℝ → ℝ → (n : ℕ) → (Fin n → E) → (Fin n → E) → (Fin n → Set E) → Prop :=
  fun δ h n x v Y =>
  0 < n ∧ (n : ℝ) ≤ δ ^ (-100 : ℝ) ∧
  ∃ m : ℕ, 0 < m ∧
  ∃ ρ : ℝ, 0 < ρ ∧ δ * h ≤ ρ ∧ ρ ≤ (1/100 : ℝ) ∧
  ∃ (M : Fin m → ℕ)
    (f : Fin m → AffineEquiv ℝ E E)
    (D : Fin m → ℝ)
    (z w : (j : Fin m) → Fin (M j) → E)
    (Z : (j : Fin m) → Fin (M j) → Set E)
    (F : (j : Fin m) → Fin (M j) → Finset (Fin n)),
    (∀ j, 0 < M j) ∧
    (∀ j, δ ^ (100 : ℕ) ≤ D j ∧ D j ≤ δ ^ (-100 : ℝ)) ∧
    (∀ j (Q : Set E), MeasureTheory.volume (f j '' Q) =
      ENNReal.ofReal (D j) * MeasureTheory.volume Q) ∧
    (∀ j a, ‖w j a‖ = 1) ∧
    (∀ j a, tube ρ (z j a) (w j a) ⊆ ball) ∧
    (∀ j a b, a ≠ b →
      MeasureTheory.volume (tube ρ (z j a) (w j a) ∩ tube ρ (z j b) (w j b)) ≤
        (1/2 : ENNReal) * MeasureTheory.volume (tube ρ (z j a) (w j a))) ∧
    (∀ j a, MeasurableSet (Z j a)) ∧
    (∀ j a, Z j a ⊆ tube ρ (z j a) (w j a)) ∧
    (∀ j a, ENNReal.ofReal (h * ρ ^ 2) ≤ MeasureTheory.volume (Z j a)) ∧
    (∀ j a, (F j a).Nonempty) ∧
    (∀ j a b, a ≠ b → Disjoint (F j a) (F j b)) ∧
    (∀ j a i, i ∈ F j a →
      tube δ (x i) (v i) ⊆ f j '' tube ρ (z j a) (w j a)) ∧
    h * (n : ℝ) ≤ Finset.sum Finset.univ
      (fun j => Finset.sum Finset.univ (fun a => ((F j a).card : ℝ))) ∧
    (∀ j (ν : E) (s r : ℝ), ‖ν‖ = 1 → 0 < r →
      ENNReal.ofReal (Set.ncard {i : Fin n | ∃ a : Fin (M j), i ∈ F j a ∧
        tube ρ (z j a) (w j a) ⊆ (ball ∩ {p | |inner ℝ ν p - s| ≤ r})} : ℝ) ≤
      ENNReal.ofReal (h⁻¹ * Finset.sum Finset.univ (fun a => ((F j a).card : ℝ))) *
        MeasureTheory.volume (ball ∩ {p | |inner ℝ ν p - s| ≤ r})) ∧
    Finset.sum Finset.univ (fun j =>
      ENNReal.ofReal (D j) * MeasureTheory.volume (⋃ a, Z j a)) ≤
        MeasureTheory.volume (⋃ i, Y i)

def conclusion : ℝ → ℝ → (n : ℕ) → (Fin n → E) → (Fin n → E) → (Fin n → Set E) → Prop :=
  fun e δ n x v Y =>
  ∃ k N q : ℕ, 0 < k ∧ 0 < N ∧ 0 < q ∧
  ∃ ρ t : ℝ, δ ^ (1 + e) ≤ ρ ∧ ρ ≤ (1/100 : ℝ) ∧ 0 < t ∧
  ∃ (z w : Fin k → Fin N → E) (Z : Fin k → Fin N → Set E),
    packet δ (δ ^ e) ρ t n k N q x v z w ∧
    (∀ j, admissible (δ ^ e) ρ N (z j) (w j) (Z j) ∧
      slab ρ ((δ ^ e)⁻¹) N (z j) (w j)) ∧
    ENNReal.ofReal (δ ^ e * t) *
      Finset.sum Finset.univ (fun j => MeasureTheory.volume (⋃ a, Z j a)) ≤
        MeasureTheory.volume (⋃ i, Y i)

end WangZahlLot.Obl.wz_balanced_affine_tube_packets
