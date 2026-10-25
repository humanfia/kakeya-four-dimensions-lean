-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_rescaled_tube_estimate.Interfaces.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
set_option linter.unusedVariables false

noncomputable section

namespace WangZahlLot.Obl.wz_rescaled_tube_estimate.Interfaces

def o :=
  ENNReal.ofReal

def q :=
  fun {n : ℕ} (s : Set (Fin n)) => (Set.ncard s : ℝ)

abbrev V :=
  LeanEval.Analysis.WangZahlKakeya.Space

def ι :=
  fun (p : V) (i : Fin 3) => p i

def μ :=
  (MeasureTheory.volume : MeasureTheory.Measure V)

def I :=
  Metric.ball (0 : V) 1

def T :=
  fun (d : ℝ) (p q : V) => Metric.thickening d (segment ℝ p (p + q))

def X :=
  fun (d : ℝ) (n : ℕ) (x v : Fin n → V) => ∀ i j, i ≠ j → μ (T d (x i) (v i) ∩ T d (x j) (v j)) ≤ 1 / 2 * μ (T d (x i) (v i))

def K :=
  fun (d m : ℝ) (n : ℕ) (x v : Fin n → V) => ∀ W, Convex ℝ W → o (q {i | T d (x i) (v i) ⊆ W} * d ^ 2) ≤ o m * μ W

def F :=
  fun (d l : ℝ) (n : ℕ) (x v : Fin n → V) => ∀ (u : V) (t r : ℝ), ‖u‖ = 1 → 0 < r → o (q {i | T d (x i) (v i) ⊆ I ∩ {p | |inner ℝ u p - t| ≤ r}}) ≤ o (l * n) * μ (I ∩ {p | |inner ℝ u p - t| ≤ r})

def A :=
  fun (d η m l : ℝ) (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V) => 0 < n ∧ (∀ i, ‖v i‖ = 1 ∧ T d (x i) (v i) ⊆ I ∧ MeasurableSet (Y i) ∧ Y i ⊆ T d (x i) (v i)) ∧ X d n x v ∧ o (d ^ η * n * d ^ 2) ≤ ∑ i, μ (Y i) ∧ K d m n x v ∧ F d l n x v

def P :=
  fun (a b c : ℝ) (z : V) (e : V ≃ₗᵢ[ℝ] V) => {p : V | |(ι (e (p - z))) 0| ≤ a / 2 ∧ |(ι (e (p - z))) 1| ≤ b / 2 ∧ |(ι (e (p - z))) 2| ≤ c / 2}

def B :=
  fun (d ρ l : ℝ) (n N : ℕ) (x v : Fin n → V) (S : Finset (Fin n)) (y w : Fin N → V) (f : Fin n → Fin N) => ∀ k, (fun (D : Set V) => ∀ (u : V) (t r : ℝ), ‖u‖ = 1 → 0 < r → o (q {i | i ∈ S ∧ f i = k ∧ T d (x i) (v i) ⊆ D ∩ {p | |inner ℝ u p - t| ≤ r}}) * μ D ≤ o (l * q {i | i ∈ S ∧ f i = k}) * μ (D ∩ {p | |inner ℝ u p - t| ≤ r})) (T (2 * ρ) (y k - (1 / 2 : ℝ) • w k) (2 • w k))

def C :=
  fun (d h : ℝ) (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V) (S : Finset (Fin n)) (Z : Fin n → Set V) (ρ : ℝ) (N : ℕ) (y w : Fin N → V) (f : Fin n → Fin N) => (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i ∧ (i ∉ S → Z i = ∅)) ∧ o (d ^ h) * ∑ i, μ (Y i) ≤ ∑ i ∈ S, μ (Z i) ∧ (∀ k, ‖w k‖ = 1) ∧ (∀ i ∈ S, T d (x i) (v i) ⊆ T ρ (y (f i)) (w (f i))) ∧ F ρ (d ^ (-h)) N y w ∧ B d ρ (d ^ (-h)) n N x v S y w f ∧ (∀ k k', q {i | i ∈ S ∧ f i = k} ≤ d ^ (-h) * q {i | i ∈ S ∧ f i = k'}) ∧ X ρ N y w ∧ (∀ i ∈ S, q {k | T d (x i) (v i) ⊆ T ρ (y k) (w k)} ≤ d ^ (-h))

def G :=
  fun (ω d h : ℝ) (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V) (S : Finset (Fin n)) (Z : Fin n → Set V) (ρ : ℝ) (N : ℕ) (y w : Fin N → V) (f : Fin n → Fin N) => C d h n x v Y S Z ρ N y w f ∧ d ^ (1 - ω / 100) ≤ ρ ∧ ρ ≤ d ^ (ω / 100) ∧ ∃ (a c : ℝ) (L : ℕ) (z : Fin L → V) (e : Fin L → V ≃ₗᵢ[ℝ] V) (H : Fin L → Set V) (g : Fin L → Fin N) (m : ℝ), (fun (U : Fin L → Set V) => d ≤ a ∧ a ≤ ρ * c ∧ ρ * c ≤ c ∧ c ≤ 1 ∧ (∀ j, MeasurableSet (H j) ∧ H j ⊆ U j ∧ U j ⊆ T ρ (y (g j)) (w (g j)) ∧ ((ι (e j (w (g j)))) 0) ^ 2 + ((ι (e j (w (g j)))) 1) ^ 2 ≤ (10 * ρ) ^ 2) ∧ (∀ j j', j ≠ j' → g j = g j' → Disjoint (H j) (H j')) ∧ (∀ k, {p | ∃ j, g j = k ∧ p ∈ H j} = {p | ∃ i ∈ S, f i = k ∧ p ∈ Z i}) ∧ o (d ^ h * L * a * (ρ * c) * c) ≤ ∑ j, μ (H j) ∧ (∀ k p, (∃ i ∈ S, f i = k ∧ p ∈ Z i) → q {i | i ∈ S ∧ f i = k ∧ p ∈ Z i} ∈ Set.Icc m (2 * m)) ∧ (∀ i ∈ S, ∀ j, f i = g j → (Z i ∩ H j).Nonempty → Z i ∩ U j ⊆ H j ∧ (∀ p ∈ T d (x i) (v i) ∩ frontier (U j), |(ι (e j (p - z j))) 2| = c / 2) ∧ (∀ t ∈ ({-c / 2, c / 2} : Set ℝ), ∃ p ∈ T d (x i) (v i) ∩ U j, (ι (e j (p - z j))) 2 = t)) ∧ d ^ h * (ρ / d) * (N : ℝ) / n ≤ c ∧ (∀ j W, Convex ℝ W → o (q {j' | P (a / ρ) c c (z j') (e j') ⊆ P (2 * a / ρ) (2 * c) (2 * c) (z j) (e j) ∧ U j' ⊆ W} * (a * (ρ * c) * c)) ≤ o (d ^ (-h)) * μ W)) (fun j => P a (ρ * c) c (z j) (e j))

def E :=
  fun (σ ω : ℝ) => ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ m l : ℝ, 1 ≤ m → 1 ≤ l → ∀ n x v Y, A δ η m l n x v Y → o (a * δ ^ (ω + ε) * m⁻¹ * (n * δ ^ 2) * (m ^ (-(3 / 2 : ℝ)) * l * (n * δ)) ^ (-σ)) ≤ μ (⋃ i, Y i)

def J :=
  fun (σ ω : ℝ) => ∀ ε : ℝ, 0 < ε → ∃ κ : ℝ, 0 < κ ∧ ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ n x v Y, A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y → ∀ ρ : ℝ, δ ≤ ρ → ρ ≤ 1 → ∀ N y w f, C δ η n x v Y Finset.univ Y ρ N y w f → ∀ a b : ℝ, ρ ≤ a → a ≤ b → b ≤ 1 → ∀ (L : ℕ) (z : Fin L → V) (e : Fin L → V ≃ₗᵢ[ℝ] V) (g : Fin N → Fin L), (fun (U : Fin L → Set V) => (∀ k, T ρ (y k) (w k) ⊆ U (g k)) → (∀ j j', q {k | g k = j} ≤ δ ^ (-η) * q {k | g k = j'}) → (∀ k, q {j | T ρ (y k) (w k) ⊆ U j} ≤ δ ^ (-η)) → (∀ W, Convex ℝ W → o (q {j | U j ⊆ W} * (a * b)) ≤ o (δ ^ (-η)) * μ W) → (∀ j W, Convex ℝ W → o (q {k | g k = j ∧ T ρ (y k) (w k) ⊆ U j ∩ W}) * μ (U j) ≤ o (δ ^ (-η) * q {k | g k = j}) * μ (U j ∩ W)) → o (κ * δ ^ (ω + ε) * (b / a) ^ ω * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤ μ (⋃ i, Y i)) (fun j => P a b 2 (z j) (e j))

def R :=
  fun (σ ω : ℝ) => ∀ ε : ℝ, 0 < ε → ∃ κ : ℝ, 0 < κ ∧ ∃ η : ℝ, 0 < η ∧ ∀ δ ρ : ℝ, 0 < δ → δ ≤ 1 / 100 → δ ≤ ρ → ρ ≤ 1 → ∀ m l : ℝ, 1 ≤ m → 1 ≤ l → ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V) (y w : V), 0 < n → ‖w‖ = 1 → (∀ i, ‖v i‖ = 1 ∧ T δ (x i) (v i) ⊆ T ρ y w ∧ MeasurableSet (Y i) ∧ Y i ⊆ T δ (x i) (v i)) → X δ n x v → o (δ ^ η * n * δ ^ 2) ≤ ∑ i, μ (Y i) → K δ m n x v → B δ ρ l n 1 x v Finset.univ (fun _ => y) (fun _ => w) (fun _ => 0) → o (κ * δ ^ ε * (δ / ρ) ^ ω * m⁻¹ * (n * δ ^ 2) * (m ^ (-(3 / 2 : ℝ)) * l * (n * δ / ρ)) ^ (-σ)) ≤ μ (⋃ i, Y i)

end WangZahlLot.Obl.wz_rescaled_tube_estimate.Interfaces
