-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonflat_factored_improvement.Basic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
namespace WangZahlLot.Obl.wz_nonflat_factored_improvement

open MeasureTheory

abbrev Space := EuclideanSpace ℝ (Fin 3)

abbrev unitBall : Set Space := Metric.ball 0 1

abbrev tube (δ : ℝ) (x v : Space) : Set Space :=
  Metric.thickening δ (segment ℝ x (x + v))

abbrev ConvexCount (δ m : ℝ) {n : ℕ} (x v : Fin n → Space) : Prop :=
  ∀ U : Set Space, Convex ℝ U →
    ENNReal.ofReal ((Set.ncard {i | tube δ (x i) (v i) ⊆ U} : ℝ) * δ ^ 2) ≤
      ENNReal.ofReal m * volume U

abbrev SlabCount (δ l : ℝ) {n : ℕ} (x v : Fin n → Space) : Prop :=
  ∀ (u : Space) (t r : ℝ), ‖u‖ = 1 → 0 < r →
    ENNReal.ofReal (Set.ncard {i | tube δ (x i) (v i) ⊆
      (unitBall ∩ {p | |inner ℝ u p - t| ≤ r})} : ℝ) ≤
    ENNReal.ofReal (l * n) * volume (unitBall ∩ {p | |inner ℝ u p - t| ≤ r})

/-- The geometric and density hypotheses, in the continuation form of the frozen type. -/
abbrev FamilyHypotheses (η δ : ℝ) (n : ℕ) (x v : Fin n → Space)
    (Y : Fin n → Set Space) (P : Prop) : Prop :=
  0 < n → (∀ i, ‖v i‖ = 1) → (∀ i, tube δ (x i) (v i) ⊆ unitBall) →
    (∀ i j, i ≠ j → volume (tube δ (x i) (v i) ∩ tube δ (x j) (v j)) ≤
      (1 / 2 : ENNReal) * volume (tube δ (x i) (v i))) →
    (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ tube δ (x i) (v i)) →
    ENNReal.ofReal (δ ^ η * n * δ ^ 2) ≤ ∑ i, volume (Y i) → P

abbrev CountHypotheses (δ m l : ℝ) (n : ℕ) (x v : Fin n → Space) (P : Prop) : Prop :=
  ConvexCount δ m x v → SlabCount δ l x v → P

abbrev UniformEstimate (P : ℝ → ℝ → ℝ → ℝ → Prop) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 < A ∧ ∃ η : ℝ, 0 < η ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → P ε A η δ

abbrev AtScale (η δ m l : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
    FamilyHypotheses η δ n x v Y
      (CountHypotheses δ m l n x v (ENNReal.ofReal (f n) ≤ volume (⋃ i, Y i)))

abbrev EstimateD (σ ω : ℝ) : Prop :=
  UniformEstimate fun ε A η δ =>
    AtScale η δ (δ ^ (-η)) (δ ^ (-η))
      (fun N => A * δ ^ (ω + ε) * (N * δ ^ 2) * (N * δ) ^ (-σ))

abbrev EstimateE (σ u : ℝ) : Prop :=
  UniformEstimate fun ε A η δ =>
    ∀ m l : ℝ, 1 ≤ m → 1 ≤ l → AtScale η δ m l
      (fun N => A * δ ^ (u + ε) * m⁻¹ * (N * δ ^ 2) *
        (m ^ (-(3 / 2 : ℝ)) * l * (N * δ)) ^ (-σ))

abbrev standardPrism (a b : ℝ) : Set Space :=
  {p | |p 0| ≤ a ∧ |p 1| ≤ b ∧ |p 2| ≤ 2}

/-- The precise saturated factorization supplied in the statement. -/
abbrev Factorization (ν δ a b m : ℝ) (n : ℕ) (x v : Fin n → Space) : Prop :=
  ∃ (k : ℕ) (g : Fin k → Fin n), Function.Injective g ∧ 0 < k ∧ δ ^ ν * n ≤ k ∧
    ∃ c : ℝ, 1 ≤ c ∧ c ≤ m ∧
      ConvexCount δ c (fun i => x (g i)) (fun i => v (g i)) ∧
    ∃ q : ℕ, 0 < q ∧ ∃ W : Fin q → Set Space,
      (∀ j, ∃ e : AffineIsometryEquiv ℝ Space Space, W j = e '' standardPrism a b) ∧
      (∀ i, ∃ j, tube δ (x (g i)) (v (g i)) ⊆ W j) ∧
      (∀ i, (Set.ncard {j | tube δ (x (g i)) (v (g i)) ⊆ W j} : ℝ) ≤ δ ^ (-ν)) ∧
      (∀ j j', (Set.ncard {i | tube δ (x (g i)) (v (g i)) ⊆ W j} : ℝ) ≤
        δ ^ (-ν) * (Set.ncard {i | tube δ (x (g i)) (v (g i)) ⊆ W j'} : ℝ)) ∧
      (∀ j, δ ^ ν * c * a * b ≤
        (Set.ncard {i | tube δ (x (g i)) (v (g i)) ⊆ W j} : ℝ) * δ ^ 2) ∧
      (∀ U : Set Space, Convex ℝ U →
        ENNReal.ofReal ((Set.ncard {j | W j ⊆ U} : ℝ) * a * b) ≤
          ENNReal.ofReal (δ ^ (-ν)) * volume U) ∧
      (∀ j, ∀ U : Set Space, Convex ℝ U →
        ENNReal.ofReal ((Set.ncard {i | tube δ (x (g i)) (v (g i)) ⊆ W j ∧
          tube δ (x (g i)) (v (g i)) ⊆ U} : ℝ) * a * b) ≤
        ENNReal.ofReal (δ ^ (-ν) *
          (Set.ncard {i | tube δ (x (g i)) (v (g i)) ⊆ W j} : ℝ)) * volume U)

noncomputable abbrev weight (σ δ m : ℝ) (n : ℕ) : ℝ :=
  m⁻¹ * (n * δ ^ 2) * (m ^ (-(3 / 2 : ℝ)) * (n * δ)) ^ (-σ)

noncomputable abbrev target (σ w ε A δ m : ℝ) (n : ℕ) : ENNReal :=
  ENNReal.ofReal (A * δ ^ (w + ε) * m⁻¹ * (n * δ ^ 2) *
    (m ^ (-(3 / 2 : ℝ)) * (n * δ)) ^ (-σ))

/-- All inputs below the last three existential choices in the frozen conclusion. -/
abbrev FactoredBound (β ν δ m : ℝ) (n : ℕ) (x v : Fin n → Space)
    (Y : Fin n → Set Space) (P : ℝ → ℝ → Prop) : Prop :=
  FamilyHypotheses ν δ n x v Y (CountHypotheses δ m (δ ^ (-ν)) n x v
    ((∀ i, ENNReal.ofReal (δ ^ ν * δ ^ 2) ≤ volume (Y i)) →
      ∀ a b : ℝ, δ ≤ a → a ≤ b → b ≤ 2 → Factorization ν δ a b m n x v →
        δ ^ β * b < a → P a b))

theorem weight_nonneg {δ m : ℝ} (hδ : 0 ≤ δ) (hm : 0 ≤ m) (σ : ℝ) (n : ℕ) :
    0 ≤ weight σ δ m n := by
  dsimp [weight]
  positivity

theorem target_eq_weight (σ w ε A δ m : ℝ) (n : ℕ) :
    target σ w ε A δ m n = ENNReal.ofReal (A * δ ^ (w + ε) * weight σ δ m n) := by
  unfold target weight
  congr 1
  ring

end WangZahlLot.Obl.wz_nonflat_factored_improvement
