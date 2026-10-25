-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Model; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
import Submission.Obl.k4_critical_intercept_concentration.PreparedModel
import Submission.Lib.K4QuadSheetMatching.Matching

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set Filter
open scoped ENNReal BigOperators

noncomputable section

/-- Reuse the original data and candidate predicate. No horizontal hypothesis
is part of this structure. -/
abbrev Parent := Submission.Obl.k4_critical_intercept_concentration.Data

namespace Parent

abbrev block := Submission.Obl.k4_critical_intercept_concentration.Data.I

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- The full true assignment at a fixed depth in the general model. -/
def AtDepth (k : ℕ) (s R : ℝ) : Prop :=
  let q := (2 : ℝ) ^ (-(p.T k s : ℤ))
  let a := p.N k ^ (-s)
  let g := p.N k ^ (-p.ℓ * s)
  p.N k ^ (p.κ * s) / p.K k ≤ (2 : ℝ) ^ p.T k s ∧
  (2 : ℝ) ^ p.T k s ≤ p.K k * p.N k ^ (p.κ * s) ∧
  (∀ i, MeasurableSet (p.A k s i) ∧ MeasurableSet (p.B k s i) ∧ p.B k s i ⊆ p.A k s i) ∧
  (∀ i i', i ≠ i' → p.j k s i = p.j k s i' → Disjoint (p.A k s i) (p.A k s i')) ∧
  (∀ i,
    ENNReal.ofReal (a ^ p.d * q ^ 2 * g / p.K k) ≤ p.ν k (p.A k s i) ∧
    p.ν k (p.A k s i) ≤ ENNReal.ofReal (p.K k * a ^ p.d * q ^ 2 * g) ∧
    ENNReal.ofReal (q / p.K k) * p.ν k (p.A k s i) ≤
      p.μ k (p.B k s i ×ˢ block (p.T k s) (p.j k s i)) ∧
    (∀ e, |p.c k s i e| ≤ p.K k) ∧ (p.F k s i).totalDegree ≤ 2 ∧
    (∀ l ∈ p.A k s i, ∀ t ∈ block (p.T k s) (p.j k s i),
      |(p.x k l t) 1 - p.c k s i 0 - t * p.c k s i 1| ≤ p.K k * q ∧
      |(p.x k l t) 2 - p.c k s i 2 - t * p.c k s i 3 - p.c k s i 4 * (p.x k l t) 1| ≤
        p.K k * q * g ∧
      |p.b k l 4 - p.c k s i 3 - p.c k s i 4 * p.b k l 3| ≤ p.K k * g) ∧
    (∀ l ∈ p.B k s i, p.fit k (p.K k) a (p.F k s i) l (block (p.T k s) (p.j k s i))) ∧
    (∀ᵐ ω ∂p.μ k, ω.1 ∈ p.B k s i → ω.2 ∈ block (p.T k s) (p.j k s i) →
      (p.K k)⁻¹ ≤ |MvPolynomial.eval (p.x k ω.1 ω.2) (MvPolynomial.pderiv (3 : Fin 4) (p.F k s i))|)) ∧
  (∀ᵐ ω ∂p.μ k, ∃ i, ω.1 ∈ p.B k s i ∧ ω.2 ∈ block (p.T k s) (p.j k s i)) ∧
  (∀ (i : Fin (p.n k s)) (v : ℝ) (v₀ : ℤ), R⁻¹ ≤ v → v ≤ R →
    p.μ k {ω | ω.1 ∈ p.B k s i ∧ ω.2 ∈ block (p.T k s) (p.j k s i) ∧
      ⌊p.b k ω.1 3 / (p.N k ^ (-v))⌋ = v₀} ≤
      ENNReal.ofReal (p.K k * q) * p.ν k (p.A k s i) *
        p.π k {w : ℝ | ⌊w / (p.N k ^ (-v))⌋ = v₀})

def Prepared : Prop := ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop,
  ∀ s : ℝ, R⁻¹ ≤ s → s ≤ p.U → p.AtDepth k s R

structure Valid : Prop where
  scale : ∀ k, 2 ≤ p.N k
  scale_limit : Tendsto p.N atTop atTop
  subpower : (∀ k, 1 ≤ p.K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, p.K k ≤ p.N k ^ ε
  dimension_nonneg : 0 ≤ p.d
  dimension_lt_one : p.d < 1
  rate_pos : 0 < p.κ
  rate_le_one : p.κ ≤ 1
  transverse_pos : 0 < p.ℓ
  palette_pos : 0 < p.S
  palette_le_one : p.S ≤ 1
  depth_pos : 0 < p.U
  defect_pos : 0 < p.e₀
  basic : p.Basic
  caps : p.Caps
  prepared : p.Prepared
  nested : p.Nested

/-- The exact finite-depth wide projected preparation in the frozen input. -/
def WideLayers : Prop :=
  ∃ L : ℝ, 2 < L ∧ ∀ a : ℝ, 0 < a → L * a < p.U →
    ∀ D : Finset ℝ, (∀ s ∈ D, a ≤ s ∧ s ≤ 2 * a) → ∀ m : ℝ, L * a < m →
    ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∃ H : ℕ → ℝ,
      (∀ k, 1 ≤ H k ∧ p.K (τ k) ≤ H k) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ p.N (τ k) ^ ε) ∧
    ∃ (ρ' : ℕ → Measure (α × ℝ)) (β : ℕ → ℝ → ℝ) (n' : ℕ → ℝ → ℕ)
      (C : (k : ℕ) → (s : ℝ) → Fin (n' k s) → Set α)
      (tag : (k : ℕ) → (s : ℝ) → Fin (n' k s) → Fin 2 → ℤ)
      (u v : (k : ℕ) → (s : ℝ) → Fin (n' k s) → ℝ)
      (G : (k : ℕ) → (s : ℝ) → Fin (n' k s) → MvPolynomial (Fin 2) ℝ),
      (∀ k, ρ' k ≤ p.ρ (τ k) ∧ ENNReal.ofReal ((H k)⁻¹) ≤ ρ' k univ) ∧
      ∀ k s, s ∈ D →
      0 < β k s ∧ p.N (τ k) ^ (-p.ℓ * s) / H k ≤ β k s ∧
      β k s ≤ H k * p.N (τ k) ^ (-p.ℓ * s) ∧
      (∀ i, MeasurableSet (C k s i)) ∧
      (∀ i i', i ≠ i' → Disjoint (C k s i) (C k s i')) ∧
      (∀ i, |u k s i| + |v k s i| ≤ H k ∧ (G k s i).totalDegree ≤ 2 ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1,
          |MvPolynomial.eval ![t, u k s i + t * v k s i + β k s * w] (G k s i)| ≤ H k) ∧
        (∀ l ∈ C k s i,
          ⌊p.b (τ k) l 3 / (p.N (τ k) ^ (-m))⌋ = tag k s i 0 ∧
          ⌊p.b (τ k) l 0 / (p.N (τ k) ^ (-m))⌋ = tag k s i 1 ∧
          ∀ t ∈ Icc (0 : ℝ) 1,
            |(p.x (τ k) l t) 2 - u k s i - t * v k s i| ≤ H k * β k s ∧
            |MvPolynomial.eval (p.x (τ k) l t) (p.P (τ k)) -
              MvPolynomial.eval ![t, (p.x (τ k) l t) 2] (G k s i)| ≤ H k * p.N (τ k) ^ (-s)) ∧
        ENNReal.ofReal (p.N (τ k) ^ (-m) * (p.N (τ k) ^ (-s)) ^ p.d * β k s / H k) *
          p.π (τ k) {w : ℝ | ⌊w / (p.N (τ k) ^ (-m))⌋ = tag k s i 0} ≤
          p.ρ (τ k) (C k s i ×ˢ Icc (0 : ℝ) 1)) ∧
      (∑ i : Fin (n' k s),
        ENNReal.ofReal (p.N (τ k) ^ (-m) * (p.N (τ k) ^ (-s)) ^ p.d * β k s) *
          p.π (τ k) {w : ℝ | ⌊w / (p.N (τ k) ^ (-m))⌋ = tag k s i 0}) ≤ ENNReal.ofReal (H k) ∧
      (∀ᵐ ω ∂ρ' k, ∃ i, ω.1 ∈ C k s i)

end Parent
end
end Submission.Obl.k4_general_compared_layers_velocity_lists
