-- Adapted from this LOT tree, o241, session x0834, branch x0834 at 511ef044.
-- Original file: Submission/Obl/k4_contact_equal_rate_affine_palettes/Model.lean
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.DepthPreparation

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover

open MeasureTheory Set Filter MvPolynomial
open Submission.Lib.K4ContactNormalization

/-- The data of the frozen prepared contact parent. -/
structure Model (α : Type*) [MeasurableSpace α] where
  N : ℕ → ℝ
  K : ℕ → ℝ
  d : ℝ
  κ : ℝ
  ℓ : ℝ
  S : ℝ
  U : ℝ
  e₀ : ℝ
  ν : ℕ → Measure α
  μ : ℕ → Measure (α × ℝ)
  ρ : ℕ → Measure (α × ℝ)
  π : ℕ → Measure ℝ
  b : ℕ → α → Fin 6 → ℝ
  P : ℕ → MvPolynomial (Fin 4) ℝ
  T : ℕ → ℝ → ℕ
  n : ℕ → ℝ → ℕ
  j : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (2 ^ T k s)
  A : (k : ℕ) → (s : ℝ) → Fin (n k s) → Set α
  B : (k : ℕ) → (s : ℝ) → Fin (n k s) → Set α
  c : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin 5 → ℝ
  F : (k : ℕ) → (s : ℝ) → Fin (n k s) → MvPolynomial (Fin 4) ℝ

namespace Model

variable {α : Type*} [MeasurableSpace α] (p : Model α)

def x (k : ℕ) (l : α) (t : ℝ) : Fin 4 → ℝ := point (p.b k l) t

def I (k : ℕ) (s : ℝ) (i : Fin (p.n k s)) : Set ℝ :=
  timeBlock (p.T k s) (p.j k s i)

def base (k : ℕ) (u : α × ℝ) : Fin 3 → ℝ :=
  ![u.2, p.x k u.1 u.2 1, p.x k u.1 u.2 2]

noncomputable def q (k : ℕ) (s : ℝ) : ℝ := (2 : ℝ) ^ (-(p.T k s : ℤ))

noncomputable def a (k : ℕ) (s : ℝ) : ℝ := p.N k ^ (-s)

noncomputable def g (k : ℕ) (s : ℝ) : ℝ := p.N k ^ (-p.ℓ * s)

noncomputable def z (k : ℕ) (r : ℝ) (v : α × ℝ) (e : Fin 3) : ℤ :=
  ⌊(![v.2, p.x k v.1 v.2 1, p.x k v.1 v.2 2] : Fin 3 → ℝ) e / (p.N k ^ (-r))⌋

def Fit (k : ℕ) (H a : ℝ) (Q : MvPolynomial (Fin 4) ℝ) (l : α) (J : Set ℝ) : Prop :=
  ∀ t ∈ J, |eval (p.x k l t) Q| ≤ H * a ∧
    |eval (p.x k l t) (pderiv 3 Q)| ≤ H ∧
    |eval (p.x k l t) (pderiv 3 (pderiv 3 Q))| ≤ H / a

def Basic : Prop := ∀ k,
  Measurable (p.b k) ∧ IsProbabilityMeasure (p.ν k) ∧ IsProbabilityMeasure (p.π k) ∧
  p.μ k ≤ ENNReal.ofReal (p.K k) • ((p.ν k).prod volume) ∧ p.ρ k ≤ p.μ k ∧
  p.μ k (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0 ∧
  ENNReal.ofReal ((p.K k)⁻¹) ≤ p.ρ k univ ∧ (p.P k).totalDegree ≤ 2 ∧
  (∀ᵐ l ∂p.ν k, |p.b k l 0| + |p.b k l 1| + |p.b k l 3| + |p.b k l 4| ≤ p.K k) ∧
  ∀ᵐ v ∂p.μ k,
    (∀ t ∈ Icc (0 : ℝ) 1, |eval (p.x k v.1 t) (p.P k)| ≤ p.K k ∧
      |eval (p.x k v.1 t) (pderiv 3 (p.P k))| ≤ p.K k ∧
      |eval (p.x k v.1 t) (pderiv 3 (pderiv 3 (p.P k)))| ≤ p.K k) ∧
    (p.K k)⁻¹ ≤ |eval (p.x k v.1 v.2) (pderiv 3 (p.P k))|

def Caps : Prop := ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop,
  ∀ r s v : ℝ, R⁻¹ ≤ r → r ≤ R → 0 ≤ s → s ≤ R → R⁻¹ ≤ v → v ≤ R →
  (∀ a : ℤ, p.π k {w : ℝ | ⌊w / (p.N k ^ (-v))⌋ = a} ≤
    ENNReal.ofReal (p.K k * p.N k ^ (-p.S * v))) ∧
  (∀ h : Bool, ∀ (q : Fin 3 → ℤ) (a : ℤ),
    p.μ k {u | p.z k r u = q ∧
      ⌊(if h then eval (p.x k u.1 u.2) (p.P k) else p.x k u.1 u.2 3) /
        (p.N k ^ (-s))⌋ = a} ≤ ENNReal.ofReal (p.K k * p.N k ^ (-3 * r - p.d * s))) ∧
  ∀ h : Bool, ∀ (q : Fin 3 → ℤ) (a v₀ : ℤ),
    p.μ k {u | p.z k r u = q ∧
      ⌊(if h then eval (p.x k u.1 u.2) (p.P k) else p.x k u.1 u.2 3) /
        (p.N k ^ (-s))⌋ = a ∧ ⌊p.b k u.1 3 / (p.N k ^ (-v))⌋ = v₀} ≤
      ENNReal.ofReal (p.K k * p.N k ^ (-3 * r - p.d * s)) *
        p.π k {w : ℝ | ⌊w / (p.N k ^ (-v))⌋ = v₀}

def Label (k : ℕ) (s : ℝ) (i : Fin (p.n k s)) : Prop :=
  ENNReal.ofReal (p.a k s ^ p.d * p.q k s ^ 2 * p.g k s / p.K k) ≤ p.ν k (p.A k s i) ∧
  p.ν k (p.A k s i) ≤ ENNReal.ofReal (p.K k * p.a k s ^ p.d * p.q k s ^ 2 * p.g k s) ∧
  ENNReal.ofReal (p.q k s / p.K k) * p.ν k (p.A k s i) ≤
    p.μ k (p.B k s i ×ˢ p.I k s i) ∧
  (∀ e, |p.c k s i e| ≤ p.K k) ∧ (p.F k s i).totalDegree ≤ 2 ∧
  (∀ l ∈ p.A k s i, ∀ t ∈ p.I k s i,
    |p.x k l t 1 - p.c k s i 0 - t * p.c k s i 1| ≤ p.K k * p.q k s ∧
    |p.x k l t 2 - p.c k s i 2 - t * p.c k s i 3 - p.c k s i 4 * p.x k l t 1| ≤
      p.K k * p.q k s * p.g k s ∧
    |p.b k l 4 - p.c k s i 3 - p.c k s i 4 * p.b k l 3| ≤ p.K k * p.g k s) ∧
  (∀ l ∈ p.B k s i, p.Fit k (p.K k) (p.a k s) (p.F k s i) l (p.I k s i)) ∧
  ∀ᵐ v ∂p.μ k, v.1 ∈ p.B k s i → v.2 ∈ p.I k s i →
    (p.K k)⁻¹ ≤ |eval (p.x k v.1 v.2) (pderiv 3 (p.F k s i))|

def Labels : Prop := ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop,
  ∀ s : ℝ, R⁻¹ ≤ s → s ≤ p.U →
    p.N k ^ (p.κ * s) / p.K k ≤ (2 : ℝ) ^ p.T k s ∧
    (2 : ℝ) ^ p.T k s ≤ p.K k * p.N k ^ (p.κ * s) ∧
    (∀ i, MeasurableSet (p.A k s i) ∧ MeasurableSet (p.B k s i) ∧ p.B k s i ⊆ p.A k s i) ∧
    (∀ i i', i ≠ i' → p.j k s i = p.j k s i' → Disjoint (p.A k s i) (p.A k s i')) ∧
    (∀ i, p.Label k s i) ∧
    (∀ᵐ v ∂p.μ k, ∃ i, v.1 ∈ p.B k s i ∧ v.2 ∈ p.I k s i) ∧
    ∀ (i : Fin (p.n k s)) (v : ℝ) (v₀ : ℤ), R⁻¹ ≤ v → v ≤ R →
      p.μ k {u | u.1 ∈ p.B k s i ∧ u.2 ∈ p.I k s i ∧
        ⌊p.b k u.1 3 / (p.N k ^ (-v))⌋ = v₀} ≤
      ENNReal.ofReal (p.K k * p.q k s) * p.ν k (p.A k s i) *
        p.π k {w : ℝ | ⌊w / (p.N k ^ (-v))⌋ = v₀}

def Nested : Prop := ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop,
  ∀ s t : ℝ, R⁻¹ ≤ s → s < t → t ≤ p.U → ∀ i : Fin (p.n k t),
    ∃ h : Fin (p.n k s), p.A k t i ⊆ p.A k s h ∧ p.I k t i ⊆ p.I k s h

structure Valid : Prop where
  N_ge : ∀ k, 2 ≤ p.N k
  N_lim : Tendsto p.N atTop atTop
  K_ge : ∀ k, 1 ≤ p.K k
  K_sub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, p.K k ≤ p.N k ^ ε
  d_nonneg : 0 ≤ p.d
  d_lt_one : p.d < 1
  κ_pos : 0 < p.κ
  κ_le_one : p.κ ≤ 1
  ℓ_pos : 0 < p.ℓ
  κ_le_ℓ : p.κ ≤ p.ℓ
  S_pos : 0 < p.S
  S_le_one : p.S ≤ 1
  U_pos : 0 < p.U
  e₀_pos : 0 < p.e₀
  contact : ∀ k, ∀ᵐ v ∂p.μ k, |p.b k v.1 4 + p.b k v.1 0| ≤ p.N k ^ (-p.e₀)
  basic : p.Basic
  caps : p.Caps
  labels : p.Labels
  nested : p.Nested
  equal_rate : p.ℓ = p.κ

end Model

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover
