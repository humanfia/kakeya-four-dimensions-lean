import Mathlib

namespace Submission.Obl.k4_horizontal_supercritical_three_projections

open MeasureTheory Set Filter
open scoped ENNReal BigOperators

noncomputable section

/-- The original, unchanged trajectories and true packet assignments. -/
structure HorizontalModel (α : Type) [MeasurableSpace α] where
  N : ℕ → ℝ
  K : ℕ → ℝ
  d : ℝ
  κ : ℝ
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

namespace HorizontalModel

variable {α : Type} [MeasurableSpace α] (m : HorizontalModel α)

def x (k : ℕ) (l : α) (t : ℝ) : Fin 4 → ℝ :=
  ![t, m.b k l 0 + t * m.b k l 3, m.b k l 1 + t * m.b k l 4,
    m.b k l 2 + t * m.b k l 5]

def I (T : ℕ) (j : Fin (2 ^ T)) : Set ℝ :=
  Icc (((j : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T)

def z (k : ℕ) (Nk r : ℝ) (p : α × ℝ) (e : Fin 3) : ℤ :=
  ⌊(![p.2, (m.x k p.1 p.2) 1, (m.x k p.1 p.2) 2] : Fin 3 → ℝ) e / (Nk ^ (-r))⌋

def fit (k : ℕ) (H a : ℝ) (Q : MvPolynomial (Fin 4) ℝ) (l : α) (J : Set ℝ) : Prop :=
  ∀ t ∈ J, |MvPolynomial.eval (m.x k l t) Q| ≤ H * a ∧
    |MvPolynomial.eval (m.x k l t) (MvPolynomial.pderiv (3 : Fin 4) Q)| ≤ H ∧
    |MvPolynomial.eval (m.x k l t)
      (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) Q))| ≤ H / a

/-- Original priors, domination and bounded-trajectory hypotheses. -/
def Basic : Prop := ∀ k,
  Measurable (m.b k) ∧ IsProbabilityMeasure (m.ν k) ∧ IsProbabilityMeasure (m.π k) ∧
  m.μ k ≤ ENNReal.ofReal (m.K k) • ((m.ν k).prod volume) ∧ m.ρ k ≤ m.μ k ∧
  m.μ k (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0 ∧ ENNReal.ofReal ((m.K k)⁻¹) ≤ m.ρ k univ ∧
  (m.P k).totalDegree ≤ 2 ∧
  (∀ᵐ l ∂m.ν k, |m.b k l 0| + |m.b k l 1| + |m.b k l 3| + |m.b k l 4| ≤ m.K k) ∧
  (∀ᵐ p ∂m.μ k,
    (∀ t ∈ Icc (0 : ℝ) 1,
      |MvPolynomial.eval (m.x k p.1 t) (m.P k)| ≤ m.K k ∧
      |MvPolynomial.eval (m.x k p.1 t) (MvPolynomial.pderiv (3 : Fin 4) (m.P k))| ≤ m.K k ∧
      |MvPolynomial.eval (m.x k p.1 t)
        (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (m.P k)))| ≤ m.K k) ∧
    (m.K k)⁻¹ ≤ |MvPolynomial.eval (m.x k p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (m.P k))|)

/-- Uniform original pure and joint mesh caps. -/
def Caps : Prop := ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∀ r s v : ℝ,
  R⁻¹ ≤ r → r ≤ R → 0 ≤ s → s ≤ R → R⁻¹ ≤ v → v ≤ R →
  (∀ a : ℤ, m.π k {w : ℝ | ⌊w / (m.N k ^ (-v))⌋ = a} ≤
    ENNReal.ofReal (m.K k * m.N k ^ (-m.S * v))) ∧
  (∀ h : Bool, ∀ (q : Fin 3 → ℤ) (a : ℤ),
    m.μ k {p | m.z k (m.N k) r p = q ∧
      ⌊(if h then MvPolynomial.eval (m.x k p.1 p.2) (m.P k)
        else (m.x k p.1 p.2) 3) / (m.N k ^ (-s))⌋ = a} ≤
      ENNReal.ofReal (m.K k * m.N k ^ (-3 * r - m.d * s))) ∧
  (∀ h : Bool, ∀ (q : Fin 3 → ℤ) (a v₀ : ℤ),
    m.μ k {p | m.z k (m.N k) r p = q ∧
      ⌊(if h then MvPolynomial.eval (m.x k p.1 p.2) (m.P k)
        else (m.x k p.1 p.2) 3) / (m.N k ^ (-s))⌋ = a ∧
      ⌊m.b k p.1 3 / (m.N k ^ (-v))⌋ = v₀} ≤
      ENNReal.ofReal (m.K k * m.N k ^ (-3 * r - m.d * s)) *
        m.π k {w : ℝ | ⌊w / (m.N k ^ (-v))⌋ = v₀})

/-- The finite true labels, including their full-domain witnesses and
horizontal affine fits, at one fixed depth. -/
def AtDepth (k : ℕ) (s : ℝ) (R : ℝ) : Prop :=
  let q := (2 : ℝ) ^ (-(m.T k s : ℤ))
  let a := m.N k ^ (-s)
  let g := m.N k ^ (-m.κ * s)
  m.N k ^ (m.κ * s) / m.K k ≤ (2 : ℝ) ^ m.T k s ∧
  (2 : ℝ) ^ m.T k s ≤ m.K k * m.N k ^ (m.κ * s) ∧
  (∀ i, MeasurableSet (m.A k s i) ∧ MeasurableSet (m.B k s i) ∧ m.B k s i ⊆ m.A k s i) ∧
  (∀ i i', i ≠ i' → m.j k s i = m.j k s i' → Disjoint (m.A k s i) (m.A k s i')) ∧
  (∀ i,
    ENNReal.ofReal (a ^ m.d * q ^ 2 * g / m.K k) ≤ m.ν k (m.A k s i) ∧
    m.ν k (m.A k s i) ≤ ENNReal.ofReal (m.K k * a ^ m.d * q ^ 2 * g) ∧
    ENNReal.ofReal (q / m.K k) * m.ν k (m.A k s i) ≤
      m.μ k (m.B k s i ×ˢ I (m.T k s) (m.j k s i)) ∧
    (∀ e, |m.c k s i e| ≤ m.K k) ∧ (m.F k s i).totalDegree ≤ 2 ∧
    (∀ l ∈ m.A k s i, ∀ t ∈ I (m.T k s) (m.j k s i),
      |(m.x k l t) 1 - m.c k s i 0 - t * m.c k s i 1| ≤ m.K k * q ∧
      |(m.x k l t) 2 - m.c k s i 2 - t * m.c k s i 3 - m.c k s i 4 * (m.x k l t) 1| ≤
        m.K k * q * g ∧
      |m.b k l 4 - m.c k s i 3 - m.c k s i 4 * m.b k l 3| ≤ m.K k * g) ∧
    (∀ l ∈ m.B k s i, m.fit k (m.K k) a (m.F k s i) l (I (m.T k s) (m.j k s i))) ∧
    (∀ᵐ p ∂m.μ k, p.1 ∈ m.B k s i → p.2 ∈ I (m.T k s) (m.j k s i) →
      (m.K k)⁻¹ ≤ |MvPolynomial.eval (m.x k p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (m.F k s i))|) ∧
    (true = true →
      m.P k = MvPolynomial.X (3 : Fin 4) ∧
      (∀ᵐ p ∂m.μ k, |m.b k p.1 4 + m.b k p.1 0| ≤ m.N k ^ (-m.e₀)) ∧
      |m.c k s i 3 + m.c k s i 0 + ((m.j k s i : ℕ) + (1 : ℝ) / 2) * q * m.c k s i 1| +
        |m.c k s i 4 - ((m.j k s i : ℕ) + (1 : ℝ) / 2) * q| ≤ m.K k * q ∧
      (∃ L : Fin 4 → ℝ,
        m.F k s i = MvPolynomial.X (3 : Fin 4) -
          (MvPolynomial.C (L 0) + MvPolynomial.C (L 1) * MvPolynomial.X (0 : Fin 4) +
            MvPolynomial.C (L 2) * MvPolynomial.X (1 : Fin 4) +
            MvPolynomial.C (L 3) * MvPolynomial.X (2 : Fin 4)) ∧
        |L 3| ≤ m.K k * (1 + a / q ^ 2) ∧
        ∀ l ∈ m.B k s i, ∀ t ∈ I (m.T k s) (m.j k s i),
          |L 1 - (m.x k l t) 1 * L 3| + |L 2 + t * L 3| ≤ m.K k * (1 + a / q)))) ∧
  (∀ᵐ p ∂m.μ k, ∃ i, p.1 ∈ m.B k s i ∧ p.2 ∈ I (m.T k s) (m.j k s i)) ∧
  (∀ (i : Fin (m.n k s)) (v : ℝ) (v₀ : ℤ), R⁻¹ ≤ v → v ≤ R →
    m.μ k {p | p.1 ∈ m.B k s i ∧ p.2 ∈ I (m.T k s) (m.j k s i) ∧
      ⌊m.b k p.1 3 / (m.N k ^ (-v))⌋ = v₀} ≤
      ENNReal.ofReal (m.K k * q) * m.ν k (m.A k s i) *
        m.π k {w : ℝ | ⌊w / (m.N k ^ (-v))⌋ = v₀})

def Prepared : Prop := ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop,
  ∀ s : ℝ, R⁻¹ ≤ s → s ≤ m.U → m.AtDepth k s R

def Nested : Prop := ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop,
  ∀ s t : ℝ, R⁻¹ ≤ s → s < t → t ≤ m.U → ∀ i : Fin (m.n k t),
    ∃ h : Fin (m.n k s), m.A k t i ⊆ m.A k s h ∧
      I (m.T k t) (m.j k t i) ⊆ I (m.T k s) (m.j k s h)

structure Valid : Prop where
  N_ge : ∀ k, 2 ≤ m.N k
  N_tendsto : Tendsto m.N atTop atTop
  K_ge : ∀ k, 1 ≤ m.K k
  K_subpower : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, m.K k ≤ m.N k ^ ε
  d_nonneg : 0 ≤ m.d
  d_lt : m.d < 1
  κ_pos : 0 < m.κ
  κ_le : m.κ ≤ 1
  S_pos : 0 < m.S
  S_le : m.S ≤ 1
  U_pos : 0 < m.U
  e₀_pos : 0 < m.e₀
  supercritical : 1 < 2 * m.κ
  basic : m.Basic
  caps : m.Caps
  prepared : m.Prepared
  nested : m.Nested

/-- The original residual is dense at every fixed positive power. -/
theorem Valid.residual_dense (h : m.Valid) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k in atTop, ENNReal.ofReal (m.N k ^ (-η)) ≤ m.ρ k univ := by
  filter_upwards [h.K_subpower η hη] with k hk
  apply (ENNReal.ofReal_le_ofReal ?_).trans (h.basic k).2.2.2.2.2.2.1
  rw [Real.rpow_neg (by linarith [h.N_ge k] : 0 ≤ m.N k)]
  exact inv_anti₀ (by linarith [h.K_ge k]) hk

end HorizontalModel
end
end Submission.Obl.k4_horizontal_supercritical_three_projections
