/- Adapted from our LOT tree o211, session x0736, commit fb9fb2638e83e4e42cdf985859ec4b5deb228222,
`Submission/Obl/k4_critical_affine_derivative_preparation/PreparedModel.lean`.
Earlier provenance comments in that file are retained below. -/

import Mathlib
import ChallengeDeps

/-! Adapted from our LOT tree o201, session x0697, PreparedModel.lean
(commit be1e3254). -/

namespace Submission.Obl.k4_critical_conditional_row_preparation

open MeasureTheory

noncomputable section

/-! Field-named frozen data; all bounds use the original measures. -/

structure Data (α : Type) [MeasurableSpace α] where
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

namespace Data

variable {α : Type} [MeasurableSpace α] (cfg : Data α)

def x (k : ℕ) (l : α) (t : ℝ) : Fin 4 → ℝ :=
  ![t, cfg.b k l 0 + t * cfg.b k l 3, cfg.b k l 1 + t * cfg.b k l 4,
    cfg.b k l 2 + t * cfg.b k l 5]

def I (T : ℕ) (j : Fin (2 ^ T)) : Set ℝ :=
  Set.Icc (((j : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T)

def z (k : ℕ) (Nk r : ℝ) (q : α × ℝ) (e : Fin 3) : ℤ :=
  ⌊(![q.2, (cfg.x k q.1 q.2) 1, (cfg.x k q.1 q.2) 2] : Fin 3 → ℝ) e / (Nk ^ (-r))⌋

def fit (k : ℕ) (H a : ℝ) (Q : MvPolynomial (Fin 4) ℝ) (l : α) (I : Set ℝ) : Prop :=
  ∀ t ∈ I, |MvPolynomial.eval (cfg.x k l t) Q| ≤ H * a ∧
    |MvPolynomial.eval (cfg.x k l t) (MvPolynomial.pderiv (3 : Fin 4) Q)| ≤ H ∧
    |MvPolynomial.eval (cfg.x k l t)
      (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) Q))| ≤ H / a

def Basic : Prop :=
  (∀ k, Measurable (cfg.b k) ∧ MeasureTheory.IsProbabilityMeasure (cfg.ν k) ∧ MeasureTheory.IsProbabilityMeasure (cfg.π k) ∧ cfg.μ k ≤ ENNReal.ofReal (cfg.K k) • ((cfg.ν k).prod MeasureTheory.volume) ∧ cfg.ρ k ≤ cfg.μ k ∧ cfg.μ k (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧ ENNReal.ofReal ((cfg.K k)⁻¹) ≤ cfg.ρ k Set.univ ∧ (cfg.P k).totalDegree ≤ 2 ∧ (∀ᵐ l ∂cfg.ν k, |cfg.b k l 0| + |cfg.b k l 1| + |cfg.b k l 3| + |cfg.b k l 4| ≤ cfg.K k) ∧ (∀ᵐ p ∂cfg.μ k, (∀ t ∈ Set.Icc (0 : ℝ) 1, |MvPolynomial.eval (cfg.x k p.1 t) (cfg.P k)| ≤ cfg.K k ∧ |MvPolynomial.eval (cfg.x k p.1 t) (MvPolynomial.pderiv (3 : Fin 4) (cfg.P k))| ≤ cfg.K k ∧ |MvPolynomial.eval (cfg.x k p.1 t) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (cfg.P k)))| ≤ cfg.K k) ∧ (cfg.K k)⁻¹ ≤ |MvPolynomial.eval (cfg.x k p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (cfg.P k))|))

def Caps : Prop :=
  (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ r s v : ℝ, R⁻¹ ≤ r → r ≤ R → 0 ≤ s → s ≤ R → R⁻¹ ≤ v → v ≤ R → (∀ a : ℤ, cfg.π k {w : ℝ | ⌊w / (cfg.N k ^ (-v))⌋ = a} ≤ ENNReal.ofReal (cfg.K k * cfg.N k ^ (-cfg.S * v))) ∧ (∀ h : Bool, ∀ (q : Fin 3 → ℤ) (a : ℤ), cfg.μ k {p | cfg.z k (cfg.N k) r p = q ∧ ⌊(if h then MvPolynomial.eval (cfg.x k p.1 p.2) (cfg.P k) else (cfg.x k p.1 p.2) 3) / (cfg.N k ^ (-s))⌋ = a} ≤ ENNReal.ofReal (cfg.K k * cfg.N k ^ (-3 * r - cfg.d * s))) ∧ (∀ h : Bool, ∀ (q : Fin 3 → ℤ) (a v₀ : ℤ), cfg.μ k {p | cfg.z k (cfg.N k) r p = q ∧ ⌊(if h then MvPolynomial.eval (cfg.x k p.1 p.2) (cfg.P k) else (cfg.x k p.1 p.2) 3) / (cfg.N k ^ (-s))⌋ = a ∧ ⌊cfg.b k p.1 3 / (cfg.N k ^ (-v))⌋ = v₀} ≤ ENNReal.ofReal (cfg.K k * cfg.N k ^ (-3 * r - cfg.d * s)) * cfg.π k {w : ℝ | ⌊w / (cfg.N k ^ (-v))⌋ = v₀}))

def Atlas : Prop :=
  (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ s : ℝ, R⁻¹ ≤ s → s ≤ cfg.U → (fun (q : ℝ) (a g : ℝ → ℝ) => cfg.N k ^ (cfg.κ * s) / cfg.K k ≤ (2 : ℝ) ^ cfg.T k s ∧ (2 : ℝ) ^ cfg.T k s ≤ cfg.K k * cfg.N k ^ (cfg.κ * s) ∧ (∀ i, MeasurableSet (cfg.A k s i) ∧ MeasurableSet (cfg.B k s i) ∧ cfg.B k s i ⊆ cfg.A k s i) ∧ (∀ i i', i ≠ i' → cfg.j k s i = cfg.j k s i' → Disjoint (cfg.A k s i) (cfg.A k s i')) ∧ (∀ i, ENNReal.ofReal (a s ^ cfg.d * q ^ 2 * g s / cfg.K k) ≤ cfg.ν k (cfg.A k s i) ∧ cfg.ν k (cfg.A k s i) ≤ ENNReal.ofReal (cfg.K k * a s ^ cfg.d * q ^ 2 * g s) ∧ ENNReal.ofReal (q / cfg.K k) * cfg.ν k (cfg.A k s i) ≤ cfg.μ k (cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i)) ∧ (∀ e, |cfg.c k s i e| ≤ cfg.K k) ∧ (cfg.F k s i).totalDegree ≤ 2 ∧ (∀ l ∈ cfg.A k s i, ∀ t ∈ I (cfg.T k s) (cfg.j k s i), |(cfg.x k l t) 1 - cfg.c k s i 0 - t * cfg.c k s i 1| ≤ cfg.K k * q ∧ |(cfg.x k l t) 2 - cfg.c k s i 2 - t * cfg.c k s i 3 - cfg.c k s i 4 * (cfg.x k l t) 1| ≤ cfg.K k * q * g s ∧ |cfg.b k l 4 - cfg.c k s i 3 - cfg.c k s i 4 * cfg.b k l 3| ≤ cfg.K k * g s) ∧ (∀ l ∈ cfg.B k s i, cfg.fit k (cfg.K k) (a s) (cfg.F k s i) l (I (cfg.T k s) (cfg.j k s i))) ∧ (∀ᵐ p ∂cfg.μ k, p.1 ∈ cfg.B k s i → p.2 ∈ I (cfg.T k s) (cfg.j k s i) → (cfg.K k)⁻¹ ≤ |MvPolynomial.eval (cfg.x k p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (cfg.F k s i))|) ∧ ((true : Bool) = true → cfg.P k = MvPolynomial.X (3 : Fin 4) ∧ (∀ᵐ p ∂cfg.μ k, |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ cfg.N k ^ (-cfg.e₀)) ∧ |cfg.c k s i 3 + cfg.c k s i 0 + ((cfg.j k s i : ℕ) + (1 : ℝ) / 2) * q * cfg.c k s i 1| + |cfg.c k s i 4 - ((cfg.j k s i : ℕ) + (1 : ℝ) / 2) * q| ≤ cfg.K k * q ∧ (∃ L : Fin 4 → ℝ, cfg.F k s i = MvPolynomial.X (3 : Fin 4) - (MvPolynomial.C (L 0) + MvPolynomial.C (L 1) * MvPolynomial.X (0 : Fin 4) + MvPolynomial.C (L 2) * MvPolynomial.X (1 : Fin 4) + MvPolynomial.C (L 3) * MvPolynomial.X (2 : Fin 4)) ∧ |L 3| ≤ cfg.K k * (1 + a s / q ^ 2) ∧ ∀ l ∈ cfg.B k s i, ∀ t ∈ I (cfg.T k s) (cfg.j k s i), |L 1 - (cfg.x k l t) 1 * L 3| + |L 2 + t * L 3| ≤ cfg.K k * (1 + a s / q)))) ∧ (∀ᵐ p ∂cfg.μ k, ∃ i, p.1 ∈ cfg.B k s i ∧ p.2 ∈ I (cfg.T k s) (cfg.j k s i)) ∧ (∀ (i : Fin (cfg.n k s)) (v : ℝ) (v₀ : ℤ), R⁻¹ ≤ v → v ≤ R → cfg.μ k {p | p.1 ∈ cfg.B k s i ∧ p.2 ∈ I (cfg.T k s) (cfg.j k s i) ∧ ⌊cfg.b k p.1 3 / (cfg.N k ^ (-v))⌋ = v₀} ≤ ENNReal.ofReal (cfg.K k * q) * cfg.ν k (cfg.A k s i) * cfg.π k {w : ℝ | ⌊w / (cfg.N k ^ (-v))⌋ = v₀})) ((2 : ℝ) ^ (-(cfg.T k s : ℤ))) (fun s => cfg.N k ^ (-s)) (fun s => cfg.N k ^ (-cfg.ℓ * s)))

def Nested : Prop :=
  (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ s t : ℝ, R⁻¹ ≤ s → s < t → t ≤ cfg.U → ∀ i : Fin (cfg.n k t), ∃ h : Fin (cfg.n k s), cfg.A k t i ⊆ cfg.A k s h ∧ I (cfg.T k t) (cfg.j k t i) ⊆ I (cfg.T k s) (cfg.j k s h))

structure Valid : Prop where
  scale : ∀ k, 2 ≤ cfg.N k
  scale_limit : Filter.Tendsto cfg.N Filter.atTop Filter.atTop
  subpower : (∀ k, 1 ≤ cfg.K k) ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, cfg.K k ≤ cfg.N k ^ ε
  dimension_nonneg : 0 ≤ cfg.d
  dimension_lt_one : cfg.d < 1
  rate_pos : 0 < cfg.κ
  rate_le_one : cfg.κ ≤ 1
  transverse_pos : 0 < cfg.ℓ
  palette_pos : 0 < cfg.S
  palette_le_one : cfg.S ≤ 1
  depth_pos : 0 < cfg.U
  defect_pos : 0 < cfg.e₀
  critical_rate : 2 * cfg.κ = 1
  horizontal_rate : cfg.ℓ = cfg.κ
  basic : cfg.Basic
  caps : cfg.Caps
  atlas : cfg.Atlas
  nested : cfg.Nested

end Data


end

end Submission.Obl.k4_critical_conditional_row_preparation
