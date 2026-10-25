import Mathlib
import Submission.Lib.K4ContactNormalization.RowNormalization

/-!
# The general prepared-parent model

Data and predicates of the general (non-horizontal) prepared-parent model of the
frozen statement. Adapted from the `PreparedModel` of session x0774 on the parent
obligation o222 (branch `x0774` of o222, file
`Submission/Obl/k4_projected_parent_contact_reduction/PreparedModel.lean`), with
the same field names so that helpers stated for that model port by a namespace
rename.
-/

namespace Submission.Obl.k4_general_parent_projected_layers

open MeasureTheory Set Filter MvPolynomial

noncomputable section

/-- The numerical parameters of a prepared sequence. -/
structure Parameters where
  N : ℕ → ℝ
  K : ℕ → ℝ
  d : ℝ
  kappa : ℝ
  ell : ℝ
  S : ℝ
  U : ℝ
  e₀ : ℝ

def Parameters.Valid (p : Parameters) : Prop :=
  (∀ k, 2 ≤ p.N k) ∧ Tendsto p.N atTop atTop ∧
  ((∀ k, 1 ≤ p.K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, p.K k ≤ p.N k ^ ε) ∧
  0 ≤ p.d ∧ p.d < 1 ∧ 0 < p.kappa ∧ p.kappa ≤ 1 ∧ 0 < p.ell ∧
  0 < p.S ∧ p.S ≤ 1 ∧ 0 < p.U ∧ 0 < p.e₀

/-- The measures, trajectories and true labels of a prepared sequence. -/
structure PreparedModel (α : Type) [MeasurableSpace α] where
  nu : ℕ → Measure α
  mu : ℕ → Measure (α × ℝ)
  rho : ℕ → Measure (α × ℝ)
  pi : ℕ → Measure ℝ
  b : ℕ → α → Fin 6 → ℝ
  P : ℕ → MvPolynomial (Fin 4) ℝ
  T : ℕ → ℝ → ℕ
  n : ℕ → ℝ → ℕ
  j : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (2 ^ T k s)
  A : (k : ℕ) → (s : ℝ) → Fin (n k s) → Set α
  B : (k : ℕ) → (s : ℝ) → Fin (n k s) → Set α
  c : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin 5 → ℝ
  F : (k : ℕ) → (s : ℝ) → Fin (n k s) → MvPolynomial (Fin 4) ℝ

namespace PreparedModel

variable {α : Type} [MeasurableSpace α]

/-- The trajectory `(t, Z, Y, X)` of a line at time `t`. -/
abbrev x (a : PreparedModel α) (k : ℕ) (l : α) (t : ℝ) : Fin 4 → ℝ :=
  Submission.Lib.K4ContactNormalization.point (a.b k l) t

def interval (T : ℕ) (j : Fin (2 ^ T)) : Set ℝ :=
  Icc ((j : ℝ) / (2 : ℝ) ^ T) (((j : ℝ) + 1) / (2 : ℝ) ^ T)

def block (a : PreparedModel α) (k : ℕ) (s : ℝ) (i : Fin (a.n k s)) : Set ℝ :=
  interval (a.T k s) (a.j k s i)

def q (a : PreparedModel α) (k : ℕ) (s : ℝ) : ℝ := (2 : ℝ) ^ (-(a.T k s : ℤ))

def width (p : Parameters) (k : ℕ) (s : ℝ) : ℝ := p.N k ^ (-s)

def narrow (p : Parameters) (k : ℕ) (s : ℝ) : ℝ := p.N k ^ (-p.ell * s)

def fit (a : PreparedModel α) (k : ℕ) (H w : ℝ)
    (Q : MvPolynomial (Fin 4) ℝ) (l : α) (I : Set ℝ) : Prop :=
  ∀ t ∈ I, |eval (a.x k l t) Q| ≤ H * w ∧
    |eval (a.x k l t) (pderiv (3 : Fin 4) Q)| ≤ H ∧
    |eval (a.x k l t) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) Q))| ≤ H / w

def cell (a : PreparedModel α) (N r : ℝ) (k : ℕ) (p : α × ℝ) : Fin 3 → ℤ :=
  fun e => ⌊(![p.2, (a.x k p.1 p.2) 1, (a.x k p.1 p.2) 2] : Fin 3 → ℝ) e / N ^ (-r)⌋

/-- Priors, domination and the bounded native observable. -/
def Common (p : Parameters) (a : PreparedModel α) : Prop :=
  ∀ k, Measurable (a.b k) ∧ IsProbabilityMeasure (a.nu k) ∧ IsProbabilityMeasure (a.pi k) ∧
    a.mu k ≤ ENNReal.ofReal (p.K k) • (a.nu k).prod volume ∧ a.rho k ≤ a.mu k ∧
    a.mu k (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0 ∧ ENNReal.ofReal ((p.K k)⁻¹) ≤ a.rho k univ ∧
    (a.P k).totalDegree ≤ 2 ∧
    (∀ᵐ l ∂a.nu k, |a.b k l 0| + |a.b k l 1| + |a.b k l 3| + |a.b k l 4| ≤ p.K k) ∧
    (∀ᵐ z ∂a.mu k,
      (∀ t ∈ Icc (0 : ℝ) 1, |eval (a.x k z.1 t) (a.P k)| ≤ p.K k ∧
        |eval (a.x k z.1 t) (pderiv (3 : Fin 4) (a.P k))| ≤ p.K k ∧
        |eval (a.x k z.1 t) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) (a.P k)))| ≤ p.K k) ∧
      (p.K k)⁻¹ ≤ |eval (a.x k z.1 z.2) (pderiv (3 : Fin 4) (a.P k))|)

/-- The uniform pure and palette mesh caps. -/
def Caps (p : Parameters) (a : PreparedModel α) : Prop :=
  ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop,
    ∀ r s v : ℝ, R⁻¹ ≤ r → r ≤ R → 0 ≤ s → s ≤ R → R⁻¹ ≤ v → v ≤ R →
    (∀ j : ℤ, a.pi k {w | ⌊w / p.N k ^ (-v)⌋ = j} ≤
      ENNReal.ofReal (p.K k * p.N k ^ (-p.S * v))) ∧
    (∀ h : Bool, ∀ (z : Fin 3 → ℤ) (j : ℤ),
      a.mu k {w | a.cell (p.N k) r k w = z ∧
        ⌊(if h then eval (a.x k w.1 w.2) (a.P k) else (a.x k w.1 w.2) 3) / p.N k ^ (-s)⌋ = j} ≤
          ENNReal.ofReal (p.K k * p.N k ^ (-3 * r - p.d * s))) ∧
    (∀ h : Bool, ∀ (z : Fin 3 → ℤ) (j v₀ : ℤ),
      a.mu k {w | a.cell (p.N k) r k w = z ∧
        ⌊(if h then eval (a.x k w.1 w.2) (a.P k) else (a.x k w.1 w.2) 3) / p.N k ^ (-s)⌋ = j ∧
        ⌊a.b k w.1 3 / p.N k ^ (-v)⌋ = v₀} ≤
          ENNReal.ofReal (p.K k * p.N k ^ (-3 * r - p.d * s)) *
            a.pi k {w | ⌊w / p.N k ^ (-v)⌋ = v₀})

/-- The true labels at one depth. -/
def AtlasAt (p : Parameters) (a : PreparedModel α) (R : ℝ) (k : ℕ) (s : ℝ) : Prop :=
  p.N k ^ (p.kappa * s) / p.K k ≤ (2 : ℝ) ^ a.T k s ∧
  (2 : ℝ) ^ a.T k s ≤ p.K k * p.N k ^ (p.kappa * s) ∧
  (∀ i, MeasurableSet (a.A k s i) ∧ MeasurableSet (a.B k s i) ∧ a.B k s i ⊆ a.A k s i) ∧
  (∀ i i', i ≠ i' → a.j k s i = a.j k s i' → Disjoint (a.A k s i) (a.A k s i')) ∧
  (∀ i,
    ENNReal.ofReal (width p k s ^ p.d * a.q k s ^ 2 * narrow p k s / p.K k) ≤ a.nu k (a.A k s i) ∧
    a.nu k (a.A k s i) ≤ ENNReal.ofReal (p.K k * width p k s ^ p.d * a.q k s ^ 2 * narrow p k s) ∧
    ENNReal.ofReal (a.q k s / p.K k) * a.nu k (a.A k s i) ≤
      a.mu k (a.B k s i ×ˢ a.block k s i) ∧
    (∀ e, |a.c k s i e| ≤ p.K k) ∧ (a.F k s i).totalDegree ≤ 2 ∧
    (∀ l ∈ a.A k s i, ∀ t ∈ a.block k s i,
      |(a.x k l t) 1 - a.c k s i 0 - t * a.c k s i 1| ≤ p.K k * a.q k s ∧
      |(a.x k l t) 2 - a.c k s i 2 - t * a.c k s i 3 - a.c k s i 4 * (a.x k l t) 1| ≤
        p.K k * a.q k s * narrow p k s ∧
      |a.b k l 4 - a.c k s i 3 - a.c k s i 4 * a.b k l 3| ≤ p.K k * narrow p k s) ∧
    (∀ l ∈ a.B k s i, a.fit k (p.K k) (width p k s) (a.F k s i) l (a.block k s i)) ∧
    (∀ᵐ z ∂a.mu k, z.1 ∈ a.B k s i → z.2 ∈ a.block k s i →
      (p.K k)⁻¹ ≤ |eval (a.x k z.1 z.2) (pderiv (3 : Fin 4) (a.F k s i))|)) ∧
  (∀ᵐ z ∂a.mu k, ∃ i, z.1 ∈ a.B k s i ∧ z.2 ∈ a.block k s i) ∧
  (∀ (i : Fin (a.n k s)) (v : ℝ) (v₀ : ℤ), R⁻¹ ≤ v → v ≤ R →
    a.mu k {z | z.1 ∈ a.B k s i ∧ z.2 ∈ a.block k s i ∧
      ⌊a.b k z.1 3 / p.N k ^ (-v)⌋ = v₀} ≤
      ENNReal.ofReal (p.K k * a.q k s) * a.nu k (a.A k s i) *
        a.pi k {w | ⌊w / p.N k ^ (-v)⌋ = v₀})

def Atlases (p : Parameters) (a : PreparedModel α) : Prop :=
  ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∀ s : ℝ, R⁻¹ ≤ s → s ≤ p.U → a.AtlasAt p R k s

def Nested (p : Parameters) (a : PreparedModel α) : Prop :=
  ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∀ s t : ℝ,
    R⁻¹ ≤ s → s < t → t ≤ p.U → ∀ i : Fin (a.n k t),
      ∃ h : Fin (a.n k s), a.A k t i ⊆ a.A k s h ∧ a.block k t i ⊆ a.block k s h

def Valid (p : Parameters) (a : PreparedModel α) : Prop :=
  a.Common p ∧ a.Caps p ∧ a.Atlases p ∧ a.Nested p

/-- The original residual has total mass at most `K`. -/
theorem rho_univ_le (p : Parameters) (a : PreparedModel α) (h : a.Common p) (k : ℕ) :
    a.rho k univ ≤ ENNReal.ofReal (p.K k) := by
  obtain ⟨_, hν, _, hdom, hρ, hsupp, -⟩ := h k
  have h1 : a.mu k univ ≤ a.mu k (univ ×ˢ Icc (0 : ℝ) 1) := by
    simpa [hsupp] using measure_univ_le_add_compl (μ := a.mu k) (univ ×ˢ Icc (0 : ℝ) 1)
  calc a.rho k univ ≤ a.mu k univ := hρ univ
    _ ≤ a.mu k (univ ×ˢ Icc (0 : ℝ) 1) := h1
    _ ≤ (ENNReal.ofReal (p.K k) • (a.nu k).prod volume) (univ ×ˢ Icc (0 : ℝ) 1) := hdom _
    _ = ENNReal.ofReal (p.K k) := by
      rw [Measure.smul_apply, Measure.prod_prod]
      simp

end PreparedModel

end

end Submission.Obl.k4_general_parent_projected_layers
