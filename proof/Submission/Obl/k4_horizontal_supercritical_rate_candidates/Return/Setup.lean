import Mathlib

/-!
# Single-sample data of the horizontal model

Clean restatements, at one sample, of the parts of o203's frozen prepared-data prefix that
the supercritical return uses: the trajectory coordinates, one depth's true-label family
with its horizontal affine fits, the joint caps and the projected layer at one depth.
-/

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- Time-`t` coordinates `(t, x1, x2, x3)` of line `l`. -/
def x1 (b : α → Fin 6 → ℝ) (l : α) (t : ℝ) : ℝ := b l 0 + t * b l 3
def x2 (b : α → Fin 6 → ℝ) (l : α) (t : ℝ) : ℝ := b l 1 + t * b l 4
def x3 (b : α → Fin 6 → ℝ) (l : α) (t : ℝ) : ℝ := b l 2 + t * b l 5

/-- Dyadic block `[j / 2^T, (j+1) / 2^T]`. -/
def blk (T : ℕ) (j : ℕ) : Set ℝ := Icc ((j : ℝ) / 2 ^ T) (((j : ℝ) + 1) / 2 ^ T)

/-- One depth's true labels with chosen horizontal affine fits. -/
structure Fam (α : Type) where
  T : ℕ
  n : ℕ
  j : Fin n → Fin (2 ^ T)
  A : Fin n → Set α
  B : Fin n → Set α
  c : Fin n → Fin 5 → ℝ
  L : Fin n → Fin 4 → ℝ

namespace Fam

variable (f : Fam α)

/-- Block length. -/
def q : ℝ := ((2 : ℝ) ^ f.T)⁻¹

/-- Block of label `i`. -/
def I (i : Fin f.n) : Set ℝ := blk f.T (f.j i)

/-- Affine fit of label `i`. -/
def fitVal (i : Fin f.n) (t y z : ℝ) : ℝ := f.L i 0 + f.L i 1 * t + f.L i 2 * y + f.L i 3 * z

/-- Properties of a depth-`s` family at one sample (horizontal case, `ℓ = κ`). -/
structure Good (ν : Measure α) (μ : Measure (α × ℝ)) (π : Measure ℝ) (b : α → Fin 6 → ℝ)
    (N K d κ s χ : ℝ) : Prop where
  Tlo : N ^ (κ * s) / K ≤ (2 : ℝ) ^ f.T
  Thi : (2 : ℝ) ^ f.T ≤ K * N ^ (κ * s)
  measA : ∀ i, MeasurableSet (f.A i)
  measB : ∀ i, MeasurableSet (f.B i)
  BA : ∀ i, f.B i ⊆ f.A i
  disj : ∀ i i', i ≠ i' → f.j i = f.j i' → Disjoint (f.A i) (f.A i')
  floorA : ∀ i, ENNReal.ofReal ((N ^ (-s)) ^ d * f.q ^ 2 * N ^ (-κ * s) / K) ≤ ν (f.A i)
  ceilA : ∀ i, ν (f.A i) ≤ ENNReal.ofReal (K * (N ^ (-s)) ^ d * f.q ^ 2 * N ^ (-κ * s))
  floorB : ∀ i, ENNReal.ofReal (f.q / K) * ν (f.A i) ≤ μ (f.B i ×ˢ f.I i)
  cbd : ∀ i e, |f.c i e| ≤ K
  geom : ∀ i, ∀ l ∈ f.A i, ∀ t ∈ f.I i,
    |x1 b l t - f.c i 0 - t * f.c i 1| ≤ K * f.q ∧
    |x2 b l t - f.c i 2 - t * f.c i 3 - f.c i 4 * x1 b l t| ≤ K * f.q * N ^ (-κ * s) ∧
    |b l 4 - f.c i 3 - f.c i 4 * b l 3| ≤ K * N ^ (-κ * s)
  fit : ∀ i, ∀ l ∈ f.B i, ∀ t ∈ f.I i,
    |x3 b l t - f.fitVal i t (x1 b l t) (x2 b l t)| ≤ K * N ^ (-s)
  L3bd : ∀ i, |f.L i 3| ≤ K * (1 + N ^ (-s) / f.q ^ 2)
  slope : ∀ i, ∀ l ∈ f.B i, ∀ t ∈ f.I i,
    |f.L i 1 - x1 b l t * f.L i 3| + |f.L i 2 + t * f.L i 3| ≤ K * (1 + N ^ (-s) / f.q)
  cover : ∀ᵐ p ∂μ, ∃ i, p.1 ∈ f.B i ∧ p.2 ∈ f.I i
  vdom : ∀ i (v₀ : ℤ), μ {p | p.1 ∈ f.B i ∧ p.2 ∈ f.I i ∧ ⌊b p.1 3 / χ⌋ = v₀} ≤
    ENNReal.ofReal (K * f.q) * ν (f.A i) * π {w : ℝ | ⌊w / χ⌋ = v₀}
  center : ∀ i, |f.c i 3 + f.c i 0 + (((f.j i : ℕ) : ℝ) + 1 / 2) * f.q * f.c i 1| +
    |f.c i 4 - (((f.j i : ℕ) : ℝ) + 1 / 2) * f.q| ≤ K * f.q

end Fam

/-- Nesting of a deeper family into a coarser one. -/
def Nests (fine coarse : Fam α) : Prop :=
  ∀ i : Fin fine.n, ∃ h : Fin coarse.n, fine.A i ⊆ coarse.A h ∧ fine.I i ⊆ coarse.I h

/-- Base cube index at side `N^(-r)`. -/
def cube (b : α → Fin 6 → ℝ) (Nr : ℝ) (p : α × ℝ) : Fin 3 → ℤ :=
  fun e => ⌊(![p.2, x1 b p.1 p.2, x2 b p.1 p.2] : Fin 3 → ℝ) e / Nr⌋

/-- Joint caps at one sample, for cube exponents in `[rlo, rhi]`, hidden exponents in
`[0, shi]`, velocity exponents in `[vlo, vhi]`. -/
structure Caps (μ : Measure (α × ℝ)) (π : Measure ℝ) (b : α → Fin 6 → ℝ)
    (N K d S rlo rhi shi vlo vhi : ℝ) : Prop where
  pal : ∀ v, vlo ≤ v → v ≤ vhi → ∀ a : ℤ,
    π {w : ℝ | ⌊w / N ^ (-v)⌋ = a} ≤ ENNReal.ofReal (K * N ^ (-S * v))
  cap : ∀ r σ, rlo ≤ r → r ≤ rhi → 0 ≤ σ → σ ≤ shi → ∀ (q : Fin 3 → ℤ) (a : ℤ),
    μ {p | cube b (N ^ (-r)) p = q ∧ ⌊x3 b p.1 p.2 / N ^ (-σ)⌋ = a} ≤
      ENNReal.ofReal (K * N ^ (-3 * r - d * σ))
  jcap : ∀ r σ v, rlo ≤ r → r ≤ rhi → 0 ≤ σ → σ ≤ shi → vlo ≤ v → v ≤ vhi →
    ∀ (q : Fin 3 → ℤ) (a v₀ : ℤ),
    μ {p | cube b (N ^ (-r)) p = q ∧ ⌊x3 b p.1 p.2 / N ^ (-σ)⌋ = a ∧
        ⌊b p.1 3 / N ^ (-v)⌋ = v₀} ≤
      ENNReal.ofReal (K * N ^ (-3 * r - d * σ)) * π {w : ℝ | ⌊w / N ^ (-v)⌋ = v₀}

/-- One projected layer: slices `C i` with bins `qp i` and full-time laws `G i`. -/
structure Layer (α : Type) where
  n : ℕ
  C : Fin n → Set α
  qp : Fin n → Fin 3 → ℤ
  G : Fin n → MvPolynomial (Fin 2) ℝ

/-- Properties of a projected layer at accuracy `a` (one depth of the projected datum). -/
structure Layer.Good (Ly : Layer α) (ρ : Measure (α × ℝ)) (π : Measure ℝ)
    (b : α → Fin 6 → ℝ) (N χ D a d ε R : ℝ) : Prop where
  meas : ∀ i, MeasurableSet (Ly.C i)
  disj : ∀ i i', i ≠ i' → Disjoint (Ly.C i) (Ly.C i')
  bins : ∀ i, ∀ l ∈ Ly.C i, ⌊b l 3 / χ⌋ = Ly.qp i 0 ∧ ⌊b l 0 / χ⌋ = Ly.qp i 1 ∧
    ⌊b l 1 / D⌋ = Ly.qp i 2 ∧ ∀ e, |b l e| ≤ N ^ ε
  ctr : ∀ i, |(Ly.qp i 0 : ℝ) * χ| + |(Ly.qp i 1 : ℝ) * χ| + |(Ly.qp i 2 : ℝ) * D| ≤ N ^ ε
  deg : ∀ i, (Ly.G i).totalDegree ≤ 2
  coef : ∀ i e, |(Ly.G i).coeff e| ≤ N ^ R
  mov : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1,
    |MvPolynomial.eval ![t, (Ly.qp i 2 : ℝ) * D - t * ((Ly.qp i 1 : ℝ) * χ) + D * w]
      (Ly.G i)| ≤ N ^ ε
  fit : ∀ i, ∀ l ∈ Ly.C i, ∀ t ∈ Icc (0 : ℝ) 1,
    |x2 b l t - (Ly.qp i 2 : ℝ) * D + t * ((Ly.qp i 1 : ℝ) * χ)| ≤ N ^ ε * D ∧
    |x3 b l t - MvPolynomial.eval ![t, x2 b l t] (Ly.G i)| ≤ N ^ ε * a
  floor : ∀ i, ENNReal.ofReal (χ * D * a ^ d / N ^ ε) *
    π (Ico ((Ly.qp i 0 : ℝ) * χ) (((Ly.qp i 0 : ℝ) + 1) * χ)) ≤ ρ (Ly.C i ×ˢ Icc (0 : ℝ) 1)
  budget : (∑ i : Fin Ly.n, ENNReal.ofReal (χ * D * a ^ d) *
    π (Ico ((Ly.qp i 0 : ℝ) * χ) (((Ly.qp i 0 : ℝ) + 1) * χ))) ≤ ENNReal.ofReal (N ^ ε)

end

end Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return
