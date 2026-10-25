import Mathlib
import Submission.Obl.k4_critical_conditional_row_preparation.Model

set_option linter.unusedVariables false

/-!
# The compared true block: the interface between comparison and field/support

At one index `k`, one block scale `s` and one true block `i`, the comparison stage
(short-domain comparison of the layer-0 sheets with the block graph, offset freezing of the
layer-1/layer-2 sheets from the compared full-strip datum, and their counts) supplies a
`ComparedBlock`.  Everything after it -- fine-state velocity domination from deep true blocks,
coefficient agreement, the common field, the residual support count and the frozen
`ExtractionAt` output -- is derived from a `ComparedBlock` and the original hypotheses only.

Normalized block coordinates of an incidence `(l, t)` (frame `t₀ q g a c L`):
* `zt = (t - t₀)/q`, `zZ = (b 0 + t b 3 - c₀ - t c₁)/q`,
* `tr = (b 1 + t b 4 - c₂ - t c₃ - c₄ (b 0 + t b 3))/(q g)`,
* `resid = (b 2 + t b 5 - (L₀ + L₁ t + L₂ (b 0 + t b 3) + L₃ (b 1 + t b 4)))/a`.
These are exactly the expressions of the frozen output.
-/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

open MeasureTheory Set Filter

noncomputable section

/-- The frame of a true block: time start, length, transverse scale, depth width, centers,
affine graph. -/
structure Frame where
  t₀ : ℝ
  q : ℝ
  g : ℝ
  a : ℝ
  c : Fin 5 → ℝ
  L : Fin 4 → ℝ

namespace Frame

variable (F : Frame)

def zt (t : ℝ) : ℝ := (t - F.t₀) / F.q

def zZ (b : Fin 6 → ℝ) (t : ℝ) : ℝ := (b 0 + t * b 3 - F.c 0 - t * F.c 1) / F.q

def tr (b : Fin 6 → ℝ) (t : ℝ) : ℝ :=
  (b 1 + t * b 4 - F.c 2 - t * F.c 3 - F.c 4 * (b 0 + t * b 3)) / (F.q * F.g)

def resid (b : Fin 6 → ℝ) (t : ℝ) : ℝ :=
  (b 2 + t * b 5 - (F.L 0 + F.L 1 * t + F.L 2 * (b 0 + t * b 3) + F.L 3 * (b 1 + t * b 4))) /
    F.a

end Frame

/-- A quadratic in the normalized base `(zt, zZ)`. -/
def quadZ (p : Fin 6 → ℝ) (x y : ℝ) : ℝ :=
  p 0 + p 1 * x + p 2 * y + p 3 * x ^ 2 + p 4 * x * y + p 5 * y ^ 2

/-- A transverse polynomial `(τ₀ + τ₁ zt + τ₂ zZ) U + τ₃ U²` (the frozen correction shape). -/
def transv (τ : Fin 4 → ℝ) (x y U : ℝ) : ℝ := (τ 0 + τ 1 * x + τ 2 * y) * U + τ 3 * U ^ 2

open Submission.Obl.k4_critical_conditional_row_preparation

/-- The frame of block `i` at index `k` and scale `s`, with a chosen affine graph `L`. -/
def blockFrame {α : Type} [MeasurableSpace α] (cfg : Data α) (k : ℕ) (s : ℝ)
    (i : Fin (cfg.n k s)) (L : Fin 4 → ℝ) : Frame where
  t₀ := (cfg.j k s i : ℕ) / (2 : ℝ) ^ cfg.T k s
  q := ((2 : ℝ) ^ cfg.T k s)⁻¹
  g := cfg.N k ^ (-cfg.κ * s)
  a := cfg.N k ^ (-s)
  c := cfg.c k s i
  L := L

/-- **The compared true block** (output of the comparison stage at one index).

* `lam` is a restriction of the original `ρ` to the block, of mass at least `H⁻¹ q ν(A_i)`.
* Each trajectory has a label `lab l` (e.g. its three projected cells), a coarse predictor
  `crs (lab l)` (its layer-0 sheet) with normalized transverse coefficients `tc` and base
  quadratic `pc`, and two constant offsets `D1, D2` (layer 1 and layer 2, normalized by `a`).
* `fit1`, `fit2`: the normalized residual is the coarse polynomial plus the offset, to
  precision `H N^-u` and `H N^-v` respectively.
* `coarse_list`: in each original chart (velocity and intercept bins of width `χ`) only `H`
  coarse predictors occur; `offset1_list`, `offset2_list`: given a chart and a coarse
  predictor, only `H N^{d u}` (resp. `H N^{d v}`) offset bins occur. -/
structure ComparedBlock {α : Type} [MeasurableSpace α] (cfg : Data α) (k : ℕ)
    (s u v χ H : ℝ) where
  i : Fin (cfg.n k s)
  L : Fin 4 → ℝ
  /-- the block's affine graph is the one of the horizontal premise -/
  hL : cfg.F k s i = MvPolynomial.X (3 : Fin 4) - (MvPolynomial.C (L 0) +
    MvPolynomial.C (L 1) * MvPolynomial.X (0 : Fin 4) +
    MvPolynomial.C (L 2) * MvPolynomial.X (1 : Fin 4) +
    MvPolynomial.C (L 3) * MvPolynomial.X (2 : Fin 4))
  /-- a fixed-power bound for the affine graph (used for the frozen `|L e| ≤ N^J`) -/
  L_bd : ∀ e, |L e| ≤ H * cfg.N k ^ (2 * s)
  H_one : 1 ≤ H
  lam : Measure (α × ℝ)
  lam_le : lam ≤ cfg.ρ k
  lam_supp : ∀ᵐ p ∂lam, p.1 ∈ cfg.B k s i ∧
    p.2 ∈ Icc ((cfg.j k s i : ℕ) / (2 : ℝ) ^ cfg.T k s)
      ((cfg.j k s i : ℕ) / (2 : ℝ) ^ cfg.T k s + ((2 : ℝ) ^ cfg.T k s)⁻¹)
  lam_mass : ENNReal.ofReal H⁻¹ *
      (ENNReal.ofReal ((2 : ℝ) ^ cfg.T k s)⁻¹ * cfg.ν k (cfg.A k s i)) ≤ lam univ
  /-- coarse predictors and labels -/
  Γ : Type
  instΓ : Fintype Γ
  Λ : Type
  instΛ : Fintype Λ
  lab : α → Λ
  lab_meas : ∀ x, MeasurableSet (lab ⁻¹' {x})
  crs : Λ → Γ
  /-- each coarse predictor lives on one original chart (velocity, intercept bins of width `χ`) -/
  chartOf : Γ → ℤ × ℤ
  chart_ae : ∀ᵐ p ∂lam, (⌊cfg.b k p.1 3 / χ⌋, ⌊cfg.b k p.1 0 / χ⌋) = chartOf (crs (lab p.1))
  tc : Γ → Fin 4 → ℝ
  pc : Γ → Fin 6 → ℝ
  D1 : Λ → ℝ
  D2 : Λ → ℝ
  tc_bd : ∀ γ e, |tc γ e| ≤ H
  pc_bd : ∀ γ e, |pc γ e| ≤ H
  fit1 : ∀ᵐ p ∂lam,
    |(blockFrame cfg k s i L).resid (cfg.b k p.1) p.2 -
      quadZ (pc (crs (lab p.1))) ((blockFrame cfg k s i L).zt p.2)
        ((blockFrame cfg k s i L).zZ (cfg.b k p.1) p.2) - D1 (lab p.1) -
      transv (tc (crs (lab p.1))) ((blockFrame cfg k s i L).zt p.2)
        ((blockFrame cfg k s i L).zZ (cfg.b k p.1) p.2)
        ((blockFrame cfg k s i L).tr (cfg.b k p.1) p.2)| ≤ H * cfg.N k ^ (-u)
  fit2 : ∀ᵐ p ∂lam,
    |(blockFrame cfg k s i L).resid (cfg.b k p.1) p.2 -
      quadZ (pc (crs (lab p.1))) ((blockFrame cfg k s i L).zt p.2)
        ((blockFrame cfg k s i L).zZ (cfg.b k p.1) p.2) - D2 (lab p.1) -
      transv (tc (crs (lab p.1))) ((blockFrame cfg k s i L).zt p.2)
        ((blockFrame cfg k s i L).zZ (cfg.b k p.1) p.2)
        ((blockFrame cfg k s i L).tr (cfg.b k p.1) p.2)| ≤ H * cfg.N k ^ (-v)
  coarse_list : ∀ z3 z0 : ℤ, ∃ G : Finset Γ, (G.card : ℝ) ≤ H ∧
    ∀ᵐ p ∂lam, ⌊cfg.b k p.1 3 / χ⌋ = z3 → ⌊cfg.b k p.1 0 / χ⌋ = z0 → crs (lab p.1) ∈ G
  offset1_list : ∀ (z3 z0 : ℤ) (γ : Γ), ∃ F : Finset ℤ,
    (F.card : ℝ) ≤ H * cfg.N k ^ (cfg.d * u) ∧
    ∀ᵐ p ∂lam, ⌊cfg.b k p.1 3 / χ⌋ = z3 → ⌊cfg.b k p.1 0 / χ⌋ = z0 → crs (lab p.1) = γ →
      ⌊D1 (lab p.1) / cfg.N k ^ (-u)⌋ ∈ F
  offset2_list : ∀ (z3 z0 : ℤ) (γ : Γ), ∃ F : Finset ℤ,
    (F.card : ℝ) ≤ H * cfg.N k ^ (cfg.d * v) ∧
    ∀ᵐ p ∂lam, ⌊cfg.b k p.1 3 / χ⌋ = z3 → ⌊cfg.b k p.1 0 / χ⌋ = z0 → crs (lab p.1) = γ →
      ⌊D2 (lab p.1) / cfg.N k ^ (-v)⌋ ∈ F

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
