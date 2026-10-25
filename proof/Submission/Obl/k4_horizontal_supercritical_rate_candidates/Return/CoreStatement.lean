import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.Setup
import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Model

/-!
# The single-sample supercritical return

`CoreStatement` is the finite-`N` heart of the supercritical return: at one sample, from
the coarse true labels (depth `s₀`), the candidate labels (depth `s₁ - vc`), deep labels
(depth `300 s₀`) and one projected layer at depth `s₁`, it produces a quadratic candidate
of gain `vc` in some candidate label, with mass at least `N^(-d vc - ε) q ν(A)` under the
residual `ρ`. The asymptotic wrapper in `Main.lean` derives the frozen conclusion from it.
-/

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return

open MeasureTheory Set

/-- The frozen trajectory `(t, x1, x2, x3)`. -/
def trajV {α : Type} (b : α → Fin 6 → ℝ) (l : α) (t : ℝ) : Fin 4 → ℝ :=
  ![t, b l 0 + t * b l 3, b l 1 + t * b l 4, b l 2 + t * b l 5]

/-- The frozen candidate fit. -/
def candFit {α : Type} (b : α → Fin 6 → ℝ) (H a : ℝ) (Q : MvPolynomial (Fin 4) ℝ) (l : α)
    (I : Set ℝ) : Prop :=
  ∀ t ∈ I, |MvPolynomial.eval (trajV b l t) Q| ≤ H * a ∧
    |MvPolynomial.eval (trajV b l t) (MvPolynomial.pderiv (3 : Fin 4) Q)| ≤ H ∧
    |MvPolynomial.eval (trajV b l t)
      (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) Q))| ≤ H / a

/-- The single-sample supercritical return. -/
def CoreStatement : Prop :=
  Scalar → ∀ (d κ S e₀ s₀ s₁ vc M RL Rout ε : ℝ), 0 ≤ d → d < 1 → 1 < 2 * κ → κ ≤ 1 → 0 < S →
    S ≤ 1 → 0 < s₀ → s₀ < s₁ → s₁ < 3 * s₀ / 2 → 0 < vc →
    vc ≤ (2 * κ - 1) * (s₁ - s₀) / (4 * κ) → 1000 * s₀ < e₀ → M = 101 * s₀ → 1 < RL →
    2 * κ * s₁ + 10 ≤ Rout → 0 < ε →
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∃ Rcap : ℝ, 1 < Rcap ∧ Rcap⁻¹ ≤ s₀ ∧ M ≤ Rcap ∧
    ∀ N : ℝ, N₀ ≤ N → ∀ K εL : ℝ, 1 ≤ K → K ≤ N ^ η → 0 < εL → εL ≤ η →
    ∀ (α : Type) [MeasurableSpace α] (ν : Measure α) (μ ρ ρs : Measure (α × ℝ))
      (π : Measure ℝ) (b : α → Fin 6 → ℝ) (f₀ fc fe : Fam α) (Ly : Layer α),
    Measurable b → IsProbabilityMeasure ν → IsProbabilityMeasure π →
    μ ≤ ENNReal.ofReal K • ν.prod volume → ρ ≤ μ → μ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0 →
    (∀ᵐ l ∂ν, |b l 0| + |b l 1| + |b l 3| + |b l 4| ≤ K) →
    (∀ᵐ p ∂μ, ∀ t ∈ Icc (0 : ℝ) 1, |x3 b p.1 t| ≤ K) →
    (∀ᵐ p ∂μ, |b p.1 4 + b p.1 0| ≤ N ^ (-e₀)) →
    Caps μ π b N K d S Rcap⁻¹ Rcap Rcap Rcap⁻¹ Rcap →
    f₀.Good ν μ π b N K d κ s₀ (N ^ (-M)) →
    fc.Good ν μ π b N K d κ (s₁ - vc) (N ^ (-M)) →
    fe.Good ν μ π b N K d κ (300 * s₀) (N ^ (-M)) →
    Nests fc f₀ → Nests fe fc →
    ρs ≤ ρ → ENNReal.ofReal (N ^ (-εL)) ≤ ρs univ → (∀ᵐ p ∂ρs, ∃ i, p.1 ∈ Ly.C i) →
    Ly.Good ρ π b N (N ^ (-M)) (N ^ (-2 * κ * s₀)) (N ^ (-s₁)) d εL RL →
    ∃ (i : Fin fc.n) (Q : MvPolynomial (Fin 4) ℝ), Q.totalDegree ≤ 2 ∧
      (∀ e, |Q.coeff e| ≤ N ^ Rout) ∧
      ENNReal.ofReal (N ^ (-d * vc - ε) * fc.q) * ν (fc.A i) ≤
        ρ {p | p.1 ∈ fc.B i ∧ p.2 ∈ fc.I i ∧
          candFit b (N ^ ε) (N ^ (-(s₁ - vc) - vc)) Q p.1 (fc.I i) ∧
          N ^ (-ε) ≤ |MvPolynomial.eval (trajV b p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) Q)|}

end Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return
