-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
-- Adapted from this LOT tree, o232, session x0859, commit ead85178.
-- Source: Submission/Obl/k4_finite_affine_parent_sources/FlatCut.lean.
import Submission.Obl.k4_finite_affine_parent_sources.Cut

namespace Submission.Obl.k4_finite_affine_parent_sources

noncomputable section

def FlatSynthetic : Prop :=
∀ d₁ κ₁ ℓ S : ℝ, 0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 →
0 < ℓ → 0 < S → S ≤ 1 → ∀ n : ℕ, 2 ≤ n →∃ (sN sK : ℝ) (sν : MeasureTheory.Measure (ℕ × (Fin 6 → ℝ)))
(sμ sρ : MeasureTheory.Measure ((ℕ × (Fin 6 → ℝ)) × ℝ)) (sπ : MeasureTheory.Measure ℝ)
(sb : (ℕ × (Fin 6 → ℝ)) → Fin 6 → ℝ) (sP : MvPolynomial (Fin 4) ℝ)
(sT sn : ℝ → ℕ) (sj : (s : ℝ) → Fin (sn s) → Fin (2 ^ sT s))
(sA sB : (s : ℝ) → Fin (sn s) → Set (ℕ × (Fin 6 → ℝ)))
(sc : (s : ℝ) → Fin (sn s) → Fin 5 → ℝ)
(sF : (s : ℝ) → Fin (sn s) → MvPolynomial (Fin 4) ℝ), StageGood d₁ κ₁ ℓ S n ({ N := sN, K := sK, ν := sν, μ := sμ, ρ := sρ, π := sπ, b := sb, P := sP, T := sT, nl := sn, j := sj, A := sA, B := sB, c := sc, F := sF } : EStage Trajectory)

def FlatSourcePreparation : Prop :=
∀ d₁ κ₁ ℓ S η ρ : ℝ, 0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 →
0 < ℓ → 0 < S → S ≤ 1 → 0 < η → 0 < ρ → ρ ≤ 1 / 4 → ∀ n : ℕ, 2 ≤ n →∃ (m : ℕ) (s : ℕ → ℝ) (gain δ₀ unit : ℝ),
FineGrid m s gain ρ ∧ 0 < gain ∧ gain ≤ 1 / 8 ∧ 0 < δ₀ ∧ δ₀ ≤ ρ * gain ∧
∀ N K L d W ω ν E P B f g G, prob N K L d S η W ω ν E P B f g G →
(∀ q : ℝ, 0 ≤ q → q ≤ L → |f q - f 0 - d₁ * q| ≤ δ₀ * L) →
∀ Mp Dp : ℕ, ∃ M : ℕ, ∀ ε : ℝ, 0 < ε → ∃ σ : ℝ, 0 < σ ∧
∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (r : ℕ → ℝ) (T : ℕ → ℕ) (nw : ℕ → ℝ) (κ : ℝ) (C : ℕ)
(lev : Fin C → ℕ) (par : Fin C → Fin C) (γ : Fin C → Fin (W k)) (j : Fin C → ℕ)
(c u : Fin C → EuclideanSpace ℝ (Fin 2)) (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
(R : Fin C → MvPolynomial (Fin 4) ℝ) (A : Fin C → Set (ℕ × (Fin 6 → ℝ)))
(F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
(lst : ℕ → Fin (W k) → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C)),
PositivePath ℓ (N k) L (W k) (ω k) (ν k) (E k) (B k) f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst →
∀ H : Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ),
(∀ w, MeasurableSet (H w) ∧ H w ⊆ TerminalInc (W k) C m lev γ F w) →
(1 / 2 : ENNReal) * (∑ w, ENNReal.ofReal (ω k w) *
((ν k w).prod MeasureTheory.volume) (TerminalInc (W k) C m lev γ F w)) ≤
∑ w, ENNReal.ofReal (ω k w) * ((ν k w).prod MeasureTheory.volume) (H w) →
MixedCandidate (N k) L (W k) (ν k) (B k) M d₁ ρ gain ε r T C lev γ j u Q A H ∨
∃ (sN sK : ℝ) (sν : MeasureTheory.Measure (ℕ × (Fin 6 → ℝ)))
(sμ sρ : MeasureTheory.Measure ((ℕ × (Fin 6 → ℝ)) × ℝ)) (sπ : MeasureTheory.Measure ℝ)
(sb : (ℕ × (Fin 6 → ℝ)) → Fin 6 → ℝ) (sP : MvPolynomial (Fin 4) ℝ)
(sT sn : ℝ → ℕ) (sj : (s : ℝ) → Fin (sn s) → Fin (2 ^ sT s))
(sA sB : (s : ℝ) → Fin (sn s) → Set (ℕ × (Fin 6 → ℝ)))
(sc : (s : ℝ) → Fin (sn s) → Fin 5 → ℝ)
(sF : (s : ℝ) → Fin (sn s) → MvPolynomial (Fin 4) ℝ), StageGood d₁ κ₁ ℓ S n ({ N := sN, K := sK, ν := sν, μ := sμ, ρ := sρ, π := sπ, b := sb, P := sP, T := sT, nl := sn, j := sj, A := sA, B := sB, c := sc, F := sF } : EStage Trajectory) ∧ NativeSource n M d₁ ℓ ρ gain ε unit (N k) L (ν k) (B k) ({ r := r, T := T, nw := nw, κ := κ, C := C, lev := lev, par := par, world := γ, bin := j, center := c, velocity := u, frame := Q, test := R, assigned := A, counted := F, lists := lst } : PathData (W k)) H ({ N := sN, K := sK, ν := sν, μ := sμ, ρ := sρ, π := sπ, b := sb, P := sP, T := sT, nl := sn, j := sj, A := sA, B := sB, c := sc, F := sF } : EStage Trajectory)

def FlatSourceReturn : Prop :=
∀ n M : ℕ, ∃ Mc : ℕ,
∀ (d₁ κ₁ ℓ ρ gain ε unit Nk L : ℝ) (W : ℕ)
(ω : Fin W → ℝ) (ν : Fin W → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ)))
(E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (B : Fin W → ℝ) (f : ℝ → ℝ)
(m : ℕ) (s : ℕ → ℝ) (δ₀ : ℝ) (Mp Dp : ℕ) (σ : ℝ),
∀ (r : ℕ → ℝ) (T : ℕ → ℕ) (nw : ℕ → ℝ) (κ : ℝ) (C : ℕ)
(lev : Fin C → ℕ) (par : Fin C → Fin C) (γ : Fin C → Fin W) (j : Fin C → ℕ)
(c u : Fin C → EuclideanSpace ℝ (Fin 2)) (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
(R : Fin C → MvPolynomial (Fin 4) ℝ) (A : Fin C → Set (ℕ × (Fin 6 → ℝ)))
(F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
(lst : ℕ → Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C)) (H : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (sN sK : ℝ) (sν : MeasureTheory.Measure (ℕ × (Fin 6 → ℝ)))
(sμ sρ : MeasureTheory.Measure ((ℕ × (Fin 6 → ℝ)) × ℝ)) (sπ : MeasureTheory.Measure ℝ)
(sb : (ℕ × (Fin 6 → ℝ)) → Fin 6 → ℝ) (sP : MvPolynomial (Fin 4) ℝ)
(sT sn : ℝ → ℕ) (sj : (s : ℝ) → Fin (sn s) → Fin (2 ^ sT s))
(sA sB : (s : ℝ) → Fin (sn s) → Set (ℕ × (Fin 6 → ℝ)))
(sc : (s : ℝ) → Fin (sn s) → Fin 5 → ℝ)
(sF : (s : ℝ) → Fin (sn s) → MvPolynomial (Fin 4) ℝ),
PositivePath ℓ Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst →
(∀ w, MeasurableSet (H w)) → NativeSource n M d₁ ℓ ρ gain ε unit Nk L ν B ({ r := r, T := T, nw := nw, κ := κ, C := C, lev := lev, par := par, world := γ, bin := j, center := c, velocity := u, frame := Q, test := R, assigned := A, counted := F, lists := lst } : PathData W) H ({ N := sN, K := sK, ν := sν, μ := sμ, ρ := sρ, π := sπ, b := sb, P := sP, T := sT, nl := sn, j := sj, A := sA, B := sB, c := sc, F := sF } : EStage Trajectory) →
∀ R : ℝ, 1 < R → R ≤ n → ∀ ε' : ℝ, 0 < ε' → ε' ≤ ρ / (4 * R) →
ECand d₁ ℓ 1 ({ N := sN, K := sK, ν := sν, μ := sμ, ρ := sρ, π := sπ, b := sb, P := sP, T := sT, nl := sn, j := sj, A := sA, B := sB, c := sc, F := sF } : EStage Trajectory) R ε' → MixedCandidate Nk L W ν B Mc d₁ ρ gain ε r T C lev γ j u Q A H

end
end Submission.Obl.k4_finite_affine_parent_sources
