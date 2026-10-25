import Mathlib
import ChallengeDeps
import Submission.Lib.K4QuadraticSheets

namespace Submission.Obl.k4_pair_anchor_jet_bins

noncomputable section

abbrev R3 := EuclideanSpace ℝ (Fin 3)
abbrev E3 := EuclideanSpace ℂ (Fin 3)
abbrev Test := MvPolynomial (Fin 4) ℝ

def emb (z : R3) : E3 := WithLp.toLp 2 (fun i => (z i : ℂ))

def disc (P : Test) : MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (Fin.lastCases (0 : MvPolynomial (Fin 3) ℝ) MvPolynomial.X)
    ((MvPolynomial.pderiv (3 : Fin 4) P) ^ 2 -
      2 * MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) P) * P)

def localPair (N a δ q : ℝ) (P P' : Test) (z : R3)
    (zline : ℝ → R3) (wline : ℝ → ℝ) (t₀ : ℝ) (I : Set ℝ) : Prop :=
  N ^ (-a) ≤ |MvPolynomial.eval (fun i => z i) (disc P)| ∧
  N ^ (-a) ≤ |MvPolynomial.eval (fun i => z i) (disc P')| ∧
  ∃ f f' : E3 → ℂ,
    (∀ (R : Test) (F : E3 → ℂ), (R = P ∧ F = f) ∨ (R = P' ∧ F = f') →
      DifferentiableOn ℂ F (Metric.ball (emb z) (8 * N ^ (-a))) ∧
      (∀ ζ ∈ Metric.ball (emb z) (8 * N ^ (-a)),
        MvPolynomial.eval (Fin.snoc (fun i : Fin 3 => ζ i) (F ζ))
          (R.map (algebraMap ℝ ℂ)) = 0 ∧
        MvPolynomial.eval (Fin.snoc (fun i : Fin 3 => ζ i) (F ζ))
          ((MvPolynomial.pderiv (3 : Fin 4) R).map (algebraMap ℝ ℂ)) ≠ 0) ∧
      ∀ z' ∈ Metric.ball z (8 * N ^ (-a)), (F (emb z')).im = 0) ∧
    ‖f (emb z) - (wline t₀ : ℂ)‖ ≤ δ * N ^ a ∧
    ‖f' (emb z) - (wline t₀ : ℂ)‖ ≤ δ * N ^ a ∧
    (∀ z' ∈ Metric.closedBall z (2 * N ^ (-a)),
      ‖f (emb z') - f' (emb z')‖ ≤ δ * N ^ a) ∧
    ∀ t ∈ I ∩ Set.Icc (t₀ - N ^ (-a) / (100 * q)) (t₀ + N ^ (-a) / (100 * q)),
      ‖(wline t : ℂ) - f (emb (zline t))‖ ≤ δ * N ^ a

def safePath (z₀ α : R3) (σ : ℂ) : Set E3 :=
  segment ℝ (emb z₀) (emb z₀ + σ • (emb α - emb z₀)) ∪
    segment ℝ (emb z₀ + σ • (emb α - emb z₀)) (emb α)

def SafeFor (ρ : ℝ) (p p' : MvPolynomial (Fin 3) ℝ) (z₀ α : R3) (σ : ℂ) : Prop :=
  ∀ z ∈ Metric.thickening ρ (safePath z₀ α σ),
    ρ ≤ ‖MvPolynomial.eval (fun i => z i) (p.map (algebraMap ℝ ℂ))‖ ∧
    ρ ≤ ‖MvPolynomial.eval (fun i => z i) (p'.map (algebraMap ℝ ℂ))‖

def QuadTest (N a δ : ℝ) (M : ℕ) (P : Test) : Prop :=
  P.totalDegree ≤ 2 ∧
  (∀ d, |P.coeff d| ≤ N ^ M) ∧
  |MvPolynomial.eval (0 : Fin 4 → ℝ)
      (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) P))| ≤ δ⁻¹ ∧
  (disc P).totalDegree ≤ 2 ∧ ∀ d, |(disc P).coeff d| ≤ N ^ a

abbrev Continuation : Prop := Submission.Lib.K4QuadraticSheets.ContInput

def AnalyticKernel : Prop :=
  ∀ Cs : ℕ, 0 < Cs → ∃ (d : ℕ) (CR CK : ℝ)
    (Bins : ℝ → ℝ → ℝ → Test → R3 → Finset (Fin d → ℤ)),
    0 < CR ∧ 0 < CK ∧ (∀ N a δ P α, (Bins N a δ P α).card ≤ 2) ∧
    ∀ a : ℝ, 0 < a → ∀ M : ℕ, ∃ N₀ : ℝ,
    ∀ N δ q : ℝ, N₀ ≤ N → 0 < δ → δ ≤ 1 → 1 ≤ q →
    ∀ (P P' : Test) (z₀ α : R3) (σ : ℂ) (zline : ℝ → R3)
      (wline : ℝ → ℝ) (t₀ : ℝ) (I : Set ℝ),
    QuadTest N a δ M P → QuadTest N a δ M P' → ‖z₀‖ ≤ 1 / 8 →
    t₀ ∈ I → zline t₀ = z₀ → (∀ t ∈ I, ‖zline t - z₀‖ ≤ q * |t - t₀|) →
    localPair N a δ q P P' z₀ zline wline t₀ I →
    α ∈ Metric.closedBall (0 : R3) (1 / 8) →
    σ ∈ Metric.closedBall (1 / 2 : ℂ) (1 / 4) →
    SafeFor ((N ^ a) ^ (-(Cs : ℝ))) (disc P) (disc P') z₀ α σ →
    ∃ β ∈ Bins N a δ P α, ∃ β' ∈ Bins N a δ P' α,
      (∀ i, |β i - β' i| ≤ 1) ∧
      ∀ R : Test, QuadTest N a δ M R →
      (N ^ a) ^ (-(Cs : ℝ)) ≤ |MvPolynomial.eval (fun i => α i) (disc R)| →
      β ∈ Bins N a δ R α → ∀ t ∈ I, |t - t₀| ≤ N ^ (-(CR * a)) / q →
      |MvPolynomial.eval (Fin.snoc (fun i => zline t i) (wline t)) R| ≤ δ * N ^ (CK * a) ∧
      |MvPolynomial.eval (Fin.snoc (fun i => zline t i) (wline t))
        (MvPolynomial.pderiv (3 : Fin 4) R)| ≤ N ^ (CK * a)

end
end Submission.Obl.k4_pair_anchor_jet_bins
