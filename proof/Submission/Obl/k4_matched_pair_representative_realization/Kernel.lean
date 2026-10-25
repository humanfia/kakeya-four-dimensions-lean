import Submission.Obl.k4_matched_pair_representative_realization.Interface

/-!
# The per-pair analytic kernel consumed by the assembly

The assembly (`Assembly*.lean`) needs only the following analytic facts about a single
successful source/witness pair, once a real anchor `α` and a complex detour `σ` have been fixed
for its frame and the broken path from the source through the detour corner to the anchor is
safe for both discriminants.

* `Bins N a δ P α` is a finite set (at most two elements) of integer bins depending only on the
  quadratic test `P` and the anchor: the rounded finite jets at `α` of the at most two local
  root branches of `P`.
* The source's continued branch has a bin `β ∈ Bins P α`, the witness's has `β' ∈ Bins P' α`,
  and these are neighbours.
* Every representative `R` whose discriminant is not small at the anchor and which has `β`
  among its bins is small, with controlled hidden derivative, along the short real segment of
  the trajectory around the source time.
-/

namespace Submission.Obl.k4_matched_pair_representative_realization

open Submission.Obl.k4_quadratic_atlas_normalization

/-- The complexified broken path from a real source `z₀` through the detour corner
`z₀ + σ (α - z₀)` to the real anchor `α`, exactly as in `SafePaths`. -/
def safePath (z₀ α : EuclideanSpace ℝ (Fin 3)) (σ : ℂ) : Set (EuclideanSpace ℂ (Fin 3)) :=
  segment ℝ (emb z₀) (emb z₀ + σ • (emb α - emb z₀)) ∪
    segment ℝ (emb z₀ + σ • (emb α - emb z₀)) (emb α)

/-- Both discriminants have size at least `ρ` on the `ρ`-tube about the safe path: the
complement of the bad event of `SafePaths` (with `A ^ (-C) = ρ`). -/
def SafeFor (ρ : ℝ) (p p' : MvPolynomial (Fin 3) ℝ) (z₀ α : EuclideanSpace ℝ (Fin 3))
    (σ : ℂ) : Prop :=
  ∀ z ∈ Metric.thickening ρ (safePath z₀ α σ),
    ρ ≤ ‖MvPolynomial.eval (fun i => z i) (p.map (algebraMap ℝ ℂ))‖ ∧
      ρ ≤ ‖MvPolynomial.eval (fun i => z i) (p'.map (algebraMap ℝ ℂ))‖

/-- The bounds that `paired` gives every converted source equation. -/
def QuadTest (N a δ : ℝ) (M : ℕ) (P : MvPolynomial (Fin 4) ℝ) : Prop :=
  P.totalDegree ≤ 2 ∧ (∀ d, |P.coeff d| ≤ N ^ M) ∧
    |MvPolynomial.eval (0 : Fin 4 → ℝ)
        (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) P))| ≤ δ⁻¹ ∧
    (disc P).totalDegree ≤ 2 ∧ ∀ d, |(disc P).coeff d| ≤ N ^ a

/-- **The analytic kernel.**  For the safe-path constant `Cs` there are a bin dimension `d`,
absolute exponents `CR`, `CK` and a bin table `Bins` (at most two bins per test and anchor)
such that every safe successful pair has neighbouring source/witness bins, and every
representative with the source bin and a non-small anchor discriminant is small along the
short segment of the trajectory around the source time. -/
def AnalyticKernel : Prop :=
  ∀ Cs : ℕ, 0 < Cs → ∃ (d : ℕ) (CR CK : ℝ)
    (Bins : ℝ → ℝ → ℝ → MvPolynomial (Fin 4) ℝ → EuclideanSpace ℝ (Fin 3) →
      Finset (Fin d → ℤ)),
    0 < CR ∧ 0 < CK ∧ (∀ N a δ P α, (Bins N a δ P α).card ≤ 2) ∧
    ∀ a : ℝ, 0 < a → ∀ M : ℕ, ∃ N₀ : ℝ, ∀ N δ q : ℝ, N₀ ≤ N → 0 < δ → δ ≤ 1 → 1 ≤ q →
      ∀ (P P' : MvPolynomial (Fin 4) ℝ) (z₀ α : EuclideanSpace ℝ (Fin 3)) (σ : ℂ)
        (zline : ℝ → EuclideanSpace ℝ (Fin 3)) (wline : ℝ → ℝ) (t₀ : ℝ) (I : Set ℝ),
      QuadTest N a δ M P → QuadTest N a δ M P' → ‖z₀‖ ≤ 1 / 8 →
      t₀ ∈ I → zline t₀ = z₀ → (∀ t ∈ I, ‖zline t - z₀‖ ≤ q * |t - t₀|) →
      localPair N a δ q P P' z₀ zline wline t₀ I →
      α ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 8) →
      σ ∈ Metric.closedBall (1 / 2 : ℂ) (1 / 4) →
      SafeFor ((N ^ a) ^ (-(Cs : ℝ))) (disc P) (disc P') z₀ α σ →
      ∃ β ∈ Bins N a δ P α, ∃ β' ∈ Bins N a δ P' α, (∀ i, |β i - β' i| ≤ 1) ∧
        ∀ R : MvPolynomial (Fin 4) ℝ, QuadTest N a δ M R →
          (N ^ a) ^ (-(Cs : ℝ)) ≤ |MvPolynomial.eval (fun i => α i) (disc R)| →
          β ∈ Bins N a δ R α →
          ∀ t ∈ I, |t - t₀| ≤ N ^ (-(CR * a)) / q →
            |MvPolynomial.eval (Fin.snoc (fun i => zline t i) (wline t)) R| ≤
                δ * N ^ (CK * a) ∧
              |MvPolynomial.eval (Fin.snoc (fun i => zline t i) (wline t))
                  (MvPolynomial.pderiv (3 : Fin 4) R)| ≤ N ^ (CK * a)

/-- **The discriminant sublevel bound** used to delete source points where a representative's
discriminant is small: a quadratic in three real variables with coefficients at most `N ^ a`
and a non-small value at a point of the `1/8`-ball has small sublevel volume in that ball. -/
def DiscSublevel : Prop :=
  ∀ Cs : ℕ, 0 < Cs → ∃ CD : ℝ, 0 < CD ∧ ∀ a : ℝ, 0 < a → ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
    ∀ (p : MvPolynomial (Fin 3) ℝ) (α : EuclideanSpace ℝ (Fin 3)),
      p.totalDegree ≤ 2 → (∀ d, |p.coeff d| ≤ N ^ a) → ‖α‖ ≤ 1 / 8 →
      (N ^ a) ^ (-(Cs : ℝ)) ≤ |MvPolynomial.eval (fun i => α i) p| →
      MeasureTheory.volume {z : EuclideanSpace ℝ (Fin 3) | ‖z‖ ≤ 1 / 8 ∧
          |MvPolynomial.eval (fun i => z i) p| < N ^ (-(CD * a))} ≤
        ENNReal.ofReal (N ^ (-(3 * a)))

end Submission.Obl.k4_matched_pair_representative_realization
