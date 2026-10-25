import Submission.Obl.k4_pair_bin_atlas_assembly.Kernel

namespace Submission.Obl.k4_pair_bin_atlas_assembly

/-- The finite-dimensional bin table and its absolute loss exponents, chosen
once at the safe-path exponent. -/
structure BinKernel (Cs : ℕ) where
  d : ℕ
  CR : ℝ
  CK : ℝ
  Bins : ℝ → ℝ → ℝ → MvPolynomial (Fin 4) ℝ → EuclideanSpace ℝ (Fin 3) →
    Finset (Fin d → ℤ)
  CR_pos : 0 < CR
  CK_pos : 0 < CK
  card_le : ∀ N a δ P α, (Bins N a δ P α).card ≤ 2
  threshold : ∀ a : ℝ, 0 < a → ∀ M : ℕ, ∃ N₀ : ℝ, ∀ N δ q : ℝ, N₀ ≤ N → 0 < δ → δ ≤ 1 → 1 ≤ q →
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

/-- The per-pair transfer assertion at one fixed resolution and block frequency. -/
def BinKernel.At {Cs : ℕ} (k : BinKernel Cs) (N a δ q : ℝ) (M : ℕ) : Prop :=
  ∀ (P P' : MvPolynomial (Fin 4) ℝ) (z₀ α : EuclideanSpace ℝ (Fin 3)) (σ : ℂ)
        (zline : ℝ → EuclideanSpace ℝ (Fin 3)) (wline : ℝ → ℝ) (t₀ : ℝ) (I : Set ℝ),
      QuadTest N a δ M P → QuadTest N a δ M P' → ‖z₀‖ ≤ 1 / 8 →
      t₀ ∈ I → zline t₀ = z₀ → (∀ t ∈ I, ‖zline t - z₀‖ ≤ q * |t - t₀|) →
      localPair N a δ q P P' z₀ zline wline t₀ I →
      α ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 8) →
      σ ∈ Metric.closedBall (1 / 2 : ℂ) (1 / 4) →
      SafeFor ((N ^ a) ^ (-(Cs : ℝ))) (disc P) (disc P') z₀ α σ →
      ∃ β ∈ k.Bins N a δ P α, ∃ β' ∈ k.Bins N a δ P' α, (∀ i, |β i - β' i| ≤ 1) ∧
        ∀ R : MvPolynomial (Fin 4) ℝ, QuadTest N a δ M R →
          (N ^ a) ^ (-(Cs : ℝ)) ≤ |MvPolynomial.eval (fun i => α i) (disc R)| →
          β ∈ k.Bins N a δ R α →
          ∀ t ∈ I, |t - t₀| ≤ N ^ (-(k.CR * a)) / q →
            |MvPolynomial.eval (Fin.snoc (fun i => zline t i) (wline t)) R| ≤
                δ * N ^ (k.CK * a) ∧
              |MvPolynomial.eval (Fin.snoc (fun i => zline t i) (wline t))
                  (MvPolynomial.pderiv (3 : Fin 4) R)| ≤ N ^ (k.CK * a)

theorem BinKernel.at_large {Cs : ℕ} (k : BinKernel Cs) (a : ℝ) (ha : 0 < a) (M : ℕ) :
    ∃ N₀ : ℝ, ∀ N δ q : ℝ, N₀ ≤ N → 0 < δ → δ ≤ 1 → 1 ≤ q →
      k.At N a δ q M := k.threshold a ha M


theorem AnalyticKernel.binKernel (h : AnalyticKernel) (Cs : ℕ) (hCs : 0 < Cs) :
    Nonempty (BinKernel Cs) := by
  obtain ⟨d, CR, CK, Bins, hCR, hCK, hcard, hthreshold⟩ := h Cs hCs
  exact ⟨⟨d, CR, CK, Bins, hCR, hCK, hcard, hthreshold⟩⟩

end Submission.Obl.k4_pair_bin_atlas_assembly
