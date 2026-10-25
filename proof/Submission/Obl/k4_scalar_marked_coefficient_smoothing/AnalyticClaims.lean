import Submission.Obl.k4_scalar_marked_coefficient_smoothing.Interface

namespace Submission.Obl.k4_scalar_marked_coefficient_smoothing

open MeasureTheory Set
open scoped ENNReal

/-- The two density clauses, separated from the support clause of `RawEstimates`. -/
def DensityCeilings (N K d s m S U c : ℝ) (angular : Bool)
    (μ : Measure (Traj × ℝ)) : Prop :=
  (∀ r : ℝ, 0 ≤ r → r ≤ s → ∃ g : Obs → ℝ≥0∞,
    Measurable g ∧ μ.map (observation N r) = baseRef.withDensity g ∧
      ∀ᵐ z ∂baseRef, g z ≤ ENNReal.ofReal (K * c * N ^ (-d * r))) ∧
  (∀ r u : ℝ, 0 ≤ r → r ≤ s → 0 ≤ u → u ≤ 4 * (m + s + 1) →
    ∃ G : AugObs → ℝ≥0∞,
      Measurable G ∧ μ.map (velocityObservation N r u) = jointRef.withDensity G ∧
      (∀ᵐ z ∂jointRef,
        G z ≤ ENNReal.ofReal (K * c * N ^ (-d * r) * min 1 (N ^ (m - u)))) ∧
      (r = s → angular = true → 0 < u → u ≤ U → ∀ᵐ z ∂jointRef,
        G z ≤ ENNReal.ofReal (K * c * N ^ (-d * s - S * u))))

/-- Fixed-sample density transfer; no sequence, tag construction, or support output. -/
def DensityTransferClaim : Prop :=
  ∃ A : ℝ, 1 ≤ A ∧ ∃ q : ℕ,
    ∀ N K d s m S U c : ℝ,
      2 ≤ N → 1 ≤ K → 0 ≤ d → d < 1 → 0 < s → s < m →
      0 < S → 0 < U → U < m → 0 < c →
      ∀ (α : Type) [MeasurableSpace α] (ν : Measure α) (μ : Measure (α × ℝ))
        (b : α → Coeff) (angular : Bool),
      MeshInput N K d s m S U α ν μ b c angular →
      ∀ (H J : ℕ) (tag : α → Fin H) (b₀ : Fin H → Coeff)
        (w : Fin H → ℝ) (mark : Fin H → Fin J → Bool),
      1 ≤ J → 1 ≤ (J : ℝ) * N ^ (-m) → (J : ℝ) * N ^ (-m) ≤ 2 →
      (∀ j, 0 ≤ w j) → (∑ j, w j) = 1 →
      (∀ j i, |b₀ j i| ≤ K + N ^ (-10 * (m + s + 1))) →
      Coupling N (2 * K) s m α ν μ b H J tag b₀ w mark →
      DensityCeilings N (A * K ^ q) d s m S U c angular
        (MarkedLaw (N ^ (-m)) H J b₀ w mark)

/-- A geometric support transfer, independent of mesh caps and all asymptotics. -/
def SupportTransferClaim : Prop :=
  ∃ A : ℝ, 1 ≤ A ∧ ∃ q : ℕ,
    ∀ K σ a δ : ℝ,
      1 ≤ K → 0 < δ → δ ≤ σ → 0 < σ → σ ≤ 1 → σ ≤ a →
      ∀ (α : Type) [MeasurableSpace α] (μ : Measure (α × ℝ)) (b : α → Coeff),
      Measurable b → (∀ l i, |b l i| ≤ K) →
      ∀ (H J : ℕ) (tag : α → Fin H) (b₀ : Fin H → Coeff)
        (w : Fin H → ℝ) (mark : Fin H → Fin J → Bool),
      1 ≤ J → 1 ≤ (J : ℝ) * σ → (J : ℝ) * σ ≤ 2 →
      Measurable tag → (∀ j, 0 ≤ w j) →
      (∀ l i, |b l i - b₀ (tag l) i| ≤ δ) →
      (∀ j z, mark j z = true →
        ENNReal.ofReal (w j / ((J : ℝ) * (2 * K))) ≤
          μ {p | tag p.1 = j ∧ p.2 ∈ timeCell J z}) →
      ∀ F : Finset ((Fin 2 → ℤ) × ℤ),
      (∀ᵐ p ∂μ, (meshCode b σ p, (⌊curveX b p.1 p.2 / a⌋ : ℤ)) ∈ F) →
      ∃ B : Set Obs, MeasurableSet B ∧
        baseRef B ≤ ENNReal.ofReal (A * K ^ q * ((F.card : ℝ) * σ ^ 2)) ∧
        ∀ᵐ p ∂(MarkedLaw σ H J b₀ w mark),
          ((![p.2, curveY Prod.snd p.1 p.2] : Fin 2 → ℝ),
            (⌊curveX Prod.snd p.1 p.2 / a⌋ : ℤ)) ∈ B

end Submission.Obl.k4_scalar_marked_coefficient_smoothing
