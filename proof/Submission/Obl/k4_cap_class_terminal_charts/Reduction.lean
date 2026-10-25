import Submission.Obl.k4_cap_class_terminal_charts.Charts

namespace Submission.Obl.k4_cap_class_terminal_charts

open Filter MeasureTheory

/-- The finite-chart criterion produces the fully expanded output in the frozen theorem.
In particular it preserves a common polynomial format bound as the loss tends to zero. -/
theorem expanded_charts_of_fixed_tolerances
    (N K : ℕ → ℝ) (L : ℝ) (f : ℝ → ℝ) (h : ℝ) (M D : ℕ)
    (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ)
    (ν : (k : ℕ) → Fin (W k) → Measure Trajectory)
    (E : (k : ℕ) → Fin (W k) → Set Incidence)
    (B : (k : ℕ) → Fin (W k) → ℝ) (hN : ∀ k, 1 ≤ N k)
    (hfinite : ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop,
      ∃ κ : ℝ, 1 ≤ κ ∧ K k ≤ κ ∧ κ ≤ N k ^ ε ∧
        HasCharts (W k) (N k) κ (f L)
          ((2 : ℝ) ^ (-(⌊L * Real.log (N k) / Real.log 2⌋ : ℤ))) h M D
          (ω k) (ν k) (E k) (B k)) :
∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ M D : ℕ, ∃ K' : ℕ → ℝ, ((∀ k, 1 ≤ K' k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K' k ≤ N (ψ k) ^ ε) ∧ (∀ k, K (ψ k) ≤ K' k) ∧ ∃ T C' : ℕ → ℕ, ∃ (γ : (k : ℕ) → Fin (C' k) → Fin (W (ψ k))) (j : (k : ℕ) → Fin (C' k) → Fin (2 ^ T k)) (c u : (k : ℕ) → Fin (C' k) → EuclideanSpace ℝ (Fin 2)) (Q : (k : ℕ) → Fin (C' k) → Matrix (Fin 2) (Fin 2) ℝ) (R : (k : ℕ) → Fin (C' k) → MvPolynomial (Fin 4) ℝ) (A : (k : ℕ) → Fin (C' k) → Set (ℕ × (Fin 6 → ℝ))) (F : (k : ℕ) → Fin (C' k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)), ∀ k, (2 : ℝ) ^ T k ≤ N (ψ k) ^ h ∧ (C' k : ℝ) ≤ N (ψ k) ^ M ∧ (∀ b b', b ≠ b' → γ k b = γ k b' → j k b = j k b' → Disjoint (A k b) (A k b')) ∧ (∀ b, Matrix.det (Q k b) ≠ 0 ∧ ‖c k b‖ + ‖u k b‖ ≤ N (ψ k) ^ M ∧ (∑ e : Fin 2, ∑ e' : Fin 2, (|Q k b e e'| + |(Q k b)⁻¹ e e'|)) ≤ N (ψ k) ^ M ∧ (∑ e : Fin 2, ∑ e' : Fin 2, |Q k b e e'|) ≤ K' k / (2 : ℝ) ^ T k ∧ (R k b).totalDegree ≤ 2 ∧ (∀ e, |(R k b).coeff e| ≤ N (ψ k) ^ M) ∧ MeasurableSet (A k b) ∧ MeasurableSet (F k b) ∧ (∀ i, (∃ m₀ : ℕ, (m₀ : ℝ) ≤ (N (ψ k) ^ M) ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin 6) ℝ, (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool, ∀ x₀, x₀ ∈ {x | (i, x) ∈ A k b} ↔ b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true) ∧ (∃ m₀ : ℕ, (m₀ : ℝ) ≤ (N (ψ k) ^ M) ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin 7) ℝ, (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool, ∀ x₀, x₀ ∈ ({x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ (F k b)}) ↔ b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true)) ∧ (∀ l ∈ A k b, (l.1 : ℝ) ≤ N (ψ k) ^ M ∧ (∀ e, |l.2 e| ≤ N (ψ k) ^ M) ∧ ∀ t ∈ (Set.Icc (((j k b : ℕ) : ℝ) / (2 : ℝ) ^ T k) ((((j k b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T k)), ‖Matrix.toEuclideanLin ((Q k b)⁻¹) ((WithLp.toLp 2 ![![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 1, ![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 2]) - c k b - t • u k b)‖ ≤ K' k ∧ |MvPolynomial.eval (![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5]) (R k b)| ≤ K' k * ((2 : ℝ) ^ (-(⌊L * Real.log (N (ψ k)) / Real.log 2⌋ : ℤ))) ∧ |MvPolynomial.eval (![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5]) (MvPolynomial.pderiv (3 : Fin 4) (R k b))| ≤ K' k * B (ψ k) (γ k b) ∧ |MvPolynomial.eval (![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5]) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (R k b)))| ≤ K' k * (B (ψ k) (γ k b)) ^ 2 / ((2 : ℝ) ^ (-(⌊L * Real.log (N (ψ k)) / Real.log 2⌋ : ℤ)))) ∧ (∀ p ∈ F k b, p ∈ E (ψ k) (γ k b) ∧ p.1 ∈ A k b ∧ p.2 ∈ (Set.Icc (((j k b : ℕ) : ℝ) / (2 : ℝ) ^ T k) ((((j k b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T k)) ∧ B (ψ k) (γ k b) / K' k ≤ |MvPolynomial.eval (![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5]) (MvPolynomial.pderiv (3 : Fin 4) (R k b))|) ∧ ENNReal.ofReal (N (ψ k) ^ (-f L) * |Matrix.det (Q k b)| / ((2 : ℝ) ^ T k * K' k)) ≤ (((ν (ψ k) (γ k b)).prod MeasureTheory.volume) (F k b))) ∧ ENNReal.ofReal ((K' k)⁻¹) ≤ ∑ b, ENNReal.ofReal (ω (ψ k) (γ k b)) * (((ν (ψ k) (γ k b)).prod MeasureTheory.volume) (F k b)) := by
  obtain ⟨ψ, hψ, κ, hκ, hKκ, T, s, hs⟩ := charts_of_fixed_tolerances
    N K (fun k => (2 : ℝ) ^ (-(⌊L * Real.log (N k) / Real.log 2⌋ : ℤ)))
    (f L) h M D W ω ν E B hN hfinite
  refine ⟨ψ, hψ, M, D, κ, hκ, hKκ, T, (fun k => (s k).count),
    (fun k => (s k).world), (fun k => (s k).block), (fun k => (s k).center),
    (fun k => (s k).speed), (fun k => (s k).frame), (fun k => (s k).test),
    (fun k => (s k).assignment), (fun k => (s k).event), ?_⟩
  exact hs

end Submission.Obl.k4_cap_class_terminal_charts
