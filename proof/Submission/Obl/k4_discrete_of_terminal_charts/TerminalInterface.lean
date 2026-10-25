import Submission.Obl.k4_discrete_of_terminal_charts.SlopeComparison
import Submission.Obl.k4_discrete_of_terminal_charts.Interface

/-! The explicit terminal assertion and a record of its input data. All fields are
transparent abbreviations for the corresponding Mathlib-only frozen hypotheses. -/

namespace Submission.Obl.k4_discrete_of_terminal_charts

noncomputable section

structure ProfileInput (N K : ℕ → ℝ) where
  L : ℝ
  d : ℝ
  S : ℝ
  η : ℝ
  L_pos : 0 < L
  d_pos : 0 < d
  d_lt_one : d < 1
  S_pos : 0 < S
  eta_pos : 0 < η
  W : ℕ → ℕ
  ω : (k : ℕ) → Fin (W k) → ℝ
  ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))
  E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)
  P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ
  B : (k : ℕ) → Fin (W k) → ℝ
  f : ℝ → ℝ
  g : (k : ℕ) → Fin (W k) → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal
  G : (k : ℕ) → Fin (W k) → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal
  tempered : ∃ M D : ℕ, ∀ k, (W k : ℝ) ≤ N k ^ M ∧ (∀ γ, 0 ≤ ω k γ) ∧ (∑ γ, ω k γ) = 1 ∧ (∀ γ, MeasureTheory.IsProbabilityMeasure (ν k γ) ∧ 0 < B k γ ∧ B k γ ≤ N k ^ M ∧ (B k γ)⁻¹ ≤ N k ^ M ∧ (P k γ).totalDegree ≤ 2 ∧ (∀ b, |(P k γ).coeff b| ≤ N k ^ M) ∧ (∃ m : ℕ, (m : ℝ) ≤ N k ^ M ∧ ∃ (c : Fin m → ℝ) (i : Fin m → ℕ) (A : Fin m → Set (Fin 6 → ℝ)), (∀ j, 0 ≤ c j ∧ c j ≤ N k ^ M ∧ (i j : ℝ) ≤ N k ^ M ∧ (∃ m₀ : ℕ, (m₀ : ℝ) ≤ (N k ^ M) ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin 6) ℝ, (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool, ∀ x₀, x₀ ∈ (A j) ↔ b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true) ∧ (∀ x ∈ A j, ∀ b, |x b| ≤ N k ^ M)) ∧ ν k γ = ∑ j, (ENNReal.ofReal (c j)) • MeasureTheory.Measure.map (fun x => (i j, x)) (MeasureTheory.volume.restrict (A j))) ∧ MeasurableSet (E k γ) ∧ E k γ ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 ∧ (∀ p ∈ E k γ, (p.1.1 : ℝ) ≤ N k ^ M ∧ ∀ e, |p.1.2 e| ≤ N k ^ M) ∧ (∀ i, (∃ m₀ : ℕ, (m₀ : ℝ) ≤ (N k ^ M) ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin 7) ℝ, (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool, ∀ x₀, x₀ ∈ ({x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ (E k γ)}) ↔ b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true)) ∧ (∀ᵐ l ∂ν k γ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(WithLp.toLp 2 ![![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 1, ![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 2])‖ + ‖(WithLp.toLp 2 ![l.2 3, l.2 4])‖ ≤ K k ∧ |MvPolynomial.eval (![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5]) (P k γ)| ≤ K k ∧ |MvPolynomial.eval (![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5]) (MvPolynomial.pderiv (3 : Fin 4) (P k γ))| ≤ K k * B k γ ∧ |MvPolynomial.eval (![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5]) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (P k γ)))| ≤ K k * (B k γ) ^ 2) ∧ (∀ᵐ p ∂(((ν k γ).prod MeasureTheory.volume).restrict (E k γ)), B k γ / K k ≤ |MvPolynomial.eval (![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5]) (MvPolynomial.pderiv (3 : Fin 4) (P k γ))|)) ∧ ENNReal.ofReal ((K k)⁻¹) ≤ ∑ γ, ENNReal.ofReal (ω k γ) * (((ν k γ).prod MeasureTheory.volume).restrict (E k γ)) Set.univ
  pure_density : ∀ k γ r, 0 ≤ r → r ≤ L → Measurable (g k γ r) ∧ MeasureTheory.Measure.map ((fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => ((WithLp.toLp 2 ![p.2, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 1, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 2] : EuclideanSpace ℝ (Fin 3)), ⌊B k γ * ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 3 / ((2 : ℝ) ^ (-(⌊r * Real.log (N k) / Real.log 2⌋ : ℤ)))⌋))) ((((ν k γ).prod MeasureTheory.volume).restrict (E k γ))) = (MeasureTheory.volume.prod MeasureTheory.Measure.count).withDensity (g k γ r)
  angular_density : ∀ k γ u, 0 < u → u ≤ η * L → Measurable (G k γ u) ∧ MeasureTheory.Measure.map ((fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => ((fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => ((WithLp.toLp 2 ![p.2, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 1, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 2] : EuclideanSpace ℝ (Fin 3)), ⌊B k γ * ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 3 / ((2 : ℝ) ^ (-(⌊L * Real.log (N k) / Real.log 2⌋ : ℤ)))⌋)) p, fun j : Fin 2 => ⌊(WithLp.toLp 2 ![p.1.2 3, p.1.2 4]) j / ((2 : ℝ) ^ (-(⌊u * Real.log (N k) / Real.log 2⌋ : ℤ)))⌋))) ((((ν k γ).prod MeasureTheory.volume).restrict (E k γ))) = ((MeasureTheory.volume.prod MeasureTheory.Measure.count).prod MeasureTheory.Measure.count).withDensity (G k γ u)
  lipschitz_profile : ∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ L → 0 ≤ f s - f r ∧ f s - f r ≤ s - r
  homogeneous : ∀ r τ : ℝ, 0 ≤ r → r ≤ L → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop, (∑ γ, ENNReal.ofReal (ω k γ) * (((ν k γ).prod MeasureTheory.volume).restrict (E k γ)) {p | g k γ r ((fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => ((WithLp.toLp 2 ![p.2, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 1, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 2] : EuclideanSpace ℝ (Fin 3)), ⌊B k γ * ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 3 / ((2 : ℝ) ^ (-(⌊r * Real.log (N k) / Real.log 2⌋ : ℤ)))⌋)) p) < ENNReal.ofReal (N k ^ (-f r - τ)) ∨ ENNReal.ofReal (N k ^ (-f r + τ)) < g k γ r ((fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => ((WithLp.toLp 2 ![p.2, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 1, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 2] : EuclideanSpace ℝ (Fin 3)), ⌊B k γ * ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 3 / ((2 : ℝ) ^ (-(⌊r * Real.log (N k) / Real.log 2⌋ : ℤ)))⌋)) p)}) ≤ ENNReal.ofReal (N k ^ (-c))
  pure_cap : ∀ r : ℝ, 0 ≤ r → r ≤ L → f L - f r ≤ d * (L - r)
  angular_cap : ∀ u τ : ℝ, 0 < u → u ≤ η * L → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop, (∑ γ, ENNReal.ofReal (ω k γ) * (((ν k γ).prod MeasureTheory.volume).restrict (E k γ)) {p | ENNReal.ofReal (N k ^ (-f L - S * u + τ)) < G k γ u ((fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => ((fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => ((WithLp.toLp 2 ![p.2, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 1, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 2] : EuclideanSpace ℝ (Fin 3)), ⌊B k γ * ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 3 / ((2 : ℝ) ^ (-(⌊L * Real.log (N k) / Real.log 2⌋ : ℤ)))⌋)) p, fun j : Fin 2 => ⌊(WithLp.toLp 2 ![p.1.2 3, p.1.2 4]) j / ((2 : ℝ) ^ (-(⌊u * Real.log (N k) / Real.log 2⌋ : ℤ)))⌋)) p)}) ≤ ENNReal.ofReal (N k ^ (-c))

def ProfileInput.HasCharts {N K : ℕ → ℝ} (data : ProfileInput N K) (h : ℝ) : Prop :=
  ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ M D : ℕ, ∃ K' : ℕ → ℝ, ((∀ k, 1 ≤ K' k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K' k ≤ N (ψ k) ^ ε) ∧ (∀ k, K (ψ k) ≤ K' k) ∧ ∃ T C' : ℕ → ℕ, ∃ (γ : (k : ℕ) → Fin (C' k) → Fin (data.W (ψ k))) (j : (k : ℕ) → Fin (C' k) → Fin (2 ^ T k)) (c u : (k : ℕ) → Fin (C' k) → EuclideanSpace ℝ (Fin 2)) (Q : (k : ℕ) → Fin (C' k) → Matrix (Fin 2) (Fin 2) ℝ) (R : (k : ℕ) → Fin (C' k) → MvPolynomial (Fin 4) ℝ) (A : (k : ℕ) → Fin (C' k) → Set (ℕ × (Fin 6 → ℝ))) (F : (k : ℕ) → Fin (C' k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)), ∀ k, (2 : ℝ) ^ T k ≤ N (ψ k) ^ h ∧ (C' k : ℝ) ≤ N (ψ k) ^ M ∧ (∀ b b', b ≠ b' → γ k b = γ k b' → j k b = j k b' → Disjoint (A k b) (A k b')) ∧ (∀ b, Matrix.det (Q k b) ≠ 0 ∧ ‖c k b‖ + ‖u k b‖ ≤ N (ψ k) ^ M ∧ (∑ e : Fin 2, ∑ e' : Fin 2, (|Q k b e e'| + |(Q k b)⁻¹ e e'|)) ≤ N (ψ k) ^ M ∧ (∑ e : Fin 2, ∑ e' : Fin 2, |Q k b e e'|) ≤ K' k / (2 : ℝ) ^ T k ∧ (R k b).totalDegree ≤ 2 ∧ (∀ e, |(R k b).coeff e| ≤ N (ψ k) ^ M) ∧ MeasurableSet (A k b) ∧ MeasurableSet (F k b) ∧ (∀ i, (∃ m₀ : ℕ, (m₀ : ℝ) ≤ (N (ψ k) ^ M) ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin 6) ℝ, (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool, ∀ x₀, x₀ ∈ {x | (i, x) ∈ A k b} ↔ b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true) ∧ (∃ m₀ : ℕ, (m₀ : ℝ) ≤ (N (ψ k) ^ M) ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin 7) ℝ, (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool, ∀ x₀, x₀ ∈ ({x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ (F k b)}) ↔ b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true)) ∧ (∀ l ∈ A k b, (l.1 : ℝ) ≤ N (ψ k) ^ M ∧ (∀ e, |l.2 e| ≤ N (ψ k) ^ M) ∧ ∀ t ∈ (Set.Icc (((j k b : ℕ) : ℝ) / (2 : ℝ) ^ T k) ((((j k b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T k)), ‖Matrix.toEuclideanLin ((Q k b)⁻¹) ((WithLp.toLp 2 ![![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 1, ![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 2]) - c k b - t • u k b)‖ ≤ K' k ∧ |MvPolynomial.eval (![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5]) (R k b)| ≤ K' k * ((2 : ℝ) ^ (-(⌊data.L * Real.log (N (ψ k)) / Real.log 2⌋ : ℤ))) ∧ |MvPolynomial.eval (![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5]) (MvPolynomial.pderiv (3 : Fin 4) (R k b))| ≤ K' k * data.B (ψ k) (γ k b) ∧ |MvPolynomial.eval (![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5]) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (R k b)))| ≤ K' k * (data.B (ψ k) (γ k b)) ^ 2 / ((2 : ℝ) ^ (-(⌊data.L * Real.log (N (ψ k)) / Real.log 2⌋ : ℤ)))) ∧ (∀ p ∈ F k b, p ∈ data.E (ψ k) (γ k b) ∧ p.1 ∈ A k b ∧ p.2 ∈ (Set.Icc (((j k b : ℕ) : ℝ) / (2 : ℝ) ^ T k) ((((j k b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T k)) ∧ data.B (ψ k) (γ k b) / K' k ≤ |MvPolynomial.eval (![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5]) (MvPolynomial.pderiv (3 : Fin 4) (R k b))|) ∧ ENNReal.ofReal (N (ψ k) ^ (-data.f data.L) * |Matrix.det (Q k b)| / ((2 : ℝ) ^ T k * K' k)) ≤ (((data.ν (ψ k) (γ k b)).prod MeasureTheory.volume) (F k b))) ∧ ENNReal.ofReal ((K' k)⁻¹) ≤ ∑ b, ENNReal.ofReal (data.ω (ψ k) (γ k b)) * (((data.ν (ψ k) (γ k b)).prod MeasureTheory.volume) (F k b))

theorem ProfileInput.hasCharts {N K : ℕ → ℝ} (data : ProfileInput N K)
    (hterm : TerminalChartAssertion) (hN : ∀ k, 2 ≤ N k)
    (hNt : Filter.Tendsto N Filter.atTop Filter.atTop)
    (hK : (∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε)
    {h : ℝ} (hh : 0 < h) : data.HasCharts h :=
  hterm N K hN hNt hK data.L data.d data.S data.η
    data.L_pos data.d_pos data.d_lt_one data.S_pos data.eta_pos
    data.W data.ω data.ν data.E data.P data.B data.f data.g data.G
    data.tempered data.pure_density data.angular_density data.lipschitz_profile
    data.homogeneous data.pure_cap data.angular_cap h hh

end

end Submission.Obl.k4_discrete_of_terminal_charts
