import Mathlib
import ChallengeDeps
import Submission.Obl.k4_plank_projected_multiplicity
import Submission.Obl.k4_dk4_smoothed_problem
import Submission.Obl.k4_joint_homogenization
import Submission.Obl.k4_profile_density_bounds
import Submission.Obl.k4_profile_endpoint_crop
import Submission.Obl.k4_discrete_of_terminal_charts.Interface
import Submission.Obl.k4_discrete_of_terminal_charts.Comparison
set_option linter.unusedVariables false

/-!
# `Submission.k4_discrete_of_terminal_charts`

The frozen type is `PlankEstimate → SlopeVolumeEstimate → TerminalChartAssertion → DK4`
(`Interface.lean`, x0148). It is cut at `ConstructionOutput` (data satisfying every antecedent of
the terminal-chart assertion and `SlopeDominated`):

* the comparison `SlopeVolumeEstimate → ComparisonStatement` is proved here
  (`comparison_of_slope_volume`, x0146, `Comparison.lean` and its Mathlib-only chain);
* the construction `PlankEstimate → ¬ DK4 → ConstructionOutput` composes the five children:
  `k4_plank_projected_multiplicity` (plank argument), `k4_dk4_smoothed_problem` (smoothing),
  `k4_joint_homogenization` (flattening and homogenization), `k4_profile_density_bounds`
  (the estimates (2.27)) and `k4_profile_endpoint_crop` (endpoint selection and crop).

Between homogenization and the density bounds, the ceilings of the smoothed problem are
transferred along the homogenization subsequence; nothing else is proved in the glue.
-/

namespace Submission.Obl.k4_discrete_of_terminal_charts

open Filter

/-- The construction half of the model reduction, assembled from the five children. -/
theorem construction_of_children (hplank : PlankEstimate) : ¬ DK4 → ConstructionOutput := by
  intro hbad
  have hmult := Submission.k4_plank_projected_multiplicity hplank
  obtain ⟨σ, C, N, K, Λ, ν, E, hσ, hC, hN2, hNt, hK, hΛ, hfmt, hslope, hballs, hjoint, hspread⟩ :=
    Submission.k4_dk4_smoothed_problem hmult hbad
  obtain ⟨ψ, hψ, K', E', hK', hKE, hfmt', F, hprof, hdens, htyp⟩ :=
    Submission.k4_joint_homogenization N K hN2 hNt hK ν E hfmt 1 4 one_pos (by norm_num)
  have hψt : Tendsto ψ atTop atTop := hψ.tendsto_atTop
  have hN2' : ∀ k, 2 ≤ N (ψ k) := fun k => hN2 (ψ k)
  have hNt' : Tendsto (fun k => N (ψ k)) atTop atTop := hNt.comp hψt
  have hΛ' : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, Λ (ψ k) ≤ N (ψ k) ^ ε :=
    fun ε hε => hψt.eventually (hΛ ε hε)
  have hslope' := fun k => hslope (ψ k)
  have hjoint' := fun k => hjoint (ψ k)
  have hballs' : ∀ k, ∃ (m : ℕ) (z : Fin m → EuclideanSpace ℝ (Fin 4)),
      (m : ℝ) ≤ C * N (ψ k) ^ (4 - σ) ∧ ∀ p ∈ E' k, ∃ j : Fin m,
        ‖(WithLp.toLp 2 ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4,
            p.1.2 2 + p.2 * p.1.2 5] : EuclideanSpace ℝ (Fin 4)) - z j‖ ≤ C / N (ψ k) := by
    intro k
    obtain ⟨m, z, hm, hz⟩ := hballs (ψ k)
    exact ⟨m, z, hm, fun p hp => hz p ((hKE k).2 hp)⟩
  have hspread' : ∀ α : ℝ, 0 < α → ∃ θ : ℝ, 0 < θ ∧ ∀ᶠ k in atTop,
      ∀ U : Set (EuclideanSpace ℝ (Fin 3)),
        MeasureTheory.volume U ≤ ENNReal.ofReal (N (ψ k) ^ (-α)) →
        ((ν (ψ k)).prod MeasureTheory.volume)
          {p | p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ (WithLp.toLp 2 ![p.2,
            ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 1,
            ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 2] :
              EuclideanSpace ℝ (Fin 3)) ∈ U} ≤ ENNReal.ofReal (N (ψ k) ^ (-θ)) := by
    intro α hα
    obtain ⟨θ, hθ, hev⟩ := hspread α hα
    exact ⟨θ, hθ, hψt.eventually hev⟩
  obtain ⟨h10, h00, hru⟩ :=
    Submission.k4_profile_density_bounds (fun k => N (ψ k)) K' (fun k => Λ (ψ k))
      (fun k => ν (ψ k)) E' F σ C hN2' hNt' hK' hΛ' hσ hC hfmt' hballs' hjoint' hspread'
      hprof hdens htyp
  obtain ⟨N₁, K₁, L, d, S, η, W, ω, ν₁, E₁, P, B, f, g, G, h1, h2, h3, h4, h5, h6, h7, h8,
      h9, h10', h11, h12, h13, h14, h15, hdom⟩ :=
    Submission.k4_profile_endpoint_crop (fun k => N (ψ k)) K' (fun k => Λ (ψ k))
      (fun k => ν (ψ k)) E' F σ hN2' hNt' hK' hΛ' hσ hfmt' hslope' hprof hdens htyp h10 h00 hru
  exact ⟨N₁, K₁, L, d, S, η, W, ω, ν₁, E₁, P, B, f, g, G,
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10', h11, h12, h13, h14, h15⟩, hdom⟩

/-- The model reduction: plank, slope-volume and terminal-chart inputs give DK4. -/
theorem dk4_of_inputs (hplank : PlankEstimate) (hvol : SlopeVolumeEstimate)
    (hterm : TerminalChartAssertion) : DK4 :=
  dk4_of_construction_comparison hterm (construction_of_children hplank)
    (comparison_of_slope_volume hvol)

end Submission.Obl.k4_discrete_of_terminal_charts

theorem Submission.k4_discrete_of_terminal_charts : (∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 < C ∧ ∀ (D : ℕ), 1 ≤ D → ∀ (n : ℕ) (b u : Fin n → EuclideanSpace ℝ (Fin 2)) (ω : Fin n → ℝ) (A : ℝ) (J : Fin n → Finset (Fin D)), (∀ i : Fin n, ‖b i‖ ≤ 1 ∧ ‖u i‖ ≤ 1) → (∀ i : Fin n, 0 < ω i) → 0 < A → (∀ (c w e₁ e₂ : EuclideanSpace ℝ (Fin 2)) (a β : ℝ), ‖e₁‖ = 1 → ‖e₂‖ = 1 → inner ℝ e₁ e₂ = 0 → 1 ≤ a → a ≤ β → β ≤ (D : ℝ) → ∀ S : Finset (Fin n), (∀ i ∈ S, ∀ t ∈ Set.Icc (0 : ℝ) 1, |inner ℝ (b i + t • u i - c - t • w) e₁| ≤ a / (D : ℝ) ∧ |inner ℝ (b i + t • u i - c - t • w) e₂| ≤ β / (D : ℝ)) → ∑ i ∈ S, ω i ≤ A * a * β) → (∀ i : Fin n, (D : ℝ) ^ (1 - η) ≤ ((J i).card : ℝ)) → ∑ i : Fin n, ω i * ((J i).card : ℝ) ≤ C * A * (D : ℝ) ^ ε * ((((Finset.univ : Finset (Fin n)).sigma J).image (fun p => ((p.2 : ℕ), fun k : Fin 2 => ⌊(D : ℝ) * (b p.1 + (((((p.2 : ℕ) : ℝ) + 1 / 2) / (D : ℝ)) • u p.1)) k⌋))).card : ℝ)) → (∃ C : ℝ, 0 < C ∧ ∀ (P : MvPolynomial (Fin 4) ℝ) (D : Matrix (Fin 2) (Fin 2) ℝ) (c u : EuclideanSpace ℝ (Fin 2)) (t₀ q a K R : ℝ), P.totalDegree ≤ 2 → Matrix.det D ≠ 0 → 0 < q → 0 < a → 1 ≤ K → 1 ≤ R → MeasureTheory.volume {s : EuclideanSpace ℝ (Fin 3) | ‖s‖ ≤ R ∧ ∃ b : EuclideanSpace ℝ (Fin 3), ‖b‖ ≤ R ∧ (∀ t ∈ Set.Icc t₀ (t₀ + q), ‖Matrix.toEuclideanLin (D⁻¹) (WithLp.toLp 2 (fun i : Fin 2 => (b + t • s) i.castSucc - c i - t * u i))‖ ≤ K ∧ |MvPolynomial.eval ![t, (b + t • s) 0, (b + t • s) 1, (b + t • s) 2] P| ≤ K * a) ∧ ∃ t ∈ Set.Icc t₀ (t₀ + q), K⁻¹ ≤ |MvPolynomial.eval ![t, (b + t • s) 0, (b + t • s) 1, (b + t • s) 2] (MvPolynomial.pderiv (3 : Fin 4) P)|} ≤ ENNReal.ofReal (C * K ^ 4 * a * |Matrix.det D| / q ^ 3)) → (∀ N K : ℕ → ℝ, (∀ k, 2 ≤ N k) → Filter.Tendsto N Filter.atTop Filter.atTop → ((∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε) → ∀ L d S η : ℝ, 0 < L → 0 < d → d < 1 → 0 < S → 0 < η → ∀ (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ) (B : (k : ℕ) → Fin (W k) → ℝ) (f : ℝ → ℝ), ∀ (g : (k : ℕ) → Fin (W k) → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal) (G : (k : ℕ) → Fin (W k) → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal), (∃ M D : ℕ, ∀ k, (W k : ℝ) ≤ N k ^ M ∧ (∀ γ, 0 ≤ ω k γ) ∧ (∑ γ, ω k γ) = 1 ∧ (∀ γ, MeasureTheory.IsProbabilityMeasure (ν k γ) ∧ 0 < B k γ ∧ B k γ ≤ N k ^ M ∧ (B k γ)⁻¹ ≤ N k ^ M ∧ (P k γ).totalDegree ≤ 2 ∧ (∀ b, |(P k γ).coeff b| ≤ N k ^ M) ∧ (∃ m : ℕ, (m : ℝ) ≤ N k ^ M ∧ ∃ (c : Fin m → ℝ) (i : Fin m → ℕ) (A : Fin m → Set (Fin 6 → ℝ)), (∀ j, 0 ≤ c j ∧ c j ≤ N k ^ M ∧ (i j : ℝ) ≤ N k ^ M ∧ (∃ m₀ : ℕ, (m₀ : ℝ) ≤ (N k ^ M) ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin 6) ℝ, (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool, ∀ x₀, x₀ ∈ (A j) ↔ b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true) ∧ (∀ x ∈ A j, ∀ b, |x b| ≤ N k ^ M)) ∧ ν k γ = ∑ j, (ENNReal.ofReal (c j)) • MeasureTheory.Measure.map (fun x => (i j, x)) (MeasureTheory.volume.restrict (A j))) ∧ MeasurableSet (E k γ) ∧ E k γ ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 ∧ (∀ p ∈ E k γ, (p.1.1 : ℝ) ≤ N k ^ M ∧ ∀ e, |p.1.2 e| ≤ N k ^ M) ∧ (∀ i, (∃ m₀ : ℕ, (m₀ : ℝ) ≤ (N k ^ M) ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin 7) ℝ, (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool, ∀ x₀, x₀ ∈ ({x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ (E k γ)}) ↔ b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true)) ∧ (∀ᵐ l ∂ν k γ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(WithLp.toLp 2 ![![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 1, ![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 2])‖ + ‖(WithLp.toLp 2 ![l.2 3, l.2 4])‖ ≤ K k ∧ |MvPolynomial.eval (![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5]) (P k γ)| ≤ K k ∧ |MvPolynomial.eval (![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5]) (MvPolynomial.pderiv (3 : Fin 4) (P k γ))| ≤ K k * B k γ ∧ |MvPolynomial.eval (![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5]) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (P k γ)))| ≤ K k * (B k γ) ^ 2) ∧ (∀ᵐ p ∂(((ν k γ).prod MeasureTheory.volume).restrict (E k γ)), B k γ / K k ≤ |MvPolynomial.eval (![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5]) (MvPolynomial.pderiv (3 : Fin 4) (P k γ))|)) ∧ ENNReal.ofReal ((K k)⁻¹) ≤ ∑ γ, ENNReal.ofReal (ω k γ) * (((ν k γ).prod MeasureTheory.volume).restrict (E k γ)) Set.univ) → (∀ k γ r, 0 ≤ r → r ≤ L → Measurable (g k γ r) ∧ MeasureTheory.Measure.map ((fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => ((WithLp.toLp 2 ![p.2, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 1, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 2] : EuclideanSpace ℝ (Fin 3)), ⌊B k γ * ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 3 / ((2 : ℝ) ^ (-(⌊r * Real.log (N k) / Real.log 2⌋ : ℤ)))⌋))) ((((ν k γ).prod MeasureTheory.volume).restrict (E k γ))) = (MeasureTheory.volume.prod MeasureTheory.Measure.count).withDensity (g k γ r)) → (∀ k γ u, 0 < u → u ≤ η * L → Measurable (G k γ u) ∧ MeasureTheory.Measure.map ((fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => ((fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => ((WithLp.toLp 2 ![p.2, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 1, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 2] : EuclideanSpace ℝ (Fin 3)), ⌊B k γ * ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 3 / ((2 : ℝ) ^ (-(⌊L * Real.log (N k) / Real.log 2⌋ : ℤ)))⌋)) p, fun j : Fin 2 => ⌊(WithLp.toLp 2 ![p.1.2 3, p.1.2 4]) j / ((2 : ℝ) ^ (-(⌊u * Real.log (N k) / Real.log 2⌋ : ℤ)))⌋))) ((((ν k γ).prod MeasureTheory.volume).restrict (E k γ))) = ((MeasureTheory.volume.prod MeasureTheory.Measure.count).prod MeasureTheory.Measure.count).withDensity (G k γ u)) → (∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ L → 0 ≤ f s - f r ∧ f s - f r ≤ s - r) → (∀ r τ : ℝ, 0 ≤ r → r ≤ L → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop, (∑ γ, ENNReal.ofReal (ω k γ) * (((ν k γ).prod MeasureTheory.volume).restrict (E k γ)) {p | g k γ r ((fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => ((WithLp.toLp 2 ![p.2, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 1, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 2] : EuclideanSpace ℝ (Fin 3)), ⌊B k γ * ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 3 / ((2 : ℝ) ^ (-(⌊r * Real.log (N k) / Real.log 2⌋ : ℤ)))⌋)) p) < ENNReal.ofReal (N k ^ (-f r - τ)) ∨ ENNReal.ofReal (N k ^ (-f r + τ)) < g k γ r ((fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => ((WithLp.toLp 2 ![p.2, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 1, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 2] : EuclideanSpace ℝ (Fin 3)), ⌊B k γ * ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 3 / ((2 : ℝ) ^ (-(⌊r * Real.log (N k) / Real.log 2⌋ : ℤ)))⌋)) p)}) ≤ ENNReal.ofReal (N k ^ (-c))) → (∀ r : ℝ, 0 ≤ r → r ≤ L → f L - f r ≤ d * (L - r)) → (∀ u τ : ℝ, 0 < u → u ≤ η * L → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop, (∑ γ, ENNReal.ofReal (ω k γ) * (((ν k γ).prod MeasureTheory.volume).restrict (E k γ)) {p | ENNReal.ofReal (N k ^ (-f L - S * u + τ)) < G k γ u ((fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => ((fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => ((WithLp.toLp 2 ![p.2, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 1, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 2] : EuclideanSpace ℝ (Fin 3)), ⌊B k γ * ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 3 / ((2 : ℝ) ^ (-(⌊L * Real.log (N k) / Real.log 2⌋ : ℤ)))⌋)) p, fun j : Fin 2 => ⌊(WithLp.toLp 2 ![p.1.2 3, p.1.2 4]) j / ((2 : ℝ) ^ (-(⌊u * Real.log (N k) / Real.log 2⌋ : ℤ)))⌋)) p)}) ≤ ENNReal.ofReal (N k ^ (-c))) → ∀ h : ℝ, 0 < h → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ M D : ℕ, ∃ K' : ℕ → ℝ, ((∀ k, 1 ≤ K' k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K' k ≤ N (ψ k) ^ ε) ∧ (∀ k, K (ψ k) ≤ K' k) ∧ ∃ T C' : ℕ → ℕ, ∃ (γ : (k : ℕ) → Fin (C' k) → Fin (W (ψ k))) (j : (k : ℕ) → Fin (C' k) → Fin (2 ^ T k)) (c u : (k : ℕ) → Fin (C' k) → EuclideanSpace ℝ (Fin 2)) (Q : (k : ℕ) → Fin (C' k) → Matrix (Fin 2) (Fin 2) ℝ) (R : (k : ℕ) → Fin (C' k) → MvPolynomial (Fin 4) ℝ) (A : (k : ℕ) → Fin (C' k) → Set (ℕ × (Fin 6 → ℝ))) (F : (k : ℕ) → Fin (C' k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)), ∀ k, (2 : ℝ) ^ T k ≤ N (ψ k) ^ h ∧ (C' k : ℝ) ≤ N (ψ k) ^ M ∧ (∀ b b', b ≠ b' → γ k b = γ k b' → j k b = j k b' → Disjoint (A k b) (A k b')) ∧ (∀ b, Matrix.det (Q k b) ≠ 0 ∧ ‖c k b‖ + ‖u k b‖ ≤ N (ψ k) ^ M ∧ (∑ e : Fin 2, ∑ e' : Fin 2, (|Q k b e e'| + |(Q k b)⁻¹ e e'|)) ≤ N (ψ k) ^ M ∧ (∑ e : Fin 2, ∑ e' : Fin 2, |Q k b e e'|) ≤ K' k / (2 : ℝ) ^ T k ∧ (R k b).totalDegree ≤ 2 ∧ (∀ e, |(R k b).coeff e| ≤ N (ψ k) ^ M) ∧ MeasurableSet (A k b) ∧ MeasurableSet (F k b) ∧ (∀ i, (∃ m₀ : ℕ, (m₀ : ℝ) ≤ (N (ψ k) ^ M) ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin 6) ℝ, (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool, ∀ x₀, x₀ ∈ {x | (i, x) ∈ A k b} ↔ b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true) ∧ (∃ m₀ : ℕ, (m₀ : ℝ) ≤ (N (ψ k) ^ M) ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin 7) ℝ, (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool, ∀ x₀, x₀ ∈ ({x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ (F k b)}) ↔ b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true)) ∧ (∀ l ∈ A k b, (l.1 : ℝ) ≤ N (ψ k) ^ M ∧ (∀ e, |l.2 e| ≤ N (ψ k) ^ M) ∧ ∀ t ∈ (Set.Icc (((j k b : ℕ) : ℝ) / (2 : ℝ) ^ T k) ((((j k b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T k)), ‖Matrix.toEuclideanLin ((Q k b)⁻¹) ((WithLp.toLp 2 ![![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 1, ![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 2]) - c k b - t • u k b)‖ ≤ K' k ∧ |MvPolynomial.eval (![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5]) (R k b)| ≤ K' k * ((2 : ℝ) ^ (-(⌊L * Real.log (N (ψ k)) / Real.log 2⌋ : ℤ))) ∧ |MvPolynomial.eval (![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5]) (MvPolynomial.pderiv (3 : Fin 4) (R k b))| ≤ K' k * B (ψ k) (γ k b) ∧ |MvPolynomial.eval (![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5]) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (R k b)))| ≤ K' k * (B (ψ k) (γ k b)) ^ 2 / ((2 : ℝ) ^ (-(⌊L * Real.log (N (ψ k)) / Real.log 2⌋ : ℤ)))) ∧ (∀ p ∈ F k b, p ∈ E (ψ k) (γ k b) ∧ p.1 ∈ A k b ∧ p.2 ∈ (Set.Icc (((j k b : ℕ) : ℝ) / (2 : ℝ) ^ T k) ((((j k b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T k)) ∧ B (ψ k) (γ k b) / K' k ≤ |MvPolynomial.eval (![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5]) (MvPolynomial.pderiv (3 : Fin 4) (R k b))|) ∧ ENNReal.ofReal (N (ψ k) ^ (-f L) * |Matrix.det (Q k b)| / ((2 : ℝ) ^ T k * K' k)) ≤ (((ν (ψ k) (γ k b)).prod MeasureTheory.volume) (F k b))) ∧ ENNReal.ofReal ((K' k)⁻¹) ≤ ∑ b, ENNReal.ofReal (ω (ψ k) (γ k b)) * (((ν (ψ k) (γ k b)).prod MeasureTheory.volume) (F k b))) → ∀ σ : ℝ, 0 < σ → σ ≤ 1 → ∀ c : ℝ, 0 < c → ∀ R : ℝ, 1 ≤ R → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ (n : ℕ) (x v : Fin n → EuclideanSpace ℝ (Fin 4)), c * (2 : ℝ) ^ (3 * k) / ((k : ℝ) + 1) ^ 2 ≤ (n : ℝ) → (∀ i : Fin n, x i 0 = 0 ∧ v i 0 = 1 ∧ ‖v i‖ ≤ 2) → (∀ i j : Fin n, i ≠ j → (2 : ℝ) ^ (-(k : ℤ)) ≤ ‖v i - v j‖) → (∀ i : Fin n, ‖x i‖ ≤ R) → ∀ (m : ℕ) (z : Fin m → EuclideanSpace ℝ (Fin 4)) (ρ : Fin m → ℝ), (m : ℝ) ≤ (2 : ℝ) ^ (((k : ℝ) + 1) * (4 - σ)) → (∀ j : Fin m, (2 : ℝ) ^ (-((k : ℤ) + 1)) < ρ j ∧ ρ j ≤ (2 : ℝ) ^ (-(k : ℤ))) → ¬ (∀ i : Fin n, ENNReal.ofReal (c / ((k : ℝ) + 1) ^ 2) ≤ MeasureTheory.volume {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ x i + t • v i ∈ ⋃ j : Fin m, Metric.ball (z j) (ρ j)}) :=
  Submission.Obl.k4_discrete_of_terminal_charts.frozen_of_parts
    Submission.Obl.k4_discrete_of_terminal_charts.dk4_of_inputs
