import Mathlib
import ChallengeDeps
import Submission.Obl.k4_horizon_light_cell_mass.Asymptotic
set_option linter.unusedVariables false

/-!
# `Submission.k4_horizon_light_cell_mass`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_horizon_light_cell_mass`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_horizon_light_cell_mass/`
belong to this obligation.
-/

theorem Submission.k4_horizon_light_cell_mass : ((fun x : (ℕ × (Fin 6 → ℝ)) → ℝ → Fin 4 → ℝ => (fun y : (ℕ × (Fin 6 → ℝ)) → ℝ → EuclideanSpace ℝ (Fin 2) => (fun v : (ℕ × (Fin 6 → ℝ)) → EuclideanSpace ℝ (Fin 2) => (fun δ : ℝ → ℝ → ℝ => (fun obs : ℝ → ℝ → ((ℕ × (Fin 6 → ℝ)) × ℝ) → EuclideanSpace ℝ (Fin 3) × ℤ => (fun fmt : (n : ℕ) → ℝ → ℕ → Set (Fin n → ℝ) → Prop => (fun prob : (ℕ → ℝ) → (ℕ → ℝ) → ℝ → ℝ → ℝ → ℝ → (W : ℕ → ℕ) → ((k : ℕ) → Fin (W k) → ℝ) → ((k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) → ((k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) → ((k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ) → ((k : ℕ) → Fin (W k) → ℝ) → (ℝ → ℝ) → ((k : ℕ) → Fin (W k) → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal) → ((k : ℕ) → Fin (W k) → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal) → Prop => (∀ N K L d S η W ω ν E P B f g G, prob N K L d S η W ω ν E P B f g G → ∃ H₀ : ℝ, ∀ τ : ℝ, 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop, ∀ ρ₁ ρ₂ : ℝ, 0 < ρ₁ → ρ₁ ≤ N k ^ (-H₀) → 0 < ρ₂ → ρ₂ ≤ N k ^ (-H₀) → (∑ γ, ENNReal.ofReal (ω k γ) * ((ν k γ).prod MeasureTheory.volume) {p | p ∈ E k γ ∧ ((ν k γ).prod MeasureTheory.volume) {p' | p' ∈ E k γ ∧ ⌊p'.2 / ρ₁⌋ = ⌊p.2 / ρ₁⌋ ∧ ⌊(x p'.1 p'.2) 1 / ρ₂⌋ = ⌊(x p.1 p.2) 1 / ρ₂⌋ ∧ ⌊(x p'.1 p'.2) 2 / ρ₂⌋ = ⌊(x p.1 p.2) 2 / ρ₂⌋ ∧ (obs (B k γ) (δ (N k) L) p').2 = (obs (B k γ) (δ (N k) L) p).2} < ENNReal.ofReal (N k ^ (-f L - τ) * ρ₁ * ρ₂ ^ 2)}) ≤ ENNReal.ofReal (N k ^ (-c)))) (fun N K L d S η W ω ν E P B f g G => (∀ k, 2 ≤ N k) ∧ Filter.Tendsto N Filter.atTop Filter.atTop ∧ ((∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε) ∧ 0 < L ∧ 0 < d ∧ d < 1 ∧ 0 < S ∧ 0 < η ∧ (fun μ : (k : ℕ) → Fin (W k) → MeasureTheory.Measure ((ℕ × (Fin 6 → ℝ)) × ℝ) => (∃ M D : ℕ, ∀ k, (W k : ℝ) ≤ N k ^ M ∧ (∀ γ, 0 ≤ ω k γ) ∧ (∑ γ, ω k γ) = 1 ∧ (∀ γ, MeasureTheory.IsProbabilityMeasure (ν k γ) ∧ 0 < B k γ ∧ B k γ ≤ N k ^ M ∧ (B k γ)⁻¹ ≤ N k ^ M ∧ (P k γ).totalDegree ≤ 2 ∧ (∀ b, |(P k γ).coeff b| ≤ N k ^ M) ∧ (∃ m : ℕ, (m : ℝ) ≤ N k ^ M ∧ ∃ (c : Fin m → ℝ) (i : Fin m → ℕ) (A : Fin m → Set (Fin 6 → ℝ)), (∀ j, 0 ≤ c j ∧ c j ≤ N k ^ M ∧ (i j : ℝ) ≤ N k ^ M ∧ (fmt 6 (N k ^ M) D (A j)) ∧ (∀ x ∈ A j, ∀ b, |x b| ≤ N k ^ M)) ∧ ν k γ = ∑ j, (ENNReal.ofReal (c j)) • MeasureTheory.Measure.map (fun x => (i j, x)) (MeasureTheory.volume.restrict (A j))) ∧ MeasurableSet (E k γ) ∧ E k γ ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 ∧ (∀ p ∈ E k γ, (p.1.1 : ℝ) ≤ N k ^ M ∧ ∀ e, |p.1.2 e| ≤ N k ^ M) ∧ (∀ i, (fmt 7 (N k ^ M) D ({x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ (E k γ)}))) ∧ (∀ᵐ l ∂ν k γ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(y l t)‖ + ‖(v l)‖ ≤ K k ∧ |MvPolynomial.eval (x l t) (P k γ)| ≤ K k ∧ |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (P k γ))| ≤ K k * B k γ ∧ |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (P k γ)))| ≤ K k * (B k γ) ^ 2) ∧ (∀ᵐ p ∂(μ k γ), B k γ / K k ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (P k γ))|)) ∧ ENNReal.ofReal ((K k)⁻¹) ≤ ∑ γ, ENNReal.ofReal (ω k γ) * (μ k γ) Set.univ) ∧ (∀ k γ r, 0 ≤ r → r ≤ L → Measurable (g k γ r) ∧ MeasureTheory.Measure.map (obs (B k γ) (δ (N k) r)) (μ k γ) = (MeasureTheory.volume.prod MeasureTheory.Measure.count).withDensity (g k γ r)) ∧ (∀ k γ u, 0 < u → u ≤ η * L → Measurable (G k γ u) ∧ MeasureTheory.Measure.map (fun p : ((ℕ × (Fin 6 → ℝ)) × ℝ) => ((obs (B k γ) (δ (N k) L)) p, fun j : Fin 2 => ⌊(v p.1) j / (δ (N k) u)⌋)) (μ k γ) = ((MeasureTheory.volume.prod MeasureTheory.Measure.count).prod MeasureTheory.Measure.count).withDensity (G k γ u)) ∧ (∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ L → 0 ≤ f s - f r ∧ f s - f r ≤ s - r) ∧ (∀ r τ : ℝ, 0 ≤ r → r ≤ L → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop, (∑ γ, ENNReal.ofReal (ω k γ) * (μ k γ) {p | g k γ r ((obs (B k γ) (δ (N k) r)) p) < ENNReal.ofReal (N k ^ (-f r - τ)) ∨ ENNReal.ofReal (N k ^ (-f r + τ)) < g k γ r ((obs (B k γ) (δ (N k) r)) p)}) ≤ ENNReal.ofReal (N k ^ (-c))) ∧ (∀ r : ℝ, 0 ≤ r → r ≤ L → f L - f r ≤ d * (L - r)) ∧ (∀ u τ : ℝ, 0 < u → u ≤ η * L → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop, (∑ γ, ENNReal.ofReal (ω k γ) * (μ k γ) {p | ENNReal.ofReal (N k ^ (-f L - S * u + τ)) < G k γ u ((fun p : ((ℕ × (Fin 6 → ℝ)) × ℝ) => ((obs (B k γ) (δ (N k) L)) p, fun j : Fin 2 => ⌊(v p.1) j / (δ (N k) u)⌋)) p)}) ≤ ENNReal.ofReal (N k ^ (-c)))) (fun k γ => ((ν k γ).prod MeasureTheory.volume).restrict (E k γ)))) (fun n H D A => ∃ m₀ : ℕ, (m₀ : ℝ) ≤ H ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin n) ℝ, (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool, ∀ x₀, x₀ ∈ A ↔ b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true)) (fun B a p => (WithLp.toLp 2 ![p.2, (x p.1 p.2) 1, (x p.1 p.2) 2], ⌊B * (x p.1 p.2) 3 / a⌋))) (fun N r => (2 : ℝ) ^ (-(⌊r * Real.log N / Real.log 2⌋ : ℤ)))) (fun l => WithLp.toLp 2 ![l.2 3, l.2 4])) (fun l t => WithLp.toLp 2 ![(x l t) 1, (x l t) 2])) (fun l t => ![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5])) := by
  classical
  intro N K L d S η W ω ν E P B f g G h
  rcases h with ⟨hN, hNt, hK, hL, hd, hd1, hS, hη, hfmt,
    hg, hG, hmono, htyp, hLip, hjoint⟩
  obtain ⟨M, D, hfmt⟩ := hfmt
  let μ := fun k γ => ((ν k γ).prod MeasureTheory.volume).restrict (E k γ)
  let a : ℕ → ℝ := fun k => (2 : ℝ) ^ (-(⌊L * Real.log (N k) / Real.log 2⌋ : ℤ))
  have hsource : ∀ k γ, ∃ F : Submission.Obl.k4_horizon_light_cell_mass.Raw → ℝ,
      Submission.Obl.k4_native_base_flattening.NativeMixtureFormat (N k) M D F ∧
      Measurable F ∧ (∀ x, 0 ≤ F x) ∧ (∀ x, |F x| ≤ N k ^ (2 * M)) ∧
      (μ k γ).map Submission.Obl.k4_horizon_light_cell_mass.rawChart =
        MeasureTheory.volume.withDensity (fun x => ENNReal.ofReal (F x)) := by
    intro k γ
    rcases (hfmt k).2.2.2.1 γ with
      ⟨hνprob, hBpos, hBup, hBdown, hPdeg, hPcoeff, hprior,
        hEm, hEsub, hEbound, hEf, htrace, hderiv⟩
    exact Submission.Obl.k4_horizon_light_cell_mass.exists_formatted_source
      (N k) M D (hN k) (ν k γ) (E k γ) hprior hEm hEsub hEf
  have hden : ∀ k γ, Measurable (g k γ L) ∧
      (μ k γ).map (Submission.Obl.k4_horizon_light_cell_mass.pureMap (B k γ) (a k)) =
        Submission.Obl.k4_horizon_light_cell_mass.reference.withDensity (g k γ L) := by
    intro k γ
    exact hg k γ L hL.le le_rfl
  have htyp' : ∀ τ : ℝ, 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop,
      (∑ γ, ENNReal.ofReal (ω k γ) * (μ k γ)
        {p | g k γ L (Submission.Obl.k4_horizon_light_cell_mass.pureMap (B k γ) (a k) p) <
          ENNReal.ofReal (N k ^ (-f L - τ))}) ≤ ENNReal.ofReal (N k ^ (-c)) := by
    intro τ hτ
    obtain ⟨c, hc, he⟩ := htyp L τ hL.le le_rfl hτ
    refine ⟨c, hc, he.mono (fun k hk => ?_)⟩
    refine le_trans (Finset.sum_le_sum (fun γ _ => ?_)) hk
    exact mul_le_mul_right (MeasureTheory.measure_mono (fun p hp => Or.inl hp)) _
  obtain ⟨H, hH⟩ := Submission.Obl.k4_horizon_light_cell_mass.weighted_light_cells
    N hN hNt M D W ω (fun k => (hfmt k).2.1) (fun k => (hfmt k).2.2.1)
    μ B a (fun k γ => g k γ L) (f L) hsource hden htyp'
  refine ⟨H, ?_⟩
  intro τ hτ
  obtain ⟨c, hc, he⟩ := hH τ hτ
  refine ⟨c, hc, he.mono (fun k hk => ?_)⟩
  intro ρ₁ ρ₂ hρ₁ hρ₁H hρ₂ hρ₂H
  have hh := hk ρ₁ ρ₂ hρ₁ hρ₁H hρ₂ hρ₂H
  simpa only [μ, a, ← Submission.Obl.k4_horizon_light_cell_mass.original_lightMass_eq,
    Matrix.cons_val] using hh
