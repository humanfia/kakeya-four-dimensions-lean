import Submission.Obl.k4_quadratic_atlas_normalization.Interface

/-!
Adapted from this LOT tree, o103, session x0360, commit 642b39c,
`Submission/Obl/k4_initial_horizon_bound/Defs.lean`.

# Named forms of the frozen abbreviations of `Submission.k4_initial_horizon_bound`

The frozen statement is written with immediately applied lambdas (graph point `x`, base `y`,
velocity `v`, dyadic thickness `δ`, observation `obs`, Boolean format `fmt`, the problem
predicate `prob` and the chart predicate `chart`). Here each lambda gets a name; the frozen
statement is definitionally `Outer.HorizonStatement`.
-/

open MeasureTheory

namespace Submission.Obl.k4_horizon_chart_assembly

noncomputable section

/-- The graph point of an indexed line at time `t`. -/
abbrev xl := Submission.Obl.k4_quadratic_atlas_normalization.x

/-- The base point. -/
abbrev yl := Submission.Obl.k4_quadratic_atlas_normalization.y

/-- The base velocity. -/
def vl : (ℕ × (Fin 6 → ℝ)) → EuclideanSpace ℝ (Fin 2) :=
  fun l => WithLp.toLp 2 ![l.2 3, l.2 4]

/-- The dyadic thickness `δ(N, r)`. -/
abbrev dl := Submission.Obl.k4_quadratic_atlas_normalization.δ

/-- The observation at derivative scale `B` and hidden width `a`. -/
abbrev obsl := Submission.Obl.k4_quadratic_atlas_normalization.obs

/-- Boolean polynomial format. -/
abbrev Fmt := Submission.Obl.k4_quadratic_atlas_normalization.fmt

/-- The problem predicate. -/
def Prob : (ℕ → ℝ) → (ℕ → ℝ) → ℝ → ℝ → ℝ → ℝ → (W : ℕ → ℕ) → ((k : ℕ) → Fin (W k) → ℝ) → ((k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) → ((k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) → ((k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ) → ((k : ℕ) → Fin (W k) → ℝ) → (ℝ → ℝ) → ((k : ℕ) → Fin (W k) → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal) → ((k : ℕ) → Fin (W k) → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal) → Prop :=
  (fun (x : (ℕ × (Fin 6 → ℝ)) → ℝ → Fin 4 → ℝ) (y : (ℕ × (Fin 6 → ℝ)) → ℝ → EuclideanSpace ℝ (Fin 2)) (v : (ℕ × (Fin 6 → ℝ)) → EuclideanSpace ℝ (Fin 2)) (δ : ℝ → ℝ → ℝ) (obs : ℝ → ℝ → ((ℕ × (Fin 6 → ℝ)) × ℝ) → EuclideanSpace ℝ (Fin 3) × ℤ) (fmt : (n : ℕ) → ℝ → ℕ → Set (Fin n → ℝ) → Prop) =>
    ((fun N K L d S η W ω ν E P B f g G => (∀ k, 2 ≤ N k) ∧ Filter.Tendsto N Filter.atTop Filter.atTop ∧ ((∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε) ∧ 0 < L ∧ 0 < d ∧ d < 1 ∧ 0 < S ∧ 0 < η ∧ (fun μ : (k : ℕ) → Fin (W k) → MeasureTheory.Measure ((ℕ × (Fin 6 → ℝ)) × ℝ) => (∃ M D : ℕ, ∀ k, (W k : ℝ) ≤ N k ^ M ∧ (∀ γ, 0 ≤ ω k γ) ∧ (∑ γ, ω k γ) = 1 ∧ (∀ γ, MeasureTheory.IsProbabilityMeasure (ν k γ) ∧ 0 < B k γ ∧ B k γ ≤ N k ^ M ∧ (B k γ)⁻¹ ≤ N k ^ M ∧ (P k γ).totalDegree ≤ 2 ∧ (∀ b, |(P k γ).coeff b| ≤ N k ^ M) ∧ (∃ m : ℕ, (m : ℝ) ≤ N k ^ M ∧ ∃ (c : Fin m → ℝ) (i : Fin m → ℕ) (A : Fin m → Set (Fin 6 → ℝ)), (∀ j, 0 ≤ c j ∧ c j ≤ N k ^ M ∧ (i j : ℝ) ≤ N k ^ M ∧ (fmt 6 (N k ^ M) D (A j)) ∧ (∀ x ∈ A j, ∀ b, |x b| ≤ N k ^ M)) ∧ ν k γ = ∑ j, (ENNReal.ofReal (c j)) • MeasureTheory.Measure.map (fun x => (i j, x)) (MeasureTheory.volume.restrict (A j))) ∧ MeasurableSet (E k γ) ∧ E k γ ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 ∧ (∀ p ∈ E k γ, (p.1.1 : ℝ) ≤ N k ^ M ∧ ∀ e, |p.1.2 e| ≤ N k ^ M) ∧ (∀ i, (fmt 7 (N k ^ M) D ({x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ (E k γ)}))) ∧ (∀ᵐ l ∂ν k γ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(y l t)‖ + ‖(v l)‖ ≤ K k ∧ |MvPolynomial.eval (x l t) (P k γ)| ≤ K k ∧ |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (P k γ))| ≤ K k * B k γ ∧ |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (P k γ)))| ≤ K k * (B k γ) ^ 2) ∧ (∀ᵐ p ∂(μ k γ), B k γ / K k ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (P k γ))|)) ∧ ENNReal.ofReal ((K k)⁻¹) ≤ ∑ γ, ENNReal.ofReal (ω k γ) * (μ k γ) Set.univ) ∧ (∀ k γ r, 0 ≤ r → r ≤ L → Measurable (g k γ r) ∧ MeasureTheory.Measure.map (obs (B k γ) (δ (N k) r)) (μ k γ) = (MeasureTheory.volume.prod MeasureTheory.Measure.count).withDensity (g k γ r)) ∧ (∀ k γ u, 0 < u → u ≤ η * L → Measurable (G k γ u) ∧ MeasureTheory.Measure.map (fun p : ((ℕ × (Fin 6 → ℝ)) × ℝ) => ((obs (B k γ) (δ (N k) L)) p, fun j : Fin 2 => ⌊(v p.1) j / (δ (N k) u)⌋)) (μ k γ) = ((MeasureTheory.volume.prod MeasureTheory.Measure.count).prod MeasureTheory.Measure.count).withDensity (G k γ u)) ∧ (∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ L → 0 ≤ f s - f r ∧ f s - f r ≤ s - r) ∧ (∀ r τ : ℝ, 0 ≤ r → r ≤ L → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop, (∑ γ, ENNReal.ofReal (ω k γ) * (μ k γ) {p | g k γ r ((obs (B k γ) (δ (N k) r)) p) < ENNReal.ofReal (N k ^ (-f r - τ)) ∨ ENNReal.ofReal (N k ^ (-f r + τ)) < g k γ r ((obs (B k γ) (δ (N k) r)) p)}) ≤ ENNReal.ofReal (N k ^ (-c))) ∧ (∀ r : ℝ, 0 ≤ r → r ≤ L → f L - f r ≤ d * (L - r)) ∧ (∀ u τ : ℝ, 0 < u → u ≤ η * L → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop, (∑ γ, ENNReal.ofReal (ω k γ) * (μ k γ) {p | ENNReal.ofReal (N k ^ (-f L - S * u + τ)) < G k γ u ((fun p : ((ℕ × (Fin 6 → ℝ)) × ℝ) => ((obs (B k γ) (δ (N k) L)) p, fun j : Fin 2 => ⌊(v p.1) j / (δ (N k) u)⌋)) p)}) ≤ ENNReal.ofReal (N k ^ (-c)))) (fun k γ => ((ν k γ).prod MeasureTheory.volume).restrict (E k γ))) : (ℕ → ℝ) → (ℕ → ℝ) → ℝ → ℝ → ℝ → ℝ → (W : ℕ → ℕ) → ((k : ℕ) → Fin (W k) → ℝ) → ((k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) → ((k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) → ((k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ) → ((k : ℕ) → Fin (W k) → ℝ) → (ℝ → ℝ) → ((k : ℕ) → Fin (W k) → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal) → ((k : ℕ) → Fin (W k) → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal) → Prop)) xl yl vl dl obsl Fmt

/-- The chart predicate. -/
abbrev Chart := Submission.Obl.k4_quadratic_atlas_normalization.chart

/-- The frozen statement with named abbreviations. -/
def HorizonStatement : Prop :=
  (∀ N K L d S η W ω ν E P B f g G, Prob N K L d S η W ω ν E P B f g G → ∀ h : ℝ, L < h → ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop, ∃ κ : ℝ, 1 ≤ κ ∧ K k ≤ κ ∧ κ ≤ N k ^ ε ∧ ∃ T C' : ℕ, ∃ (γ : Fin (C') → Fin (W k)) (j : Fin (C') → Fin (2 ^ T)) (c u : Fin (C') → EuclideanSpace ℝ (Fin 2)) (Q : Fin (C') → Matrix (Fin 2) (Fin 2) ℝ) (R : Fin (C') → MvPolynomial (Fin 4) ℝ) (A : Fin (C') → Set (ℕ × (Fin 6 → ℝ))) (F : Fin (C') → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)), (2 : ℝ) ^ T ≤ N k ^ h ∧ (C' : ℝ) ≤ N k ^ M ∧ (∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b')) ∧ (∀ b, Chart (N k) M D κ T ((j b : ℕ) : ℝ) L (B k (γ b)) (E k (γ b)) (c b) (u b) (Q b) (R b) (A b) (F b) (ENNReal.ofReal (N k ^ (-f L) * |Matrix.det (Q b)| / ((2 : ℝ) ^ T * κ)) ≤ (((ν k (γ b)).prod MeasureTheory.volume) (F b)))) ∧ ENNReal.ofReal ((κ)⁻¹) ≤ ∑ b, ENNReal.ofReal (ω k (γ b)) * (((ν k (γ b)).prod MeasureTheory.volume) (F b)))

/-- The supplied per-group plank selection hypothesis. -/
def GreedyKernel : Prop :=
  (∀ ε : ℝ, 0 < ε → ∃ η C : ℝ, 0 < η ∧ 0 < C ∧ ∀ D : ℕ, 2 ≤ D → ∀ (α : Type) [MeasurableSpace α] (ν : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure ν] (b u : α → EuclideanSpace ℝ (Fin 2)), Measurable b → Measurable u → ∀ U : Set α, MeasurableSet U → (∀ z ∈ U, ‖b z‖ ≤ 1 ∧ ‖u z‖ ≤ 1) → ((fun fit : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → ℝ → ℝ → α → Prop => ∀ E Gd : Set (α × ℝ), MeasurableSet E → MeasurableSet Gd → E ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 → ∀ τ₀ s : ℝ, 0 < τ₀ → (D : ℝ) ^ (-η) ≤ s → ∀ F : Finset (ℤ × (Fin 2 → ℤ)), (∀ p ∈ E ∩ Gd, p.1 ∈ U → (⌊p.2 * (D : ℝ)⌋, fun k : Fin 2 => ⌊(D : ℝ) * (b p.1 + p.2 • u p.1) k⌋) ∈ F) → ∃ (m : ℕ) (c w e₁ e₂ : Fin m → EuclideanSpace ℝ (Fin 2)) (a β : Fin m → ℝ), (∀ i, ‖e₁ i‖ = 1 ∧ ‖e₂ i‖ = 1 ∧ inner ℝ (e₁ i) (e₂ i) = 0 ∧ 2 / (D : ℝ) ≤ a i ∧ a i ≤ β i ∧ β i ≤ 2) ∧ (∀ i, ENNReal.ofReal (τ₀ * a i * β i) ≤ (ν.prod MeasureTheory.volume) (E ∩ ({z | z ∈ U ∧ fit (c i) (w i) (e₁ i) (e₂ i) (a i) (β i) z ∧ ∀ j : Fin m, j < i → ¬ fit (c j) (w j) (e₁ j) (e₂ j) (a j) (β j) z} ×ˢ Set.univ))) ∧ (ν.prod MeasureTheory.volume) (E ∩ ({z | z ∈ U ∧ ∀ i, ¬ fit (c i) (w i) (e₁ i) (e₂ i) (a i) (β i) z} ×ˢ Set.univ)) ≤ (ν.prod MeasureTheory.volume) (E ∩ Gdᶜ ∩ ({z | z ∈ U ∧ ∀ i, ¬ fit (c i) (w i) (e₁ i) (e₂ i) (a i) (β i) z} ×ˢ Set.univ)) + ENNReal.ofReal s * ν {z | z ∈ U ∧ ∀ i, ¬ fit (c i) (w i) (e₁ i) (e₂ i) (a i) (β i) z} + ENNReal.ofReal (C * τ₀ * (D : ℝ) ^ ε / (s * (D : ℝ) ^ 3) * (F.card : ℝ))) (fun c w e₁ e₂ a β z => ∀ t ∈ Set.Icc (0 : ℝ) 1, |inner ℝ (b z + t • u z - c - t • w) e₁| ≤ a ∧ |inner ℝ (b z + t • u z - c - t • w) e₂| ≤ β)))

/-- The supplied light original-cell estimate. -/
def LightCells : Prop :=
  (∀ N K L d S η W ω ν E P B f g G, Prob N K L d S η W ω ν E P B f g G → ∃ H₀ : ℝ, ∀ τ : ℝ, 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop, ∀ ρ₁ ρ₂ : ℝ, 0 < ρ₁ → ρ₁ ≤ N k ^ (-H₀) → 0 < ρ₂ → ρ₂ ≤ N k ^ (-H₀) → (∑ γ, ENNReal.ofReal (ω k γ) * ((ν k γ).prod MeasureTheory.volume) {p | p ∈ E k γ ∧ ((ν k γ).prod MeasureTheory.volume) {p' | p' ∈ E k γ ∧ ⌊p'.2 / ρ₁⌋ = ⌊p.2 / ρ₁⌋ ∧ ⌊(xl p'.1 p'.2) 1 / ρ₂⌋ = ⌊(xl p.1 p.2) 1 / ρ₂⌋ ∧ ⌊(xl p'.1 p'.2) 2 / ρ₂⌋ = ⌊(xl p.1 p.2) 2 / ρ₂⌋ ∧ (obsl (B k γ) (dl (N k) L) p').2 = (obsl (B k γ) (dl (N k) L) p).2} < ENNReal.ofReal (N k ^ (-f L - τ) * ρ₁ * ρ₂ ^ 2)}) ≤ ENNReal.ofReal (N k ^ (-c)))

end

end Submission.Obl.k4_horizon_chart_assembly
