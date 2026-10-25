import Mathlib

/-!
# Shared definitions for o093 (`k4_scalar_critical_path_terminal`)

The three hypotheses of the frozen statement (multilinear Kakeya, two-color
matching, scalar tangent improvement) and its conclusion are recorded verbatim
as `MKStatement`, `TCMStatement`, `STIStatement` and `ExactConclusion`.

`Data` bundles one version-1 exact sequence (the data quantified in the
conclusion); `Data.Exact` is the conjunction of its hypotheses and
`Data.Concl` the frozen conclusion (arbitrarily small-horizon true terminal
systems).  `exactConclusion_of` shows that `∀ ed, ed.Exact → ed.Concl` is the
frozen conclusion, so later work can use these names.
-/

namespace Submission.Obl.k4_scalar_critical_path_terminal

open MeasureTheory Filter

/-- Multilinear Kakeya (first hypothesis of the frozen statement, verbatim). -/
def MKStatement : Prop :=
  (∀ n : ℕ, 2 ≤ n → n ≤ 4 → ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → ∀ (N : Fin n → ℕ) (a e : (i : Fin n) → Fin (N i) → EuclideanSpace ℝ (Fin n)) (w : (i : Fin n) → Fin (N i) → ℝ), (∀ (i : Fin n) (k : Fin (N i)), ‖e i k‖ = 1) → (∀ (i : Fin n) (k : Fin (N i)), 0 ≤ w i k) → MeasureTheory.lintegral MeasureTheory.volume (fun x : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal ((∑ T : ((i : Fin n) → Fin (N i)), |Matrix.det (Matrix.of fun i j : Fin n => e i (T i) j)| * ∏ i : Fin n, (w i (T i) * (Metric.thickening r (Set.range fun t : ℝ => a i (T i) + t • e i (T i))).indicator (fun _ => (1 : ℝ)) x)) ^ ((1 : ℝ) / ((n : ℝ) - 1)))) ≤ ENNReal.ofReal (C * r ^ n * ∏ i : Fin n, (∑ k : Fin (N i), w i k) ^ ((1 : ℝ) / ((n : ℝ) - 1))))

/-- Two-color matching (second hypothesis of the frozen statement, verbatim). -/
def TCMStatement : Prop :=
  (∀ (D J : ℕ), 1 ≤ D → D < J → ∀ d : ℝ, 0 ≤ d → d < 1 → ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ (n₁ n₂ : ℕ) (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ) (π₁ : Fin n₁ → ℝ) (π₂ : Fin n₂ → ℝ) (μ : MeasureTheory.Measure ((Fin n₁ × Fin n₂) × ℝ)), (n₁ : ℝ) ≤ N ^ (d + η) → (n₂ : ℝ) ≤ N ^ (d + η) → (∀ i : Fin n₁, ContDiffOn ℝ (J + 1) (f₁ i) (Set.Ioo (-1 : ℝ) 2)) → (∀ i : Fin n₂, ContDiffOn ℝ (J + 1) (f₂ i) (Set.Ioo (-1 : ℝ) 2)) → (∀ (i : Fin n₁) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv j (f₁ i) t| ≤ N ^ η) → (∀ (i : Fin n₂) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv j (f₂ i) t| ≤ N ^ η) → (∀ i : Fin n₁, 0 ≤ π₁ i) → (∀ i : Fin n₂, 0 ≤ π₂ i) → (∑ i : Fin n₁, π₁ i) = 1 → (∑ i : Fin n₂, π₂ i) = 1 → MeasureTheory.IsProbabilityMeasure μ → (∀ (i : Fin n₁) (E : Set ℝ), MeasurableSet E → μ {p | p.1.1 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ η * π₁ i) * MeasureTheory.volume E) → (∀ (i : Fin n₂) (E : Set ℝ), MeasurableSet E → μ {p | p.1.2 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ η * π₂ i) * MeasureTheory.volume E) → ¬ μ {p | p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ |f₁ p.1.1 p.2 - f₂ p.1.2 p.2| ≤ N ^ (-1 + η) ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ D ∧ N ^ (-η) ≤ |iteratedDeriv j (f₁ p.1.1) p.2 - iteratedDeriv j (f₂ p.1.2) p.2|}ᶜ = 0)

/-- Scalar tangent improvement (third hypothesis of the frozen statement,
verbatim; this is the conclusion of o092). -/
def STIStatement : Prop :=
  (∀ (N K : ℕ → ℝ), (∀ k, 2 ≤ N k) → Filter.Tendsto N Filter.atTop Filter.atTop → ((∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε) → ∀ d κ S : ℝ, 0 ≤ d → d < 1 → 0 < κ → κ ≤ 1 → 0 < S → ∀ (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 5 → ℝ))) (ρ : (k : ℕ) → Fin (W k) → MeasureTheory.Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) (π : (k : ℕ) → Fin (W k) → MeasureTheory.Measure ℝ) (T n : ℕ → ℝ → ℕ) (γ : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (W k)) (j : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (2 ^ T k s)) (A : (k : ℕ) → (s : ℝ) → Fin (n k s) → Set (ℕ × (Fin 5 → ℝ))) (u v : (k : ℕ) → (s : ℝ) → Fin (n k s) → ℝ) (F : (k : ℕ) → (s : ℝ) → Fin (n k s) → MvPolynomial (Fin 2) ℝ), (fun (y x : (ℕ × (Fin 5 → ℝ)) → ℝ → ℝ) (I : (T : ℕ) → Fin (2 ^ T) → Set ℝ) => (fun z : ℝ → ℝ → ((ℕ × (Fin 5 → ℝ)) × ℝ) → Fin 2 → ℤ => (∀ k, (∀ g, 0 ≤ ω k g) ∧ (∑ g, ω k g) = 1 ∧ (∀ g, MeasureTheory.IsProbabilityMeasure (ν k g) ∧ MeasureTheory.IsProbabilityMeasure (π k g) ∧ (∀ᵐ l ∂ν k g, ∀ e, |l.2 e| ≤ K k) ∧ ρ k g ≤ ENNReal.ofReal (K k) • ((ν k g).prod MeasureTheory.volume) ∧ ρ k g (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0) ∧ ENNReal.ofReal ((K k)⁻¹) ≤ ∑ g, ENNReal.ofReal (ω k g) * ρ k g Set.univ) → (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ (g : Fin (W k)) (r s b : ℝ), R⁻¹ ≤ r → r ≤ R → R⁻¹ ≤ s → s ≤ R → R⁻¹ ≤ b → b ≤ R → (∀ c : ℤ, π k g {v : ℝ | (⌊v / (N k ^ (-b))⌋ : ℤ) = c} ≤ ENNReal.ofReal (K k * N k ^ (-S * b))) ∧ (∀ (q : Fin 2 → ℤ) (a : ℤ), ρ k g {p | z (N k) r p = q ∧ (⌊x p.1 p.2 / (N k ^ (-s))⌋ : ℤ) = a} ≤ ENNReal.ofReal (K k * N k ^ (-2 * r - d * s))) ∧ (∀ (q : Fin 2 → ℤ) (a c : ℤ), ρ k g {p | z (N k) r p = q ∧ (⌊x p.1 p.2 / (N k ^ (-s))⌋ : ℤ) = a ∧ (⌊p.1.2 1 / (N k ^ (-b))⌋ : ℤ) = c} ≤ ENNReal.ofReal (K k * N k ^ (-2 * r - d * s)) * π k g {v : ℝ | (⌊v / (N k ^ (-b))⌋ : ℤ) = c})) → (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ s : ℝ, R⁻¹ ≤ s → s ≤ R → N k ^ (κ * s) / K k ≤ (2 : ℝ) ^ T k s ∧ (2 : ℝ) ^ T k s ≤ K k * N k ^ (κ * s) ∧ (∀ i, MeasurableSet (A k s i)) ∧ (∀ i i', i ≠ i' → γ k s i = γ k s i' → j k s i = j k s i' → Disjoint (A k s i) (A k s i')) ∧ (∀ i, ENNReal.ofReal (N k ^ (-d * s) / (K k * (2 : ℝ) ^ T k s)) ≤ ν k (γ k s i) (A k s i) ∧ ν k (γ k s i) (A k s i) ≤ ENNReal.ofReal (K k * N k ^ (-d * s) / (2 : ℝ) ^ T k s) ∧ ENNReal.ofReal ((K k * (2 : ℝ) ^ T k s)⁻¹) * ν k (γ k s i) (A k s i) ≤ ρ k (γ k s i) (A k s i ×ˢ I (T k s) (j k s i)) ∧ |u k s i| + |v k s i| ≤ K k ∧ (F k s i).totalDegree ≤ 2 ∧ (∀ t ∈ I (T k s) (j k s i), ∀ w ∈ Set.Icc (-2 : ℝ) 2, |MvPolynomial.eval ![t, u k s i + t * v k s i + w / (2 : ℝ) ^ T k s] (F k s i)| ≤ K k) ∧ (∀ l ∈ A k s i, ∀ t ∈ I (T k s) (j k s i), |y l t - u k s i - t * v k s i| ≤ K k / (2 : ℝ) ^ T k s ∧ |x l t - MvPolynomial.eval ![t, y l t] (F k s i)| ≤ K k * N k ^ (-s))) ∧ (∀ g : Fin (W k), ρ k g {p | ∃ i, γ k s i = g ∧ p.1 ∈ A k s i ∧ p.2 ∈ I (T k s) (j k s i)}ᶜ = 0)) → ∃ R : ℝ, 1 < R ∧ ∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop, ∃ (s c : ℝ) (i : Fin (n k s)) (P : MvPolynomial (Fin 2) ℝ), R⁻¹ ≤ s ∧ s ≤ R ∧ R⁻¹ ≤ c ∧ c ≤ R ∧ P.totalDegree ≤ 2 ∧ (∀ b, |P.coeff b| ≤ N k ^ R) ∧ ENNReal.ofReal (N k ^ (-d * c - ε) / (2 : ℝ) ^ T k s) * ν k (γ k s i) (A k s i) ≤ ρ k (γ k s i) {p | p.1 ∈ A k s i ∧ p.2 ∈ I (T k s) (j k s i) ∧ ∀ t ∈ I (T k s) (j k s i), |x p.1 t - MvPolynomial.eval ![t, y p.1 t] P| ≤ N k ^ ε * N k ^ (-s - c)}) (fun B r p e => ⌊(![p.2, y p.1 p.2] : Fin 2 → ℝ) e / (B ^ (-r))⌋)) (fun l t => l.2 0 + t * l.2 1) (fun l t => l.2 2 + t * l.2 3 + t ^ 2 * l.2 4) (fun T j => Set.Icc (((j : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T)))

/-- The conclusion of the frozen statement, verbatim. -/
def ExactConclusion : Prop :=
  (∀ (N K : ℕ → ℝ), (∀ k, 2 ≤ N k) → Filter.Tendsto N Filter.atTop Filter.atTop → ((∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε) → ∀ (M D : ℕ) (L d S U : ℝ), 1 ≤ M → 1 ≤ D → 0 < L → 0 ≤ d → d < 1 → 0 < S → 0 < U → ∀ (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 5 → ℝ))) (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) (g : (k : ℕ) → Fin (W k) → ℝ → ((Fin 2 → ℝ) × ℤ) → ENNReal) (G : (k : ℕ) → Fin (W k) → ℝ → (((Fin 2 → ℝ) × ℤ) × ℤ) → ENNReal) (f : ℝ → ℝ), (fun (y x : (ℕ × (Fin 5 → ℝ)) → ℝ → ℝ) (μ : (k : ℕ) → Fin (W k) → MeasureTheory.Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) (fmt : (n : ℕ) → ℝ → ℕ → Set (Fin n → ℝ) → Prop) => (∀ k, (W k : ℝ) ≤ N k ^ (M : ℝ) ∧ (∀ γ, 0 ≤ ω k γ) ∧ (∑ γ, ω k γ) = 1 ∧ (∀ γ, MeasureTheory.IsProbabilityMeasure (ν k γ) ∧ (∃ n : ℕ, (n : ℝ) ≤ N k ^ (M : ℝ) ∧ ∃ (h : Fin n → ℝ) (i : Fin n → ℕ) (B : Fin n → Set (Fin 5 → ℝ)), (∀ j, 0 ≤ h j ∧ h j ≤ N k ^ (M : ℝ) ∧ (i j : ℝ) ≤ N k ^ (M : ℝ) ∧ fmt 5 (N k ^ (M : ℝ)) D (B j) ∧ (∀ b ∈ B j, ∀ e, |b e| ≤ N k ^ (M : ℝ))) ∧ ν k γ = ∑ j, ENNReal.ofReal (h j) • MeasureTheory.Measure.map (fun b => (i j, b)) (MeasureTheory.volume.restrict (B j))) ∧ (∀ᵐ l ∂ν k γ, ∀ e, |l.2 e| ≤ K k) ∧ MeasurableSet (E k γ) ∧ E k γ ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 ∧ (∀ p ∈ E k γ, (p.1.1 : ℝ) ≤ N k ^ (M : ℝ)) ∧ (∀ i : ℕ, fmt 6 (N k ^ (M : ℝ)) D {b : Fin 6 → ℝ | ((i, fun e : Fin 5 => b e.castSucc), b 5) ∈ E k γ})) ∧ ENNReal.ofReal ((K k)⁻¹) ≤ ∑ γ, ENNReal.ofReal (ω k γ) * μ k γ Set.univ) → (∀ k γ r, 0 ≤ r → r ≤ L → Measurable (g k γ r) ∧ MeasureTheory.Measure.map (fun p => ((![p.2, y p.1 p.2] : Fin 2 → ℝ), (⌊x p.1 p.2 / (N k ^ (-r))⌋ : ℤ))) (μ k γ) = (MeasureTheory.volume.prod MeasureTheory.Measure.count).withDensity (g k γ r)) → (∀ k γ u, 0 < u → u ≤ U → Measurable (G k γ u) ∧ MeasureTheory.Measure.map (fun p => (((![p.2, y p.1 p.2] : Fin 2 → ℝ), (⌊x p.1 p.2 / (N k ^ (-L))⌋ : ℤ)), (⌊p.1.2 1 / (N k ^ (-u))⌋ : ℤ))) (μ k γ) = ((MeasureTheory.volume.prod MeasureTheory.Measure.count).prod MeasureTheory.Measure.count).withDensity (G k γ u)) → (∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ L → 0 ≤ f s - f r ∧ f s - f r ≤ s - r) → (∀ r τ : ℝ, 0 ≤ r → r ≤ L → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop, (∑ γ, ENNReal.ofReal (ω k γ) * μ k γ {p | g k γ r ((![p.2, y p.1 p.2] : Fin 2 → ℝ), (⌊x p.1 p.2 / (N k ^ (-r))⌋ : ℤ)) < ENNReal.ofReal (N k ^ (-f r - τ)) ∨ ENNReal.ofReal (N k ^ (-f r + τ)) < g k γ r ((![p.2, y p.1 p.2] : Fin 2 → ℝ), (⌊x p.1 p.2 / (N k ^ (-r))⌋ : ℤ))}) ≤ ENNReal.ofReal (N k ^ (-c))) → (∀ r : ℝ, 0 ≤ r → r ≤ L → f L - f r ≤ d * (L - r)) → (∀ u τ : ℝ, 0 < u → u ≤ U → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop, (∑ γ, ENNReal.ofReal (ω k γ) * μ k γ {p | ENNReal.ofReal (N k ^ (-f L - S * u + τ)) < G k γ u (((![p.2, y p.1 p.2] : Fin 2 → ℝ), (⌊x p.1 p.2 / (N k ^ (-L))⌋ : ℤ)), (⌊p.1.2 1 / (N k ^ (-u))⌋ : ℤ))}) ≤ ENNReal.ofReal (N k ^ (-c))) → ((fun I : (T : ℕ) → Fin (2 ^ T) → Set ℝ => ∀ h ε : ℝ, 0 < h → 0 < ε → ∃ᶠ k in Filter.atTop, ∃ (T n : ℕ) (γ : Fin n → Fin (W k)) (j : Fin n → Fin (2 ^ T)) (A : Fin n → Set (ℕ × (Fin 5 → ℝ))) (u v J : Fin n → ℝ) (P : Fin n → MvPolynomial (Fin 2) ℝ), (2 : ℝ) ^ T ≤ N k ^ h ∧ (∀ i, MeasurableSet (A i)) ∧ (∀ i i', i ≠ i' → γ i = γ i' → j i = j i' → Disjoint (A i) (A i')) ∧ (∀ i, 0 < J i ∧ J i ≤ N k ^ ε / (2 : ℝ) ^ T ∧ |u i| + |v i| ≤ N k ^ ε ∧ (P i).totalDegree ≤ 2 ∧ (∀ l ∈ A i, ∀ t ∈ I T (j i), |y l t - u i - t * v i| ≤ N k ^ ε * J i ∧ |x l t - MvPolynomial.eval ![t, y l t] (P i)| ≤ N k ^ ε * N k ^ (-L)) ∧ ENNReal.ofReal (N k ^ (-f L) * J i / (N k ^ ε * (2 : ℝ) ^ T)) ≤ μ k (γ i) (A i ×ˢ I T (j i))) ∧ ENNReal.ofReal (N k ^ (-ε)) ≤ ∑ g : Fin (W k), ENNReal.ofReal (ω k g) * μ k g {p | ∃ i, γ i = g ∧ p.1 ∈ A i ∧ p.2 ∈ I T (j i)}) (fun T j => Set.Icc (((j : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T)))) (fun l t => l.2 0 + t * l.2 1) (fun l t => l.2 2 + t * l.2 3 + t ^ 2 * l.2 4) (fun k γ => ((ν k γ).prod MeasureTheory.volume).restrict (E k γ)) (fun (n : ℕ) (B : ℝ) (D : ℕ) (A : Set (Fin n → ℝ)) => ∃ k : ℕ, (k : ℝ) ≤ B ∧ ∃ p : Fin k → MvPolynomial (Fin n) ℝ, (∀ j, (p j).totalDegree ≤ D ∧ ∀ b, |(p j).coeff b| ≤ B) ∧ ∃ S : Set (Fin k → SignType), A = {x | (fun j => SignType.sign (MvPolynomial.eval x (p j))) ∈ S}))

/-- The base coordinate `y(t) = y₀ + t V` of a version-1 trajectory. -/
def yT (l : ℕ × (Fin 5 → ℝ)) (t : ℝ) : ℝ := l.2 0 + t * l.2 1

/-- The hidden coordinate `w(t) = w₀ + w₁ t + w₂ t²` of a version-1 trajectory. -/
def xT (l : ℕ × (Fin 5 → ℝ)) (t : ℝ) : ℝ := l.2 2 + t * l.2 3 + t ^ 2 * l.2 4

/-- The closed dyadic time block `[j/2^T, (j+1)/2^T]`. -/
def blk (T : ℕ) (j : Fin (2 ^ T)) : Set ℝ :=
  Set.Icc (((j : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T)

/-- Sign-pattern semialgebraic sets with at most `B` polynomials of degree at most
`D` and coefficients at most `B`. -/
def fmt (n : ℕ) (B : ℝ) (D : ℕ) (A : Set (Fin n → ℝ)) : Prop :=
  ∃ k : ℕ, (k : ℝ) ≤ B ∧ ∃ p : Fin k → MvPolynomial (Fin n) ℝ,
    (∀ j, (p j).totalDegree ≤ D ∧ ∀ b, |(p j).coeff b| ≤ B) ∧
    ∃ S : Set (Fin k → SignType),
      A = {x | (fun j => SignType.sign (MvPolynomial.eval x (p j))) ∈ S}

/-- The data of one version-1 exact sequence, as quantified in the frozen
conclusion. -/
structure Data where
  N : ℕ → ℝ
  K : ℕ → ℝ
  M : ℕ
  D : ℕ
  L : ℝ
  d : ℝ
  S : ℝ
  U : ℝ
  W : ℕ → ℕ
  ω : (k : ℕ) → Fin (W k) → ℝ
  ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 5 → ℝ))
  E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)
  g : (k : ℕ) → Fin (W k) → ℝ → ((Fin 2 → ℝ) × ℤ) → ENNReal
  G : (k : ℕ) → Fin (W k) → ℝ → (((Fin 2 → ℝ) × ℤ) × ℤ) → ENNReal
  f : ℝ → ℝ

namespace Data

variable (ed : Data)

/-- The selected incidence measure `μ_γ = 1_{E_γ} ν_γ ⊗ dt`. -/
noncomputable def μ (k : ℕ) (γ : Fin (ed.W k)) : Measure ((ℕ × (Fin 5 → ℝ)) × ℝ) :=
  ((ed.ν k γ).prod volume).restrict (ed.E k γ)

/-- Scalar parameters and subpower factors. -/
def Params : Prop :=
  (∀ k, 2 ≤ ed.N k) ∧ Tendsto ed.N atTop atTop ∧
    ((∀ k, 1 ≤ ed.K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ed.K k ≤ ed.N k ^ ε) ∧
    1 ≤ ed.M ∧ 1 ≤ ed.D ∧ 0 < ed.L ∧ 0 ≤ ed.d ∧ ed.d < 1 ∧ 0 < ed.S ∧ 0 < ed.U

/-- Polynomially many worlds, tagged semialgebraic priors and incidence events, subpower coefficient bounds and dense selected mass. -/
def H1 : Prop :=
  (∀ k, (ed.W k : ℝ) ≤ ed.N k ^ (ed.M : ℝ) ∧ (∀ γ, 0 ≤ ed.ω k γ) ∧ (∑ γ, ed.ω k γ) = 1 ∧ (∀ γ, MeasureTheory.IsProbabilityMeasure (ed.ν k γ) ∧ (∃ n : ℕ, (n : ℝ) ≤ ed.N k ^ (ed.M : ℝ) ∧ ∃ (h : Fin n → ℝ) (i : Fin n → ℕ) (B : Fin n → Set (Fin 5 → ℝ)), (∀ j, 0 ≤ h j ∧ h j ≤ ed.N k ^ (ed.M : ℝ) ∧ (i j : ℝ) ≤ ed.N k ^ (ed.M : ℝ) ∧ fmt 5 (ed.N k ^ (ed.M : ℝ)) ed.D (B j) ∧ (∀ b ∈ B j, ∀ e, |b e| ≤ ed.N k ^ (ed.M : ℝ))) ∧ ed.ν k γ = ∑ j, ENNReal.ofReal (h j) • MeasureTheory.Measure.map (fun b => (i j, b)) (MeasureTheory.volume.restrict (B j))) ∧ (∀ᵐ l ∂ed.ν k γ, ∀ e, |l.2 e| ≤ ed.K k) ∧ MeasurableSet (ed.E k γ) ∧ ed.E k γ ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 ∧ (∀ p ∈ ed.E k γ, (p.1.1 : ℝ) ≤ ed.N k ^ (ed.M : ℝ)) ∧ (∀ i : ℕ, fmt 6 (ed.N k ^ (ed.M : ℝ)) ed.D {b : Fin 6 → ℝ | ((i, fun e : Fin 5 => b e.castSucc), b 5) ∈ ed.E k γ})) ∧ ENNReal.ofReal ((ed.K k)⁻¹) ≤ ∑ γ, ENNReal.ofReal (ed.ω k γ) * ed.μ k γ Set.univ)

/-- Exact-base observation densities `g` at hidden depth `r ∈ [0, L]`. -/
def H2 : Prop :=
  (∀ k γ r, 0 ≤ r → r ≤ ed.L → Measurable (ed.g k γ r) ∧ MeasureTheory.Measure.map (fun p => ((![p.2, yT p.1 p.2] : Fin 2 → ℝ), (⌊xT p.1 p.2 / (ed.N k ^ (-r))⌋ : ℤ))) (ed.μ k γ) = (MeasureTheory.volume.prod MeasureTheory.Measure.count).withDensity (ed.g k γ r))

/-- Terminal observation densities `G` with an appended velocity bin at depth `u ∈ (0, U]`. -/
def H3 : Prop :=
  (∀ k γ u, 0 < u → u ≤ ed.U → Measurable (ed.G k γ u) ∧ MeasureTheory.Measure.map (fun p => (((![p.2, yT p.1 p.2] : Fin 2 → ℝ), (⌊xT p.1 p.2 / (ed.N k ^ (-ed.L))⌋ : ℤ)), (⌊p.1.2 1 / (ed.N k ^ (-u))⌋ : ℤ))) (ed.μ k γ) = ((MeasureTheory.volume.prod MeasureTheory.Measure.count).prod MeasureTheory.Measure.count).withDensity (ed.G k γ u))

/-- The profile `f` is nondecreasing and `1`-Lipschitz on `[0, L]`. -/
def H4 : Prop :=
  (∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ ed.L → 0 ≤ ed.f s - ed.f r ∧ ed.f s - ed.f r ≤ s - r)

/-- Typical density `N^{-f(r)}` of the depth-`r` observation. -/
def H5 : Prop :=
  (∀ r τ : ℝ, 0 ≤ r → r ≤ ed.L → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop, (∑ γ, ENNReal.ofReal (ed.ω k γ) * ed.μ k γ {p | ed.g k γ r ((![p.2, yT p.1 p.2] : Fin 2 → ℝ), (⌊xT p.1 p.2 / (ed.N k ^ (-r))⌋ : ℤ)) < ENNReal.ofReal (ed.N k ^ (-ed.f r - τ)) ∨ ENNReal.ofReal (ed.N k ^ (-ed.f r + τ)) < ed.g k γ r ((![p.2, yT p.1 p.2] : Fin 2 → ℝ), (⌊xT p.1 p.2 / (ed.N k ^ (-r))⌋ : ℤ))}) ≤ ENNReal.ofReal (ed.N k ^ (-c)))

/-- The endpoint cap `f(L) - f(r) ≤ d (L - r)`. -/
def H6 : Prop :=
  (∀ r : ℝ, 0 ≤ r → r ≤ ed.L → ed.f ed.L - ed.f r ≤ ed.d * (ed.L - r))

/-- The angular cap: typical upper density `N^{-f(L) - S u}`. -/
def H7 : Prop :=
  (∀ u τ : ℝ, 0 < u → u ≤ ed.U → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop, (∑ γ, ENNReal.ofReal (ed.ω k γ) * ed.μ k γ {p | ENNReal.ofReal (ed.N k ^ (-ed.f ed.L - ed.S * u + τ)) < ed.G k γ u (((![p.2, yT p.1 p.2] : Fin 2 → ℝ), (⌊xT p.1 p.2 / (ed.N k ^ (-ed.L))⌋ : ℤ)), (⌊p.1.2 1 / (ed.N k ^ (-u))⌋ : ℤ))}) ≤ ENNReal.ofReal (ed.N k ^ (-c)))

/-- All hypotheses of one exact sequence. -/
def Exact : Prop :=
  ed.Params ∧ ed.H1 ∧ ed.H2 ∧ ed.H3 ∧ ed.H4 ∧ ed.H5 ∧ ed.H6 ∧ ed.H7

/-- A true terminal chart system at sample `k`, with time-length exponent `h` and
loss exponent `ε`: dyadic blocks `2^{-T} ≥ N^{-h}`, disjoint assignments per world
and block, affine centers of width `J`, whole-block quadratic residuals at the
terminal thickness, unnormalized floors `q n(L) J`, and dense total mass. -/
def SystemAt (h ε : ℝ) (k : ℕ) : Prop :=
  ∃ (T n : ℕ) (γ : Fin n → Fin (ed.W k)) (j : Fin n → Fin (2 ^ T)) (A : Fin n → Set (ℕ × (Fin 5 → ℝ))) (u v J : Fin n → ℝ) (P : Fin n → MvPolynomial (Fin 2) ℝ), (2 : ℝ) ^ T ≤ ed.N k ^ h ∧ (∀ i, MeasurableSet (A i)) ∧ (∀ i i', i ≠ i' → γ i = γ i' → j i = j i' → Disjoint (A i) (A i')) ∧ (∀ i, 0 < J i ∧ J i ≤ ed.N k ^ ε / (2 : ℝ) ^ T ∧ |u i| + |v i| ≤ ed.N k ^ ε ∧ (P i).totalDegree ≤ 2 ∧ (∀ l ∈ A i, ∀ t ∈ blk T (j i), |yT l t - u i - t * v i| ≤ ed.N k ^ ε * J i ∧ |xT l t - MvPolynomial.eval ![t, yT l t] (P i)| ≤ ed.N k ^ ε * ed.N k ^ (-ed.L)) ∧ ENNReal.ofReal (ed.N k ^ (-ed.f ed.L) * J i / (ed.N k ^ ε * (2 : ℝ) ^ T)) ≤ ed.μ k (γ i) (A i ×ˢ blk T (j i))) ∧ ENNReal.ofReal (ed.N k ^ (-ε)) ≤ ∑ g : Fin (ed.W k), ENNReal.ofReal (ed.ω k g) * ed.μ k g {p | ∃ i, γ i = g ∧ p.1 ∈ A i ∧ p.2 ∈ blk T (j i)}

/-- Arbitrarily small-horizon true terminal systems (the frozen conclusion). -/
def Concl : Prop :=
  ∀ h ε : ℝ, 0 < h → 0 < ε → ∃ᶠ k in Filter.atTop, ed.SystemAt h ε k

end Data

/-- The frozen conclusion is `∀ ed : Data, ed.Exact → ed.Concl`. -/
theorem exactConclusion_of (H : ∀ ed : Data, ed.Exact → ed.Concl) : ExactConclusion := by
  intro N K hN hNt hK M D L d S U hM hD hL hd0 hd1 hS hU W ω ν E g G f h1 h2 h3 h4 h5 h6 h7
  exact H ⟨N, K, M, D, L, d, S, U, W, ω, ν, E, g, G, f⟩
    ⟨⟨hN, hNt, hK, hM, hD, hL, hd0, hd1, hS, hU⟩, h1, h2, h3, h4, h5, h6, h7⟩

/-- Conversely, every exact sequence satisfies the frozen conclusion if it holds. -/
theorem concl_of_exactConclusion (H : ExactConclusion) (ed : Data) (hed : ed.Exact) :
    ed.Concl := by
  obtain ⟨⟨hN, hNt, hK, hM, hD, hL, hd0, hd1, hS, hU⟩, h1, h2, h3, h4, h5, h6, h7⟩ := hed
  exact H ed.N ed.K hN hNt hK ed.M ed.D ed.L ed.d ed.S ed.U hM hD hL hd0 hd1 hS hU ed.W ed.ω
    ed.ν ed.E ed.g ed.G ed.f h1 h2 h3 h4 h5 h6 h7

end Submission.Obl.k4_scalar_critical_path_terminal
