import Mathlib
import ChallengeDeps
import Submission.Obl.k4_scalar_grid_parameter_preparation
import Submission.Obl.k4_scalar_grid_polynomial_qualification
import Submission.Obl.k4_scalar_grid_cartesian_field
import Submission.Obl.k4_scalar_capped_heavy_potential
import Submission.Obl.k4_scalar_tangent_isotropic_improvement.SplitStatements
import Submission.Obl.k4_scalar_tangent_isotropic_improvement.HeavyPotentialRecovery
import Submission.Obl.k4_scalar_tangent_isotropic_improvement.VelocityGraph
set_option linter.unusedVariables false

/-!
# `Submission.k4_scalar_tangent_isotropic_improvement`

Glue of the split of o092. The six stages are the scalar case of Section 6 of the supplied
paper:
1. physical and parameter preparation on a finite exponent grid (child);
2. the physical velocity graph (proved: `VelocityGraph.lean`, x0320);
3. polynomial qualification (child);
4. Cartesian interpolation of the field (child);
5. a conservative potential with a heavy intercept group (child);
6. quadratic recovery (proved: `HeavyPotentialRecovery.lean`, x0317).

`SplitStatements.lean` states the stages as propositions and composes them (`of_children`).
-/

theorem Submission.k4_scalar_tangent_isotropic_improvement : (∀ n : ℕ, 2 ≤ n → n ≤ 4 → ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → ∀ (N : Fin n → ℕ) (a e : (i : Fin n) → Fin (N i) → EuclideanSpace ℝ (Fin n)) (w : (i : Fin n) → Fin (N i) → ℝ), (∀ (i : Fin n) (k : Fin (N i)), ‖e i k‖ = 1) → (∀ (i : Fin n) (k : Fin (N i)), 0 ≤ w i k) → MeasureTheory.lintegral MeasureTheory.volume (fun x : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal ((∑ T : ((i : Fin n) → Fin (N i)), |Matrix.det (Matrix.of fun i j : Fin n => e i (T i) j)| * ∏ i : Fin n, (w i (T i) * (Metric.thickening r (Set.range fun t : ℝ => a i (T i) + t • e i (T i))).indicator (fun _ => (1 : ℝ)) x)) ^ ((1 : ℝ) / ((n : ℝ) - 1)))) ≤ ENNReal.ofReal (C * r ^ n * ∏ i : Fin n, (∑ k : Fin (N i), w i k) ^ ((1 : ℝ) / ((n : ℝ) - 1)))) → (∀ (N K : ℕ → ℝ), (∀ k, 2 ≤ N k) → Filter.Tendsto N Filter.atTop Filter.atTop → ((∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε) → ∀ d κ S : ℝ, 0 ≤ d → d < 1 → 0 < κ → κ ≤ 1 → 0 < S → ∀ (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 5 → ℝ))) (ρ : (k : ℕ) → Fin (W k) → MeasureTheory.Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) (π : (k : ℕ) → Fin (W k) → MeasureTheory.Measure ℝ) (T n : ℕ → ℝ → ℕ) (γ : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (W k)) (j : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (2 ^ T k s)) (A : (k : ℕ) → (s : ℝ) → Fin (n k s) → Set (ℕ × (Fin 5 → ℝ))) (u v : (k : ℕ) → (s : ℝ) → Fin (n k s) → ℝ) (F : (k : ℕ) → (s : ℝ) → Fin (n k s) → MvPolynomial (Fin 2) ℝ), (fun (y x : (ℕ × (Fin 5 → ℝ)) → ℝ → ℝ) (I : (T : ℕ) → Fin (2 ^ T) → Set ℝ) => (fun z : ℝ → ℝ → ((ℕ × (Fin 5 → ℝ)) × ℝ) → Fin 2 → ℤ => (∀ k, (∀ g, 0 ≤ ω k g) ∧ (∑ g, ω k g) = 1 ∧ (∀ g, MeasureTheory.IsProbabilityMeasure (ν k g) ∧ MeasureTheory.IsProbabilityMeasure (π k g) ∧ (∀ᵐ l ∂ν k g, ∀ e, |l.2 e| ≤ K k) ∧ ρ k g ≤ ENNReal.ofReal (K k) • ((ν k g).prod MeasureTheory.volume) ∧ ρ k g (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0) ∧ ENNReal.ofReal ((K k)⁻¹) ≤ ∑ g, ENNReal.ofReal (ω k g) * ρ k g Set.univ) → (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ (g : Fin (W k)) (r s b : ℝ), R⁻¹ ≤ r → r ≤ R → R⁻¹ ≤ s → s ≤ R → R⁻¹ ≤ b → b ≤ R → (∀ c : ℤ, π k g {v : ℝ | (⌊v / (N k ^ (-b))⌋ : ℤ) = c} ≤ ENNReal.ofReal (K k * N k ^ (-S * b))) ∧ (∀ (q : Fin 2 → ℤ) (a : ℤ), ρ k g {p | z (N k) r p = q ∧ (⌊x p.1 p.2 / (N k ^ (-s))⌋ : ℤ) = a} ≤ ENNReal.ofReal (K k * N k ^ (-2 * r - d * s))) ∧ (∀ (q : Fin 2 → ℤ) (a c : ℤ), ρ k g {p | z (N k) r p = q ∧ (⌊x p.1 p.2 / (N k ^ (-s))⌋ : ℤ) = a ∧ (⌊p.1.2 1 / (N k ^ (-b))⌋ : ℤ) = c} ≤ ENNReal.ofReal (K k * N k ^ (-2 * r - d * s)) * π k g {v : ℝ | (⌊v / (N k ^ (-b))⌋ : ℤ) = c})) → (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ s : ℝ, R⁻¹ ≤ s → s ≤ R → N k ^ (κ * s) / K k ≤ (2 : ℝ) ^ T k s ∧ (2 : ℝ) ^ T k s ≤ K k * N k ^ (κ * s) ∧ (∀ i, MeasurableSet (A k s i)) ∧ (∀ i i', i ≠ i' → γ k s i = γ k s i' → j k s i = j k s i' → Disjoint (A k s i) (A k s i')) ∧ (∀ i, ENNReal.ofReal (N k ^ (-d * s) / (K k * (2 : ℝ) ^ T k s)) ≤ ν k (γ k s i) (A k s i) ∧ ν k (γ k s i) (A k s i) ≤ ENNReal.ofReal (K k * N k ^ (-d * s) / (2 : ℝ) ^ T k s) ∧ ENNReal.ofReal ((K k * (2 : ℝ) ^ T k s)⁻¹) * ν k (γ k s i) (A k s i) ≤ ρ k (γ k s i) (A k s i ×ˢ I (T k s) (j k s i)) ∧ |u k s i| + |v k s i| ≤ K k ∧ (F k s i).totalDegree ≤ 2 ∧ (∀ t ∈ I (T k s) (j k s i), ∀ w ∈ Set.Icc (-2 : ℝ) 2, |MvPolynomial.eval ![t, u k s i + t * v k s i + w / (2 : ℝ) ^ T k s] (F k s i)| ≤ K k) ∧ (∀ l ∈ A k s i, ∀ t ∈ I (T k s) (j k s i), |y l t - u k s i - t * v k s i| ≤ K k / (2 : ℝ) ^ T k s ∧ |x l t - MvPolynomial.eval ![t, y l t] (F k s i)| ≤ K k * N k ^ (-s))) ∧ (∀ g : Fin (W k), ρ k g {p | ∃ i, γ k s i = g ∧ p.1 ∈ A k s i ∧ p.2 ∈ I (T k s) (j k s i)}ᶜ = 0)) → ∃ R : ℝ, 1 < R ∧ ∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop, ∃ (s c : ℝ) (i : Fin (n k s)) (P : MvPolynomial (Fin 2) ℝ), R⁻¹ ≤ s ∧ s ≤ R ∧ R⁻¹ ≤ c ∧ c ≤ R ∧ P.totalDegree ≤ 2 ∧ (∀ b, |P.coeff b| ≤ N k ^ R) ∧ ENNReal.ofReal (N k ^ (-d * c - ε) / (2 : ℝ) ^ T k s) * ν k (γ k s i) (A k s i) ≤ ρ k (γ k s i) {p | p.1 ∈ A k s i ∧ p.2 ∈ I (T k s) (j k s i) ∧ ∀ t ∈ I (T k s) (j k s i), |x p.1 t - MvPolynomial.eval ![t, y p.1 t] P| ≤ N k ^ ε * N k ^ (-s - c)}) (fun B r p e => ⌊(![p.2, y p.1 p.2] : Fin 2 → ℝ) e / (B ^ (-r))⌋)) (fun l t => l.2 0 + t * l.2 1) (fun l t => l.2 2 + t * l.2 3 + t ^ 2 * l.2 4) (fun T j => Set.Icc (((j : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T))) :=
  Submission.Obl.k4_scalar_tangent_isotropic_improvement.of_children
    Submission.k4_scalar_grid_parameter_preparation
    Submission.Obl.k4_scalar_tangent_isotropic_improvement.repaired_velocity_graph
    Submission.k4_scalar_grid_polynomial_qualification
    Submission.k4_scalar_grid_cartesian_field
    Submission.k4_scalar_capped_heavy_potential
    Submission.Obl.k4_scalar_tangent_isotropic_improvement.heavy_potential_quadratic_recovery
