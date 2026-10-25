import Mathlib
import ChallengeDeps
import Submission.Obl.k4_profile_endpoint_crop.Glue
import Submission.Obl.k4_dyadic_crop_worlds
import Submission.Obl.k4_dyadic_crop_affine_laws
import Submission.Obl.k4_dyadic_crop_typicality
set_option linter.unusedVariables false

/-!
# `Submission.k4_profile_endpoint_crop`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_profile_endpoint_crop`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_profile_endpoint_crop/`
belong to this obligation.
-/

open Submission.Obl.k4_profile_endpoint_crop in
theorem Submission.k4_profile_endpoint_crop : ∀ (N₀ K₀ Λ₀ : ℕ → ℝ) (ν₀ : ℕ → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) (E₀ : ℕ → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (F₀ : ℝ → ℝ → ℝ) (σ : ℝ), (∀ k, 2 ≤ N₀ k) → Filter.Tendsto N₀ Filter.atTop Filter.atTop → ((∀ k, 1 ≤ K₀ k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K₀ k ≤ N₀ k ^ ε) → (∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, Λ₀ k ≤ N₀ k ^ ε) → 0 < σ → (∃ M D : ℕ, ∀ k, MeasureTheory.IsProbabilityMeasure (ν₀ k) ∧ (∃ m : ℕ, (m : ℝ) ≤ N₀ k ^ M ∧ ∃ (c : Fin m → ℝ) (i : Fin m → ℕ) (A : Fin m → Set (Fin 6 → ℝ)), (∀ j, 0 ≤ c j ∧ c j ≤ N₀ k ^ M ∧ (i j : ℝ) ≤ N₀ k ^ M ∧ (∃ m₀ : ℕ, (m₀ : ℝ) ≤ (N₀ k ^ M) ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin 6) ℝ, (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool, ∀ x₀, x₀ ∈ (A j) ↔ b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true) ∧ (∀ x ∈ A j, ∀ b, |x b| ≤ N₀ k ^ M)) ∧ ν₀ k = ∑ j, (ENNReal.ofReal (c j)) • MeasureTheory.Measure.map (fun x => (i j, x)) (MeasureTheory.volume.restrict (A j))) ∧ MeasurableSet (E₀ k) ∧ E₀ k ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 ∧ (∀ p ∈ E₀ k, (p.1.1 : ℝ) ≤ N₀ k ^ M ∧ ∀ e, |p.1.2 e| ≤ N₀ k ^ M) ∧ (∀ i, (∃ m₀ : ℕ, (m₀ : ℝ) ≤ (N₀ k ^ M) ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin 7) ℝ, (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool, ∀ x₀, x₀ ∈ ({x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ (E₀ k)}) ↔ b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true)) ∧ (∀ᵐ l ∂(ν₀ k), ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(WithLp.toLp 2 ![![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 1, ![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 2])‖ + ‖(WithLp.toLp 2 ![l.2 3, l.2 4])‖ ≤ K₀ k ∧ |![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 3| ≤ K₀ k) ∧ ENNReal.ofReal ((K₀ k)⁻¹) ≤ (((ν₀ k).prod MeasureTheory.volume).restrict (E₀ k)) Set.univ) → (∀ k (Z : Set (EuclideanSpace ℝ (Fin 3))), (ν₀ k) {l | (WithLp.toLp 2 ![l.2 3, l.2 4, l.2 5] : EuclideanSpace ℝ (Fin 3)) ∈ Z} ≤ ENNReal.ofReal (Λ₀ k) * MeasureTheory.volume Z) → ((∀ r r' u : ℝ, 0 ≤ r → r ≤ r' → r' ≤ 1 → 0 ≤ u → u ≤ 4 → 0 ≤ F₀ r' u - F₀ r u ∧ F₀ r' u - F₀ r u ≤ r' - r) ∧ (∀ r u u' : ℝ, 0 ≤ r → r ≤ 1 → 0 ≤ u → u ≤ u' → u' ≤ 4 → 0 ≤ F₀ r u' - F₀ r u ∧ F₀ r u' - F₀ r u ≤ 2 * (u' - u))) → (∀ k (r u : ℝ), 0 ≤ r → r ≤ 1 → 0 ≤ u → u ≤ 4 → ∃ G : (EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ) → ENNReal, Measurable G ∧ MeasureTheory.Measure.map (fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => (((WithLp.toLp 2 ![p.2, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 1, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 2] : EuclideanSpace ℝ (Fin 3)), ⌊![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 3 / ((2 : ℝ) ^ (-(⌊r * Real.log (N₀ k) / Real.log 2⌋ : ℤ)))⌋), fun j : Fin 2 => ⌊(WithLp.toLp 2 ![p.1.2 3, p.1.2 4]) j / ((2 : ℝ) ^ (-(⌊u * Real.log (N₀ k) / Real.log 2⌋ : ℤ)))⌋)) (((ν₀ k).prod MeasureTheory.volume).restrict (E₀ k)) = ((MeasureTheory.volume.prod MeasureTheory.Measure.count).prod MeasureTheory.Measure.count).withDensity G) → (∀ r u τ : ℝ, 0 ≤ r → r ≤ 1 → 0 ≤ u → u ≤ 4 → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop, ∀ G : (EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ) → ENNReal, Measurable G → MeasureTheory.Measure.map (fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => (((WithLp.toLp 2 ![p.2, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 1, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 2] : EuclideanSpace ℝ (Fin 3)), ⌊![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 3 / ((2 : ℝ) ^ (-(⌊r * Real.log (N₀ k) / Real.log 2⌋ : ℤ)))⌋), fun j : Fin 2 => ⌊(WithLp.toLp 2 ![p.1.2 3, p.1.2 4]) j / ((2 : ℝ) ^ (-(⌊u * Real.log (N₀ k) / Real.log 2⌋ : ℤ)))⌋)) (((ν₀ k).prod MeasureTheory.volume).restrict (E₀ k)) = ((MeasureTheory.volume.prod MeasureTheory.Measure.count).prod MeasureTheory.Measure.count).withDensity G → (((ν₀ k).prod MeasureTheory.volume).restrict (E₀ k)) {p | G ((fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => (((WithLp.toLp 2 ![p.2, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 1, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 2] : EuclideanSpace ℝ (Fin 3)), ⌊![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 3 / ((2 : ℝ) ^ (-(⌊r * Real.log (N₀ k) / Real.log 2⌋ : ℤ)))⌋), fun j : Fin 2 => ⌊(WithLp.toLp 2 ![p.1.2 3, p.1.2 4]) j / ((2 : ℝ) ^ (-(⌊u * Real.log (N₀ k) / Real.log 2⌋ : ℤ)))⌋)) p) < ENNReal.ofReal (N₀ k ^ (-F₀ r u - τ)) ∨ ENNReal.ofReal (N₀ k ^ (-F₀ r u + τ)) < G ((fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => (((WithLp.toLp 2 ![p.2, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 1, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 2] : EuclideanSpace ℝ (Fin 3)), ⌊![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 3 / ((2 : ℝ) ^ (-(⌊r * Real.log (N₀ k) / Real.log 2⌋ : ℤ)))⌋), fun j : Fin 2 => ⌊(WithLp.toLp 2 ![p.1.2 3, p.1.2 4]) j / ((2 : ℝ) ^ (-(⌊u * Real.log (N₀ k) / Real.log 2⌋ : ℤ)))⌋)) p)} ≤ ENNReal.ofReal (N₀ k ^ (-c))) → F₀ 1 0 ≤ 1 - σ → 0 ≤ F₀ 0 0 → (∀ r u : ℝ, 0 ≤ r → r ≤ 1 → 0 ≤ u → u ≤ 4 → 2 * u - 2 ≤ F₀ r u) → ∃ (N K : ℕ → ℝ) (L d S η : ℝ) (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ) (B : (k : ℕ) → Fin (W k) → ℝ) (f : ℝ → ℝ) (g : (k : ℕ) → Fin (W k) → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal) (G : (k : ℕ) → Fin (W k) → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal), (∀ k, 2 ≤ N k) ∧ Filter.Tendsto N Filter.atTop Filter.atTop ∧ ((∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε) ∧ 0 < L ∧ 0 < d ∧ d < 1 ∧ 0 < S ∧ 0 < η ∧ (∃ M D : ℕ, ∀ k, (W k : ℝ) ≤ N k ^ M ∧ (∀ γ, 0 ≤ ω k γ) ∧ (∑ γ, ω k γ) = 1 ∧ (∀ γ, MeasureTheory.IsProbabilityMeasure (ν k γ) ∧ 0 < B k γ ∧ B k γ ≤ N k ^ M ∧ (B k γ)⁻¹ ≤ N k ^ M ∧ (P k γ).totalDegree ≤ 2 ∧ (∀ b, |(P k γ).coeff b| ≤ N k ^ M) ∧ (∃ m : ℕ, (m : ℝ) ≤ N k ^ M ∧ ∃ (c : Fin m → ℝ) (i : Fin m → ℕ) (A : Fin m → Set (Fin 6 → ℝ)), (∀ j, 0 ≤ c j ∧ c j ≤ N k ^ M ∧ (i j : ℝ) ≤ N k ^ M ∧ (∃ m₀ : ℕ, (m₀ : ℝ) ≤ (N k ^ M) ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin 6) ℝ, (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool, ∀ x₀, x₀ ∈ (A j) ↔ b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true) ∧ (∀ x ∈ A j, ∀ b, |x b| ≤ N k ^ M)) ∧ ν k γ = ∑ j, (ENNReal.ofReal (c j)) • MeasureTheory.Measure.map (fun x => (i j, x)) (MeasureTheory.volume.restrict (A j))) ∧ MeasurableSet (E k γ) ∧ E k γ ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 ∧ (∀ p ∈ E k γ, (p.1.1 : ℝ) ≤ N k ^ M ∧ ∀ e, |p.1.2 e| ≤ N k ^ M) ∧ (∀ i, (∃ m₀ : ℕ, (m₀ : ℝ) ≤ (N k ^ M) ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin 7) ℝ, (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool, ∀ x₀, x₀ ∈ ({x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ (E k γ)}) ↔ b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true)) ∧ (∀ᵐ l ∂ν k γ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(WithLp.toLp 2 ![![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 1, ![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 2])‖ + ‖(WithLp.toLp 2 ![l.2 3, l.2 4])‖ ≤ K k ∧ |MvPolynomial.eval (![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5]) (P k γ)| ≤ K k ∧ |MvPolynomial.eval (![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5]) (MvPolynomial.pderiv (3 : Fin 4) (P k γ))| ≤ K k * B k γ ∧ |MvPolynomial.eval (![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5]) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (P k γ)))| ≤ K k * (B k γ) ^ 2) ∧ (∀ᵐ p ∂(((ν k γ).prod MeasureTheory.volume).restrict (E k γ)), B k γ / K k ≤ |MvPolynomial.eval (![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5]) (MvPolynomial.pderiv (3 : Fin 4) (P k γ))|)) ∧ ENNReal.ofReal ((K k)⁻¹) ≤ ∑ γ, ENNReal.ofReal (ω k γ) * (((ν k γ).prod MeasureTheory.volume).restrict (E k γ)) Set.univ) ∧ (∀ k γ r, 0 ≤ r → r ≤ L → Measurable (g k γ r) ∧ MeasureTheory.Measure.map ((fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => ((WithLp.toLp 2 ![p.2, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 1, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 2] : EuclideanSpace ℝ (Fin 3)), ⌊B k γ * ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 3 / ((2 : ℝ) ^ (-(⌊r * Real.log (N k) / Real.log 2⌋ : ℤ)))⌋))) ((((ν k γ).prod MeasureTheory.volume).restrict (E k γ))) = (MeasureTheory.volume.prod MeasureTheory.Measure.count).withDensity (g k γ r)) ∧ (∀ k γ u, 0 < u → u ≤ η * L → Measurable (G k γ u) ∧ MeasureTheory.Measure.map ((fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => ((fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => ((WithLp.toLp 2 ![p.2, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 1, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 2] : EuclideanSpace ℝ (Fin 3)), ⌊B k γ * ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 3 / ((2 : ℝ) ^ (-(⌊L * Real.log (N k) / Real.log 2⌋ : ℤ)))⌋)) p, fun j : Fin 2 => ⌊(WithLp.toLp 2 ![p.1.2 3, p.1.2 4]) j / ((2 : ℝ) ^ (-(⌊u * Real.log (N k) / Real.log 2⌋ : ℤ)))⌋))) ((((ν k γ).prod MeasureTheory.volume).restrict (E k γ))) = ((MeasureTheory.volume.prod MeasureTheory.Measure.count).prod MeasureTheory.Measure.count).withDensity (G k γ u)) ∧ (∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ L → 0 ≤ f s - f r ∧ f s - f r ≤ s - r) ∧ (∀ r τ : ℝ, 0 ≤ r → r ≤ L → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop, (∑ γ, ENNReal.ofReal (ω k γ) * (((ν k γ).prod MeasureTheory.volume).restrict (E k γ)) {p | g k γ r ((fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => ((WithLp.toLp 2 ![p.2, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 1, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 2] : EuclideanSpace ℝ (Fin 3)), ⌊B k γ * ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 3 / ((2 : ℝ) ^ (-(⌊r * Real.log (N k) / Real.log 2⌋ : ℤ)))⌋)) p) < ENNReal.ofReal (N k ^ (-f r - τ)) ∨ ENNReal.ofReal (N k ^ (-f r + τ)) < g k γ r ((fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => ((WithLp.toLp 2 ![p.2, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 1, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 2] : EuclideanSpace ℝ (Fin 3)), ⌊B k γ * ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 3 / ((2 : ℝ) ^ (-(⌊r * Real.log (N k) / Real.log 2⌋ : ℤ)))⌋)) p)}) ≤ ENNReal.ofReal (N k ^ (-c))) ∧ (∀ r : ℝ, 0 ≤ r → r ≤ L → f L - f r ≤ d * (L - r)) ∧ (∀ u τ : ℝ, 0 < u → u ≤ η * L → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop, (∑ γ, ENNReal.ofReal (ω k γ) * (((ν k γ).prod MeasureTheory.volume).restrict (E k γ)) {p | ENNReal.ofReal (N k ^ (-f L - S * u + τ)) < G k γ u ((fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => ((fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => ((WithLp.toLp 2 ![p.2, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 1, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 2] : EuclideanSpace ℝ (Fin 3)), ⌊B k γ * ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 3 / ((2 : ℝ) ^ (-(⌊L * Real.log (N k) / Real.log 2⌋ : ℤ)))⌋)) p, fun j : Fin 2 => ⌊(WithLp.toLp 2 ![p.1.2 3, p.1.2 4]) j / ((2 : ℝ) ^ (-(⌊u * Real.log (N k) / Real.log 2⌋ : ℤ)))⌋)) p)}) ≤ ENNReal.ofReal (N k ^ (-c))) ∧ ((∀ k γ, B k γ = 1) ∧ ∃ (Λ : ℕ → ℝ) (g₀ : ℝ), 0 < g₀ ∧ (∀ k γ (Z : Set (EuclideanSpace ℝ (Fin 3))), ν k γ {l | (WithLp.toLp 2 ![l.2 3, l.2 4, l.2 5] : EuclideanSpace ℝ (Fin 3)) ∈ Z} ≤ ENNReal.ofReal (Λ k) * MeasureTheory.volume Z) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, Λ k ≤ N k ^ (L - f L - g₀ + ε)) := by
  intro N₀ K₀ Λ₀ ν₀ E₀ F₀ σ hN₀ hNlim hK₀ hΛ₀ hσ hfmt₀ hslope₀ hF hdens₀ htyp₀ h10 h00 hlower
  change SingleFormat N₀ K₀ ν₀ E₀ at hfmt₀
  change JointDensities N₀ ν₀ E₀ at hdens₀
  change JointTypical N₀ ν₀ E₀ F₀ at htyp₀
  have hworlds : CropWorldsStatement := Submission.k4_dyadic_crop_worlds
  have haffine : CropAffineStatement := Submission.k4_dyadic_crop_affine_laws
  have htransfer : CropTypicalStatement := Submission.k4_dyadic_crop_typicality
  obtain ⟨L, u₀, d, S, η, hL, hL1, hu₀, hu₄, hd, hd1, hS, hη,
    hroom, hgap, hsecant, hgrowth⟩ :=
    exists_profile_endpoint hF hσ h10 h00 hlower
  obtain ⟨ψ, K, β, W, ω, ν, E, p, q, ρ, hψ, hK, hfmt, hcrop⟩ :=
    hworlds N₀ K₀ ν₀ E₀ u₀ hN₀ hNlim hK₀ hfmt₀ hu₀ hu₄.le
  let N : ℕ → ℝ := N₀ ∘ ψ
  have hψlim : Filter.Tendsto ψ Filter.atTop Filter.atTop := hψ.tendsto_atTop
  have hN : ∀ k, 2 ≤ N k := fun k => hN₀ (ψ k)
  have hNt : Filter.Tendsto N Filter.atTop Filter.atTop := hNlim.comp hψlim
  have hsource : FiniteSource (ν₀ ∘ ψ) (E₀ ∘ ψ) :=
    fun k => finiteSource_of_single hfmt₀ (ψ k)
  have hdens : JointDensities N (ν₀ ∘ ψ) (E₀ ∘ ψ) :=
    fun k => hdens₀ (ψ k)
  have htyp : JointTypical N (ν₀ ∘ ψ) (E₀ ∘ ψ) F₀ := by
    intro r u τ hr hr1 hu hu4 hτ
    obtain ⟨c, hc, he⟩ := htyp₀ r u τ hr hr1 hu hu4 hτ
    exact ⟨c, hc, hψlim.eventually he⟩
  have hslope : SlopeCeiling (ν₀ ∘ ψ) (Λ₀ ∘ ψ) := fun k => hslope₀ (ψ k)
  have hΛ : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, (Λ₀ ∘ ψ) k ≤ N k ^ ε :=
    fun ε hε => hψlim.eventually (hΛ₀ ε hε)
  obtain ⟨g, G, Λ, hlaws, hceiling, hΛexp⟩ :=
    haffine N (Λ₀ ∘ ψ) (ν₀ ∘ ψ) (E₀ ∘ ψ) L u₀ β W ω ν E p q ρ
      hN hNt hsource hL.le hL1 hu₀ hu₄ hcrop hdens hslope hΛ
  obtain ⟨hbase, hangular⟩ :=
    htransfer N (ν₀ ∘ ψ) (E₀ ∘ ψ) F₀ L u₀ β W ω ν E p q ρ g G
      hN hNt hsource hL.le hL1 hu₀ hu₄ hcrop hdens htyp hF hlaws
  let f : ℝ → ℝ := fun r => F₀ r u₀ + 2 * u₀ - β
  have hcap : AngularCap N L f S η W ω ν E G :=
    angular_cap_of_typical hN hroom hgrowth hangular
  refine ⟨N, K, L, d, S, η, W, ω, ν, E, (fun _ _ => MvPolynomial.X (3 : Fin 4)),
    (fun _ _ => 1), f, g, G, hN, hNt, hK, hL, hd, hd1, hS, hη, hfmt,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k γ r hr hrL
    simp only [one_mul]
    change Measurable (g k γ r) ∧ MeasureTheory.Measure.map (Obs N k r)
      (Selected (ν k γ) (E k γ)) = BaseRef.withDensity (g k γ r)
    exact hlaws.1 k γ r hr (hrL.trans hL1)
  · intro k γ u hu huη
    simp only [one_mul]
    change Measurable (G k γ u) ∧ MeasureTheory.Measure.map (JointObs N k L u)
      (Selected (ν k γ) (E k γ)) = JointRef.withDensity (G k γ u)
    exact hlaws.2 k γ u hu (by linarith)
  · intro r s hr hrs hsL
    have hi := hF.1 r s u₀ hr hrs (hsL.trans hL1) hu₀ hu₄.le
    dsimp [f]
    constructor <;> linarith [hi.1, hi.2]
  · intro r τ hr hrL hτ
    simpa only [Obs, Point, Scale, Selected, one_mul] using
      hbase r τ hr (hrL.trans hL1) hτ
  · intro r hr hrL
    dsimp [f]
    linarith [hsecant r hr hrL]
  · simpa only [AngularCap, JointObs, Obs, Point, Scale, Selected, one_mul] using hcap
  · refine ⟨(by intro k γ; rfl), Λ, L - F₀ L u₀, (by linarith), hceiling, ?_⟩
    have heq : L - f L - (L - F₀ L u₀) = β - 2 * u₀ := by dsimp [f]; ring
    simpa only [heq] using hΛexp
