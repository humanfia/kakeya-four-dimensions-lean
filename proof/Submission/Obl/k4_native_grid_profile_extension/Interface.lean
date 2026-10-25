/-
Adapted from this LOT tree, o075, session x0249, commit c9860862e62947c5fb8b3bc42c0a4ebc874a7eee,
Submission/Obl/k4_joint_homogenization/Interface.lean. Earlier source attributions are retained below.
-/

import Mathlib
import ChallengeDeps

/-! Mathlib-only interfaces used to state and assemble the three-part split. -/

noncomputable section

namespace Submission.Obl.k4_native_grid_profile_extension

abbrev Format : (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) → (ℕ → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) → Prop := fun N K ν E => (∃ M D : ℕ, ∀ k, MeasureTheory.IsProbabilityMeasure (ν k) ∧ (∃ m : ℕ, (m : ℝ) ≤ N k ^ M ∧ ∃ (c : Fin m → ℝ) (i : Fin m → ℕ) (A : Fin m → Set (Fin 6 → ℝ)), (∀ j, 0 ≤ c j ∧ c j ≤ N k ^ M ∧ (i j : ℝ) ≤ N k ^ M ∧ (∃ m₀ : ℕ, (m₀ : ℝ) ≤ (N k ^ M) ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin 6) ℝ, (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool, ∀ x₀, x₀ ∈ (A j) ↔ b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true) ∧ (∀ x ∈ A j, ∀ b, |x b| ≤ N k ^ M)) ∧ ν k = ∑ j, (ENNReal.ofReal (c j)) • MeasureTheory.Measure.map (fun x => (i j, x)) (MeasureTheory.volume.restrict (A j))) ∧ MeasurableSet (E k) ∧ E k ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 ∧ (∀ p ∈ E k, (p.1.1 : ℝ) ≤ N k ^ M ∧ ∀ e, |p.1.2 e| ≤ N k ^ M) ∧ (∀ i, (∃ m₀ : ℕ, (m₀ : ℝ) ≤ (N k ^ M) ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin 7) ℝ, (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool, ∀ x₀, x₀ ∈ ({x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ (E k)}) ↔ b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true)) ∧ (∀ᵐ l ∂(ν k), ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(WithLp.toLp 2 ![![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 1, ![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 2])‖ + ‖(WithLp.toLp 2 ![l.2 3, l.2 4])‖ ≤ K k ∧ |![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 3| ≤ K k) ∧ ENNReal.ofReal ((K k)⁻¹) ≤ (((ν k).prod MeasureTheory.volume).restrict (E k)) Set.univ)

abbrev Subpower : (ℕ → ℝ) → (ℕ → ℝ) → Prop := fun N K => ((∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε)

abbrev Law : (ℕ → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) → (ℕ → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) → (ℕ → MeasureTheory.Measure ((ℕ × (Fin 6 → ℝ)) × ℝ)) := fun ν E => fun k => ((ν k).prod MeasureTheory.volume).restrict (E k)

abbrev Observation : ℝ → ℝ → ℝ → ((ℕ × (Fin 6 → ℝ)) × ℝ) → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) := fun n r u => fun p : ((ℕ × (Fin 6 → ℝ)) × ℝ) => (((WithLp.toLp 2 ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4] : EuclideanSpace ℝ (Fin 3)), ⌊(p.1.2 2 + p.2 * p.1.2 5) / ((2 : ℝ) ^ (-(⌊r * Real.log n / Real.log 2⌋ : ℤ)))⌋), fun j : Fin 2 => ⌊(WithLp.toLp 2 ![p.1.2 3, p.1.2 4]) j / ((2 : ℝ) ^ (-(⌊u * Real.log n / Real.log 2⌋ : ℤ)))⌋)

abbrev Labels : ℝ → ℕ → ℝ → ℝ → ((ℕ × (Fin 6 → ℝ)) × ℝ) → (Fin 6 → ℤ) := fun n H R U => fun p : ((ℕ × (Fin 6 → ℝ)) × ℝ) => (![⌊n ^ H * p.2⌋, ⌊n ^ H * (p.1.2 0 + p.2 * p.1.2 3)⌋, ⌊n ^ H * (p.1.2 1 + p.2 * p.1.2 4)⌋, ⌊(p.1.2 2 + p.2 * p.1.2 5) / ((2 : ℝ) ^ (-(⌊R * Real.log n / Real.log 2⌋ : ℤ)))⌋, ⌊p.1.2 3 / ((2 : ℝ) ^ (-(⌊U * Real.log n / Real.log 2⌋ : ℤ)))⌋, ⌊p.1.2 4 / ((2 : ℝ) ^ (-(⌊U * Real.log n / Real.log 2⌋ : ℤ)))⌋] : Fin 6 → ℤ)

abbrev Reference : MeasureTheory.Measure ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) := ((MeasureTheory.volume.prod MeasureTheory.Measure.count).prod MeasureTheory.Measure.count)

abbrev Clamp : ℝ → ℚ → ℝ := fun B q => max (0 : ℝ) (min B (q : ℝ))

abbrev DensityExists : (ℕ → ℝ) → (ℕ → MeasureTheory.Measure ((ℕ × (Fin 6 → ℝ)) × ℝ)) → ℝ → ℝ → Prop := fun N μ R U => ∀ k (r u : ℝ), 0 ≤ r → r ≤ R → 0 ≤ u → u ≤ U → ∃ G : (((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal), Measurable G ∧ MeasureTheory.Measure.map (Observation (N k) r u) (μ k) = Reference.withDensity G

abbrev SelectionAC : (ℕ → ℝ) → (ℕ → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) → (ℕ → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) → ℝ → ℝ → Prop := fun N ν E R U => ∀ k (S : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)), MeasurableSet S → S ⊆ E k → ∀ (r u : ℝ), 0 ≤ r → r ≤ R → 0 ≤ u → u ≤ U → ∃ G : (((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal), Measurable G ∧ MeasureTheory.Measure.map (Observation (N k) r u) (((ν k).prod MeasureTheory.volume).restrict S) = Reference.withDensity G

abbrev TableApprox : (ℕ → ℝ) → (ℕ → MeasureTheory.Measure ((ℕ × (Fin 6 → ℝ)) × ℝ)) → ℝ → ℝ → ℕ → ℕ → (ℕ → ℝ → ℝ → (Fin 6 → ℤ) → ℝ) → Prop := fun N μ R U C H g => (∀ k (r u : ℝ), 0 ≤ r → r ≤ R → 0 ≤ u → u ≤ U → ∀ z : Fin 6 → ℤ, 0 ≤ g k r u z ∧ g k r u z ≤ (N k) ^ C) ∧ (∀ k (r u : ℝ), 0 ≤ r → r ≤ R → 0 ≤ u → u ≤ U → ∀ G : (((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal), Measurable G → MeasureTheory.Measure.map (Observation (N k) r u) (μ k) = Reference.withDensity G → (μ k) {p | G (Observation (N k) r u p) < (2 : ENNReal)⁻¹ * ENNReal.ofReal (g k r u (Labels (N k) H R U p)) ∨ (2 : ENNReal) * ENNReal.ofReal (g k r u (Labels (N k) H R U p)) < G (Observation (N k) r u p) ∨ ENNReal.ofReal (g k r u (Labels (N k) H R U p)) < ENNReal.ofReal ((N k) ^ (-(C : ℝ)))} ≤ ENNReal.ofReal ((N k) ^ (-1 : ℝ)))

abbrev FlatData : (ℕ → ℝ) → (ℕ → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) → (ℕ → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) → ℝ → ℝ → Prop := fun N ν E R U => SelectionAC N ν E R U ∧ ∃ (C H : ℕ) (g : (ℕ → ℝ → ℝ → (Fin 6 → ℤ) → ℝ)), TableApprox N (Law ν E) R U C H g

abbrev GridTypical : (ℕ → ℝ) → (ℕ → MeasureTheory.Measure ((ℕ × (Fin 6 → ℝ)) × ℝ)) → ℝ → ℝ → (ℕ → ℚ → ℚ → ℝ) → Prop := fun N μ R U a => ∀ (q s : ℚ) (τ : ℝ), 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop, ∀ G : (((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal), Measurable G → MeasureTheory.Measure.map (Observation (N k) (Clamp R q) (Clamp U s)) (μ k) = Reference.withDensity G → (μ k) {p | G (Observation (N k) (Clamp R q) (Clamp U s) p) < ENNReal.ofReal ((N k) ^ (-(a k q s) - τ)) ∨ ENNReal.ofReal ((N k) ^ (-(a k q s) + τ)) < G (Observation (N k) (Clamp R q) (Clamp U s) p)} ≤ ENNReal.ofReal ((N k) ^ (-c))

abbrev GridData : (ℕ → ℝ) → (ℕ → MeasureTheory.Measure ((ℕ × (Fin 6 → ℝ)) × ℝ)) → ℝ → ℝ → Prop := fun N μ R U => ∃ (A : ℕ) (a : ℕ → ℚ → ℚ → ℝ), (∀ k q s, |a k q s| ≤ (A : ℝ)) ∧ GridTypical N μ R U a

abbrev ProfileRegular : ℝ → ℝ → (ℝ → ℝ → ℝ) → Prop := fun R U F => ((∀ r r' u : ℝ, 0 ≤ r → r ≤ r' → r' ≤ R → 0 ≤ u → u ≤ U → 0 ≤ F r' u - F r u ∧ F r' u - F r u ≤ r' - r) ∧ (∀ r u u' : ℝ, 0 ≤ r → r ≤ R → 0 ≤ u → u ≤ u' → u' ≤ U → 0 ≤ F r u' - F r u ∧ F r u' - F r u ≤ 2 * (u' - u)))

abbrev Typical : (ℕ → ℝ) → (ℕ → MeasureTheory.Measure ((ℕ × (Fin 6 → ℝ)) × ℝ)) → ℝ → ℝ → (ℝ → ℝ → ℝ) → Prop := fun N μ R U F => ∀ r u τ : ℝ, 0 ≤ r → r ≤ R → 0 ≤ u → u ≤ U → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop, ∀ G : (((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal), Measurable G → MeasureTheory.Measure.map (Observation (N k) (r) (u)) (μ k) = Reference.withDensity G → (μ k) {p | G (Observation (N k) (r) (u) p) < ENNReal.ofReal ((N k) ^ (-(F r u) - τ)) ∨ ENNReal.ofReal ((N k) ^ (-(F r u) + τ)) < G (Observation (N k) (r) (u) p)} ≤ ENNReal.ofReal ((N k) ^ (-c))

end Submission.Obl.k4_native_grid_profile_extension
