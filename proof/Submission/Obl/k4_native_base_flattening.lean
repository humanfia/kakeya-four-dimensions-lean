import Mathlib
import ChallengeDeps
import Submission.Obl.k4_native_base_flattening.Assembly
set_option linter.unusedVariables false

/-!
# `Submission.k4_native_base_flattening`

Native polynomial-format incidence laws have observation densities after every measurable further
selection (`exists_density`: a volume-preserving shear and Fubini), and one polynomial base mesh
gives bounded common-floor-label tables (`uniform_native_flattening`, `table`) whose factor-two
and lower-cutoff exceptions have mass at most `N⁻¹` (`table_exception_mass`).
-/

open MeasureTheory Set
open Submission.Obl.k4_native_base_flattening

theorem Submission.k4_native_base_flattening : ∀ (N K : ℕ → ℝ) (ν : (ℕ → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ)))) (E : (ℕ → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))), (∀ k, 2 ≤ N k) → Filter.Tendsto N Filter.atTop Filter.atTop → ((fun N K => ((∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε)) : (ℕ → ℝ) → (ℕ → ℝ) → Prop) N K → ((fun N K ν E => (∃ M D : ℕ, ∀ k, MeasureTheory.IsProbabilityMeasure (ν k) ∧ (∃ m : ℕ, (m : ℝ) ≤ N k ^ M ∧ ∃ (c : Fin m → ℝ) (i : Fin m → ℕ) (A : Fin m → Set (Fin 6 → ℝ)), (∀ j, 0 ≤ c j ∧ c j ≤ N k ^ M ∧ (i j : ℝ) ≤ N k ^ M ∧ (∃ m₀ : ℕ, (m₀ : ℝ) ≤ (N k ^ M) ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin 6) ℝ, (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool, ∀ x₀, x₀ ∈ (A j) ↔ b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true) ∧ (∀ x ∈ A j, ∀ b, |x b| ≤ N k ^ M)) ∧ ν k = ∑ j, (ENNReal.ofReal (c j)) • MeasureTheory.Measure.map (fun x => (i j, x)) (MeasureTheory.volume.restrict (A j))) ∧ MeasurableSet (E k) ∧ E k ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 ∧ (∀ p ∈ E k, (p.1.1 : ℝ) ≤ N k ^ M ∧ ∀ e, |p.1.2 e| ≤ N k ^ M) ∧ (∀ i, (∃ m₀ : ℕ, (m₀ : ℝ) ≤ (N k ^ M) ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin 7) ℝ, (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool, ∀ x₀, x₀ ∈ ({x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ (E k)}) ↔ b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true)) ∧ (∀ᵐ l ∂(ν k), ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(WithLp.toLp 2 ![![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 1, ![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 2])‖ + ‖(WithLp.toLp 2 ![l.2 3, l.2 4])‖ ≤ K k ∧ |![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 3| ≤ K k) ∧ ENNReal.ofReal ((K k)⁻¹) ≤ (((ν k).prod MeasureTheory.volume).restrict (E k)) Set.univ)) : (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) → (ℕ → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) → Prop) N K ν E → ∀ R U : ℝ, 0 < R → 0 < U → ((fun N ν E R U => ((fun N ν E R U => ∀ k (S : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)), MeasurableSet S → S ⊆ E k → ∀ (r u : ℝ), 0 ≤ r → r ≤ R → 0 ≤ u → u ≤ U → ∃ G : (((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal), Measurable G ∧ MeasureTheory.Measure.map (((fun n r u => fun p : ((ℕ × (Fin 6 → ℝ)) × ℝ) => (((WithLp.toLp 2 ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4] : EuclideanSpace ℝ (Fin 3)), ⌊(p.1.2 2 + p.2 * p.1.2 5) / ((2 : ℝ) ^ (-(⌊r * Real.log n / Real.log 2⌋ : ℤ)))⌋), fun j : Fin 2 => ⌊(WithLp.toLp 2 ![p.1.2 3, p.1.2 4]) j / ((2 : ℝ) ^ (-(⌊u * Real.log n / Real.log 2⌋ : ℤ)))⌋)) : ℝ → ℝ → ℝ → ((ℕ × (Fin 6 → ℝ)) × ℝ) → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ))) (N k) r u) (((ν k).prod MeasureTheory.volume).restrict S) = ((((MeasureTheory.volume.prod MeasureTheory.Measure.count).prod MeasureTheory.Measure.count)) : MeasureTheory.Measure ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ))).withDensity G) : (ℕ → ℝ) → (ℕ → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) → (ℕ → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) → ℝ → ℝ → Prop) N ν E R U ∧ ∃ (C H : ℕ) (g : (ℕ → ℝ → ℝ → (Fin 6 → ℤ) → ℝ)), ((fun N μ R U C H g => (∀ k (r u : ℝ), 0 ≤ r → r ≤ R → 0 ≤ u → u ≤ U → ∀ z : Fin 6 → ℤ, 0 ≤ g k r u z ∧ g k r u z ≤ (N k) ^ C) ∧ (∀ k (r u : ℝ), 0 ≤ r → r ≤ R → 0 ≤ u → u ≤ U → ∀ G : (((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal), Measurable G → MeasureTheory.Measure.map (((fun n r u => fun p : ((ℕ × (Fin 6 → ℝ)) × ℝ) => (((WithLp.toLp 2 ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4] : EuclideanSpace ℝ (Fin 3)), ⌊(p.1.2 2 + p.2 * p.1.2 5) / ((2 : ℝ) ^ (-(⌊r * Real.log n / Real.log 2⌋ : ℤ)))⌋), fun j : Fin 2 => ⌊(WithLp.toLp 2 ![p.1.2 3, p.1.2 4]) j / ((2 : ℝ) ^ (-(⌊u * Real.log n / Real.log 2⌋ : ℤ)))⌋)) : ℝ → ℝ → ℝ → ((ℕ × (Fin 6 → ℝ)) × ℝ) → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ))) (N k) r u) (μ k) = ((((MeasureTheory.volume.prod MeasureTheory.Measure.count).prod MeasureTheory.Measure.count)) : MeasureTheory.Measure ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ))).withDensity G → (μ k) {p | G (((fun n r u => fun p : ((ℕ × (Fin 6 → ℝ)) × ℝ) => (((WithLp.toLp 2 ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4] : EuclideanSpace ℝ (Fin 3)), ⌊(p.1.2 2 + p.2 * p.1.2 5) / ((2 : ℝ) ^ (-(⌊r * Real.log n / Real.log 2⌋ : ℤ)))⌋), fun j : Fin 2 => ⌊(WithLp.toLp 2 ![p.1.2 3, p.1.2 4]) j / ((2 : ℝ) ^ (-(⌊u * Real.log n / Real.log 2⌋ : ℤ)))⌋)) : ℝ → ℝ → ℝ → ((ℕ × (Fin 6 → ℝ)) × ℝ) → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ))) (N k) r u p) < (2 : ENNReal)⁻¹ * ENNReal.ofReal (g k r u (((fun n H R U => fun p : ((ℕ × (Fin 6 → ℝ)) × ℝ) => (![⌊n ^ H * p.2⌋, ⌊n ^ H * (p.1.2 0 + p.2 * p.1.2 3)⌋, ⌊n ^ H * (p.1.2 1 + p.2 * p.1.2 4)⌋, ⌊(p.1.2 2 + p.2 * p.1.2 5) / ((2 : ℝ) ^ (-(⌊R * Real.log n / Real.log 2⌋ : ℤ)))⌋, ⌊p.1.2 3 / ((2 : ℝ) ^ (-(⌊U * Real.log n / Real.log 2⌋ : ℤ)))⌋, ⌊p.1.2 4 / ((2 : ℝ) ^ (-(⌊U * Real.log n / Real.log 2⌋ : ℤ)))⌋] : Fin 6 → ℤ)) : ℝ → ℕ → ℝ → ℝ → ((ℕ × (Fin 6 → ℝ)) × ℝ) → (Fin 6 → ℤ)) (N k) H R U p)) ∨ (2 : ENNReal) * ENNReal.ofReal (g k r u (((fun n H R U => fun p : ((ℕ × (Fin 6 → ℝ)) × ℝ) => (![⌊n ^ H * p.2⌋, ⌊n ^ H * (p.1.2 0 + p.2 * p.1.2 3)⌋, ⌊n ^ H * (p.1.2 1 + p.2 * p.1.2 4)⌋, ⌊(p.1.2 2 + p.2 * p.1.2 5) / ((2 : ℝ) ^ (-(⌊R * Real.log n / Real.log 2⌋ : ℤ)))⌋, ⌊p.1.2 3 / ((2 : ℝ) ^ (-(⌊U * Real.log n / Real.log 2⌋ : ℤ)))⌋, ⌊p.1.2 4 / ((2 : ℝ) ^ (-(⌊U * Real.log n / Real.log 2⌋ : ℤ)))⌋] : Fin 6 → ℤ)) : ℝ → ℕ → ℝ → ℝ → ((ℕ × (Fin 6 → ℝ)) × ℝ) → (Fin 6 → ℤ)) (N k) H R U p)) < G (((fun n r u => fun p : ((ℕ × (Fin 6 → ℝ)) × ℝ) => (((WithLp.toLp 2 ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4] : EuclideanSpace ℝ (Fin 3)), ⌊(p.1.2 2 + p.2 * p.1.2 5) / ((2 : ℝ) ^ (-(⌊r * Real.log n / Real.log 2⌋ : ℤ)))⌋), fun j : Fin 2 => ⌊(WithLp.toLp 2 ![p.1.2 3, p.1.2 4]) j / ((2 : ℝ) ^ (-(⌊u * Real.log n / Real.log 2⌋ : ℤ)))⌋)) : ℝ → ℝ → ℝ → ((ℕ × (Fin 6 → ℝ)) × ℝ) → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ))) (N k) r u p) ∨ ENNReal.ofReal (g k r u (((fun n H R U => fun p : ((ℕ × (Fin 6 → ℝ)) × ℝ) => (![⌊n ^ H * p.2⌋, ⌊n ^ H * (p.1.2 0 + p.2 * p.1.2 3)⌋, ⌊n ^ H * (p.1.2 1 + p.2 * p.1.2 4)⌋, ⌊(p.1.2 2 + p.2 * p.1.2 5) / ((2 : ℝ) ^ (-(⌊R * Real.log n / Real.log 2⌋ : ℤ)))⌋, ⌊p.1.2 3 / ((2 : ℝ) ^ (-(⌊U * Real.log n / Real.log 2⌋ : ℤ)))⌋, ⌊p.1.2 4 / ((2 : ℝ) ^ (-(⌊U * Real.log n / Real.log 2⌋ : ℤ)))⌋] : Fin 6 → ℤ)) : ℝ → ℕ → ℝ → ℝ → ((ℕ × (Fin 6 → ℝ)) × ℝ) → (Fin 6 → ℤ)) (N k) H R U p)) < ENNReal.ofReal ((N k) ^ (-(C : ℝ)))} ≤ ENNReal.ofReal ((N k) ^ (-1 : ℝ)))) : (ℕ → ℝ) → (ℕ → MeasureTheory.Measure ((ℕ × (Fin 6 → ℝ)) × ℝ)) → ℝ → ℝ → ℕ → ℕ → (ℕ → ℝ → ℝ → (Fin 6 → ℤ) → ℝ) → Prop) N (((fun ν E => fun k => ((ν k).prod MeasureTheory.volume).restrict (E k)) : (ℕ → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) → (ℕ → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) → (ℕ → MeasureTheory.Measure ((ℕ × (Fin 6 → ℝ)) × ℝ))) ν E) R U C H g) : (ℕ → ℝ) → (ℕ → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) → (ℕ → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) → ℝ → ℝ → Prop) N ν E R U := by
  intro N K ν E hN hNt hK hfmt R U hR hU
  obtain ⟨M, D, hk⟩ := hfmt
  choose m hm c i A hj hν using fun k => (hk k).2.1
  have hEm : ∀ k, MeasurableSet (E k) := fun k => (hk k).2.2.1
  have hEsub : ∀ k, E k ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 := fun k => (hk k).2.2.2.1
  have hEfib := fun k => (hk k).2.2.2.2.2.1
  have hAm : ∀ k j, MeasurableSet (A k j) := by
    intro k j
    obtain ⟨m₀, -, p₀, -, b₀, hA⟩ := (hj k j).2.2.2.1
    exact measurableSet_of_polynomial_description (A k j) p₀ b₀ hA
  have hc : ∀ k j, 0 ≤ c k j := fun k j => (hj k j).1
  have hfmt' : ∀ k, NativeMixtureFormat (N k) M D (fun x =>
      ∑ j, nativeComponentDensity (c k j) (A k j) (eventFiber (E k) (i k j)) x) := by
    intro k
    refine ⟨m k, c k, A k, fun j => eventFiber (E k) (i k j), hm k,
      fun j => ⟨(hj k j).1, (hj k j).2.1⟩, fun j => (hj k j).2.2.2.1,
      fun j => hEfib k (i k j), fun j a ha l => (hj k j).2.2.2.2 a ha l, ?_, rfl⟩
    intro j a ha
    exact (Set.mem_prod.mp (hEsub k ha)).2
  obtain ⟨H, hH⟩ := uniform_native_flattening M D 10
  choose h hhm hhb hhcell hhs hhe using fun k => hH (N k) (hN k) _ (hfmt' k)
  refine ⟨?_, ?_⟩
  · intro k S hS hSE r u hr hrR hu huU
    refine ⟨marg (Submission.Obl.k4_profile_density_bounds.width (N k) r)
      (Submission.Obl.k4_profile_density_bounds.width (N k) u)
      (nativeDensity (c k) (i k) (A k) S),
      measurable_marg _ _ (measurable_nativeDensity _ _ (hAm k) hS), ?_⟩
    rw [hν k]
    exact exists_density (c k) (i k) (hAm k) hS (N k) r u
  · refine ⟨6 * (M + 3) + ⌈R⌉₊ + 2 * ⌈U⌉₊ + 12 + 4, H,
      fun k r u z => table (N k) H R U r u (h k) z, ?_, ?_⟩
    · intro k r u hr hrR hu huU z
      refine ⟨table_nonneg _ _ _ _ _ _ _ _,
        (table_le (hN k) M H R U r u (hhb k) (hhs k) z).trans ?_⟩
      exact pow_le_pow_right₀ (by linarith [hN k]) (by omega)
    · intro k r u hr hrR hu huU G hG hmap
      beta_reduce at hmap ⊢
      have hmap' := hmap
      rw [hν k] at hmap'
      have key := table_exception_mass (hN k) M H (c k) (hc k) (i k) (hAm k) (hEm k)
        (hhm k) (hhb k) (hhcell k) (hhs k) (hhe k) hr hrR hu huU ⌈R⌉₊ ⌈U⌉₊
        (Nat.le_ceil R) (Nat.le_ceil U) _ le_rfl G hG hmap'
      rw [hν k]
      exact key
