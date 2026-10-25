import Mathlib
import ChallengeDeps
import Submission.Obl.k4_profile_density_bounds.Endpoint
import Submission.Obl.k4_profile_density_bounds.Spread
import Submission.Obl.k4_profile_density_bounds.Ceiling
set_option linter.unusedVariables false

/-!
# `Submission.k4_profile_density_bounds`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_profile_density_bounds`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_profile_density_bounds/`
belong to this obligation.
-/

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_profile_density_bounds

theorem Submission.k4_profile_density_bounds : ∀ (N K Λ : ℕ → ℝ) (ν : ℕ → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) (E : ℕ → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (F : ℝ → ℝ → ℝ) (σ C : ℝ), (∀ k, 2 ≤ N k) → Filter.Tendsto N Filter.atTop Filter.atTop → ((∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε) → (∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, Λ k ≤ N k ^ ε) → 0 < σ → 0 < C → (∃ M D : ℕ, ∀ k, MeasureTheory.IsProbabilityMeasure (ν k) ∧ (∃ m : ℕ, (m : ℝ) ≤ N k ^ M ∧ ∃ (c : Fin m → ℝ) (i : Fin m → ℕ) (A : Fin m → Set (Fin 6 → ℝ)), (∀ j, 0 ≤ c j ∧ c j ≤ N k ^ M ∧ (i j : ℝ) ≤ N k ^ M ∧ (∃ m₀ : ℕ, (m₀ : ℝ) ≤ (N k ^ M) ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin 6) ℝ, (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool, ∀ x₀, x₀ ∈ (A j) ↔ b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true) ∧ (∀ x ∈ A j, ∀ b, |x b| ≤ N k ^ M)) ∧ ν k = ∑ j, (ENNReal.ofReal (c j)) • MeasureTheory.Measure.map (fun x => (i j, x)) (MeasureTheory.volume.restrict (A j))) ∧ MeasurableSet (E k) ∧ E k ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 ∧ (∀ p ∈ E k, (p.1.1 : ℝ) ≤ N k ^ M ∧ ∀ e, |p.1.2 e| ≤ N k ^ M) ∧ (∀ i, (∃ m₀ : ℕ, (m₀ : ℝ) ≤ (N k ^ M) ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin 7) ℝ, (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool, ∀ x₀, x₀ ∈ ({x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ (E k)}) ↔ b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true)) ∧ (∀ᵐ l ∂(ν k), ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(WithLp.toLp 2 ![![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 1, ![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 2])‖ + ‖(WithLp.toLp 2 ![l.2 3, l.2 4])‖ ≤ K k ∧ |![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 3| ≤ K k) ∧ ENNReal.ofReal ((K k)⁻¹) ≤ (((ν k).prod MeasureTheory.volume).restrict (E k)) Set.univ) → (∀ k, ∃ (m : ℕ) (z : Fin m → EuclideanSpace ℝ (Fin 4)), (m : ℝ) ≤ C * N k ^ (4 - σ) ∧ ∀ p ∈ E k, ∃ j : Fin m, ‖(WithLp.toLp 2 ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] : EuclideanSpace ℝ (Fin 4)) - z j‖ ≤ C / N k) → (∀ k (t : ℝ) (S T : Set (EuclideanSpace ℝ (Fin 2))), t ∈ Set.Icc (0 : ℝ) 1 → (ν k) {l | (WithLp.toLp 2 ![![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 1, ![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 2] : EuclideanSpace ℝ (Fin 2)) ∈ S ∧ (WithLp.toLp 2 ![l.2 3, l.2 4] : EuclideanSpace ℝ (Fin 2)) ∈ T} ≤ ENNReal.ofReal (Λ k * N k ^ 2) * MeasureTheory.volume S * MeasureTheory.volume T) → (∀ α : ℝ, 0 < α → ∃ θ : ℝ, 0 < θ ∧ ∀ᶠ k in Filter.atTop, ∀ U : Set (EuclideanSpace ℝ (Fin 3)), MeasureTheory.volume U ≤ ENNReal.ofReal (N k ^ (-α)) → ((ν k).prod MeasureTheory.volume) {p | p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ (WithLp.toLp 2 ![p.2, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 1, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 2] : EuclideanSpace ℝ (Fin 3)) ∈ U} ≤ ENNReal.ofReal (N k ^ (-θ))) → ((∀ r r' u : ℝ, 0 ≤ r → r ≤ r' → r' ≤ 1 → 0 ≤ u → u ≤ 4 → 0 ≤ F r' u - F r u ∧ F r' u - F r u ≤ r' - r) ∧ (∀ r u u' : ℝ, 0 ≤ r → r ≤ 1 → 0 ≤ u → u ≤ u' → u' ≤ 4 → 0 ≤ F r u' - F r u ∧ F r u' - F r u ≤ 2 * (u' - u))) → (∀ k (r u : ℝ), 0 ≤ r → r ≤ 1 → 0 ≤ u → u ≤ 4 → ∃ G : (EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ) → ENNReal, Measurable G ∧ MeasureTheory.Measure.map (fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => (((WithLp.toLp 2 ![p.2, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 1, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 2] : EuclideanSpace ℝ (Fin 3)), ⌊![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 3 / ((2 : ℝ) ^ (-(⌊r * Real.log (N k) / Real.log 2⌋ : ℤ)))⌋), fun j : Fin 2 => ⌊(WithLp.toLp 2 ![p.1.2 3, p.1.2 4]) j / ((2 : ℝ) ^ (-(⌊u * Real.log (N k) / Real.log 2⌋ : ℤ)))⌋)) (((ν k).prod MeasureTheory.volume).restrict (E k)) = ((MeasureTheory.volume.prod MeasureTheory.Measure.count).prod MeasureTheory.Measure.count).withDensity G) → (∀ r u τ : ℝ, 0 ≤ r → r ≤ 1 → 0 ≤ u → u ≤ 4 → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop, ∀ G : (EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ) → ENNReal, Measurable G → MeasureTheory.Measure.map (fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => (((WithLp.toLp 2 ![p.2, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 1, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 2] : EuclideanSpace ℝ (Fin 3)), ⌊![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 3 / ((2 : ℝ) ^ (-(⌊r * Real.log (N k) / Real.log 2⌋ : ℤ)))⌋), fun j : Fin 2 => ⌊(WithLp.toLp 2 ![p.1.2 3, p.1.2 4]) j / ((2 : ℝ) ^ (-(⌊u * Real.log (N k) / Real.log 2⌋ : ℤ)))⌋)) (((ν k).prod MeasureTheory.volume).restrict (E k)) = ((MeasureTheory.volume.prod MeasureTheory.Measure.count).prod MeasureTheory.Measure.count).withDensity G → (((ν k).prod MeasureTheory.volume).restrict (E k)) {p | G ((fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => (((WithLp.toLp 2 ![p.2, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 1, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 2] : EuclideanSpace ℝ (Fin 3)), ⌊![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 3 / ((2 : ℝ) ^ (-(⌊r * Real.log (N k) / Real.log 2⌋ : ℤ)))⌋), fun j : Fin 2 => ⌊(WithLp.toLp 2 ![p.1.2 3, p.1.2 4]) j / ((2 : ℝ) ^ (-(⌊u * Real.log (N k) / Real.log 2⌋ : ℤ)))⌋)) p) < ENNReal.ofReal (N k ^ (-F r u - τ)) ∨ ENNReal.ofReal (N k ^ (-F r u + τ)) < G ((fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => (((WithLp.toLp 2 ![p.2, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 1, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 2] : EuclideanSpace ℝ (Fin 3)), ⌊![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 3 / ((2 : ℝ) ^ (-(⌊r * Real.log (N k) / Real.log 2⌋ : ℤ)))⌋), fun j : Fin 2 => ⌊(WithLp.toLp 2 ![p.1.2 3, p.1.2 4]) j / ((2 : ℝ) ^ (-(⌊u * Real.log (N k) / Real.log 2⌋ : ℤ)))⌋)) p)} ≤ ENNReal.ofReal (N k ^ (-c))) → F 1 0 ≤ 1 - σ ∧ 0 ≤ F 0 0 ∧ ∀ r u : ℝ, 0 ≤ r → r ≤ 1 → 0 ≤ u → u ≤ 4 → 2 * u - 2 ≤ F r u := by
  intro N K Λ ν E F σ C hN hNt hK hΛ hσ hC hfmt hcover hjoint hspread hinc hdens htyp
  have hN1 : ∀ k, 1 ≤ N k := fun k => (by norm_num : (1 : ℝ) ≤ 2).trans (hN k)
  obtain ⟨M, D, hfmt⟩ := hfmt
  have hprob : ∀ k, IsProbabilityMeasure (ν k) := fun k => (hfmt k).1
  have hE : ∀ k, MeasurableSet (E k) := by
    intro k
    obtain ⟨_, _, h, _, _, _, _, _⟩ := hfmt k
    exact h
  have htimes : ∀ k, E k ⊆ univ ×ˢ Icc (0 : ℝ) 1 := by
    intro k
    obtain ⟨_, _, _, h, _, _, _, _⟩ := hfmt k
    exact h
  have hmass : ∀ k, ENNReal.ofReal ((K k)⁻¹) ≤ selected (ν k) (E k) univ := by
    intro k
    obtain ⟨_, _, _, _, _, _, _, h⟩ := hfmt k
    exact h
  have hvel : ∀ k, ∀ᵐ l ∂ν k, ‖velocity l‖ ≤ K k := by
    intro k
    obtain ⟨_, _, _, _, _, _, h, _⟩ := hfmt k
    filter_upwards [h] with l hl
    have hv := (hl 0 (by norm_num)).1
    change ‖velocity l‖ ≤ K k
    have hn := norm_nonneg (WithLp.toLp 2 ![l.2 0, l.2 1] : EuclideanSpace ℝ (Fin 2))
    change ‖(WithLp.toLp 2 ![l.2 0 + 0 * l.2 3, l.2 1 + 0 * l.2 4] :
      EuclideanSpace ℝ (Fin 2))‖ + ‖velocity l‖ ≤ K k at hv
    simp only [zero_mul, add_zero] at hv
    linarith
  have hd (r u : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (hu : 0 ≤ u) (hu4 : u ≤ 4) :
      ∀ k, ∃ G, Measurable G ∧ (selected (ν k) (E k)).map (observe (N k) r u) =
        reference.withDensity G := fun k => hdens k r u hr hr1 hu hu4
  have ht (r u : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (hu : 0 ≤ u) (hu4 : u ≤ 4) :
      Typical N (fun k => selected (ν k) (E k)) (fun k => observe (N k) r u) (F r u) := by
    intro τ hτ
    exact htyp r u τ hr hr1 hu hu4 hτ
  refine ⟨?_, ?_, ?_⟩
  · exact profile_endpoint_le hN1 hNt hK.1 hK.2 ν E hE hvel hmass
      (hd 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)) hC.le
      (ht 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)) hcover
  · exact profile_nonneg_of_spread hN1 hNt hK.1 hK.2 ν E hprob hE htimes hmass
      (hd 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)) hspread
      (ht 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · apply two_mul_sub_two_le_profile N K Λ ν E F hN hNt hK.1 hK.2 hΛ hprob htimes
    · intro k
      simpa only [ENNReal.ofReal_inv_of_pos (by linarith [hK.1 k] : 0 < K k)] using hmass k
    · intro k t ht S T
      exact hjoint k t S T ht
    · exact hdens
    · exact htyp
