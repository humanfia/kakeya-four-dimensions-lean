import Submission.Obl.k4_dk4_smoothed_problem.Configuration
import Submission.Obl.k4_dk4_smoothed_problem.Growth

open MeasureTheory Set Filter

namespace Submission.Obl.k4_dk4_smoothed_problem

open Framework

/- The frozen output, copied verbatim from the assigned theorem to keep the
   construction lemma readable. -/
noncomputable def SmoothedOutput : Prop :=
  ∃ (σ C : ℝ) (N K Λ : ℕ → ℝ) (ν : ℕ → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) (E : ℕ → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)), 0 < σ ∧ 0 < C ∧ (∀ k, 2 ≤ N k) ∧ Filter.Tendsto N Filter.atTop Filter.atTop ∧ ((∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε) ∧ (∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, Λ k ≤ N k ^ ε) ∧ (∃ M D : ℕ, ∀ k, MeasureTheory.IsProbabilityMeasure (ν k) ∧ (∃ m : ℕ, (m : ℝ) ≤ N k ^ M ∧ ∃ (c : Fin m → ℝ) (i : Fin m → ℕ) (A : Fin m → Set (Fin 6 → ℝ)), (∀ j, 0 ≤ c j ∧ c j ≤ N k ^ M ∧ (i j : ℝ) ≤ N k ^ M ∧ (∃ m₀ : ℕ, (m₀ : ℝ) ≤ (N k ^ M) ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin 6) ℝ, (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool, ∀ x₀, x₀ ∈ (A j) ↔ b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true) ∧ (∀ x ∈ A j, ∀ b, |x b| ≤ N k ^ M)) ∧ ν k = ∑ j, (ENNReal.ofReal (c j)) • MeasureTheory.Measure.map (fun x => (i j, x)) (MeasureTheory.volume.restrict (A j))) ∧ MeasurableSet (E k) ∧ E k ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 ∧ (∀ p ∈ E k, (p.1.1 : ℝ) ≤ N k ^ M ∧ ∀ e, |p.1.2 e| ≤ N k ^ M) ∧ (∀ i, (∃ m₀ : ℕ, (m₀ : ℝ) ≤ (N k ^ M) ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin 7) ℝ, (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool, ∀ x₀, x₀ ∈ ({x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ (E k)}) ↔ b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true)) ∧ (∀ᵐ l ∂(ν k), ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(WithLp.toLp 2 ![![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 1, ![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 2])‖ + ‖(WithLp.toLp 2 ![l.2 3, l.2 4])‖ ≤ K k ∧ |![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 3| ≤ K k) ∧ ENNReal.ofReal ((K k)⁻¹) ≤ (((ν k).prod MeasureTheory.volume).restrict (E k)) Set.univ) ∧ (∀ k (Z : Set (EuclideanSpace ℝ (Fin 3))), (ν k) {l | (WithLp.toLp 2 ![l.2 3, l.2 4, l.2 5] : EuclideanSpace ℝ (Fin 3)) ∈ Z} ≤ ENNReal.ofReal (Λ k) * MeasureTheory.volume Z) ∧ (∀ k, ∃ (m : ℕ) (z : Fin m → EuclideanSpace ℝ (Fin 4)), (m : ℝ) ≤ C * N k ^ (4 - σ) ∧ ∀ p ∈ E k, ∃ j : Fin m, ‖(WithLp.toLp 2 ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] : EuclideanSpace ℝ (Fin 4)) - z j‖ ≤ C / N k) ∧ (∀ k (t : ℝ) (S T : Set (EuclideanSpace ℝ (Fin 2))), t ∈ Set.Icc (0 : ℝ) 1 → (ν k) {l | (WithLp.toLp 2 ![![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 1, ![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 2] : EuclideanSpace ℝ (Fin 2)) ∈ S ∧ (WithLp.toLp 2 ![l.2 3, l.2 4] : EuclideanSpace ℝ (Fin 2)) ∈ T} ≤ ENNReal.ofReal (Λ k * N k ^ 2) * MeasureTheory.volume S * MeasureTheory.volume T) ∧ (∀ α : ℝ, 0 < α → ∃ θ : ℝ, 0 < θ ∧ ∀ᶠ k in Filter.atTop, ∀ U : Set (EuclideanSpace ℝ (Fin 3)), MeasureTheory.volume U ≤ ENNReal.ofReal (N k ^ (-α)) → ((ν k).prod MeasureTheory.volume) {p | p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ (WithLp.toLp 2 ![p.2, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 1, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 2] : EuclideanSpace ℝ (Fin 3)) ∈ U} ≤ ENNReal.ofReal (N k ^ (-θ)))

theorem output_of_bad_sequence {σ c R : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hR : 1 ≤ R)
    (κ : ℕ → ℕ) (hκ : ∀ j, 1 ≤ κ j ∧ j ≤ κ j)
    (hlarge : ∀ j, 2 ≤ scale (κ j) ∧ c + 1 ≤ scale (κ j) ∧ R + 3 ≤ scale (κ j))
    (A : (j : ℕ) → BadConfiguration c R σ (κ j))
    (hspread : ∀ α : ℝ, 0 < α → ∃ θ : ℝ, 0 < θ ∧ ∀ᶠ j in atTop,
      ∀ U : Set (EuclideanSpace ℝ (Fin 3)), volume U ≤ ENNReal.ofReal (scale (κ j) ^ (-α)) →
        ((configurationPrior (A j)).prod volume)
          {p | p.2 ∈ Icc (0 : ℝ) 1 ∧ baseObservation p ∈ U} ≤
            ENNReal.ofReal (scale (κ j) ^ (-θ))) : SmoothedOutput := by
  have ht : Tendsto κ atTop atTop := tendsto_atTop_mono (fun j => (hκ j).2) tendsto_id
  refine ⟨σ, 16, (fun j => scale (κ j)), (fun j => nativeFactor c R (κ j)),
    (fun j => slopeFactor c (κ j)), (fun j => configurationPrior (A j)),
    (fun j => configurationEvent (A j)), hσ, (by norm_num),
    (fun j => (hlarge j).1), tendsto_scales_of_ge κ (fun j => (hκ j).2), ?_, ?_,
    ⟨32, 4, ?_⟩, ?_, ?_, ?_, hspread⟩
  · exact ⟨fun j => (nativeFactor_ge hc hR (κ j)).1,
      poly_subpower_of_tendsto ht (normalizationFactor c R) (normalizationFactor_pos hc hR).le 2⟩
  · exact poly_subpower_of_tendsto ht (46656 / c) (by positivity) 2
  · intro j
    exact configuration_tempered hc hR hσ (hlarge j).1 (hlarge j).2.1 (hlarge j).2.2 (A j)
  · intro j Z
    exact configuration_slope_ceiling hc (A j) Z
  · intro j
    exact ⟨(A j).m, (A j).z, (configuration_cover hσ (A j)).1,
      (configuration_cover hσ (A j)).2⟩
  · intro j t S T ht
    exact configuration_joint_ceiling hc hR (A j) t S T

end Submission.Obl.k4_dk4_smoothed_problem
