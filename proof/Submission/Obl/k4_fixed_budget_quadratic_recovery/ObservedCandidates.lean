import Submission.Obl.k4_fixed_budget_quadratic_recovery.PairMarginal
import Submission.Obl.k4_fixed_budget_quadratic_recovery.Coefficients

noncomputable section

namespace Submission.Obl.k4_fixed_budget_quadratic_recovery

open MeasureTheory Set

/-- Changing the base on an input-null set preserves the original index marginal. -/
theorem scalarFit_observed_marginal_cap_power
    {X : Type*} {N η d s m S U δ : ℝ}
    (hN : 1 ≤ N) (hs : 0 ≤ s) (hδ : 0 ≤ δ)
    {ν : Measure (ℕ × (Fin 6 → ℝ))}
    {μ : Measure ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {b : (ℕ × (Fin 6 → ℝ)) → Fin 5 → ℝ}
    (hlaw : ProjectedScalarLaw N η d s m S U ν μ b)
    (O : ((ℕ × (Fin 6 → ℝ)) × ℝ) → X)
    (base : X → EuclideanSpace ℝ (Fin 2))
    (hbase : ∀ᵐ p ∂μ, base (O p) = scalarBase b p)
    (P : MvPolynomial (Fin 2) ℝ) (A : Set (Fin 5 → ℝ))
    (hA : A ⊆ scalarFit P (N ^ δ * N ^ (-s)))
    (E : Set (ℝ × ℝ)) (hE : MeasurableSet E) :
    μ {p | b p.1 ∈ A ∧ ((base (O p)) 0, (base (O p)) 1) ∈ E} ≤
      ENNReal.ofReal (7 * N ^ (η + δ - d * s)) * volume E := by
  apply le_trans _ (scalarFit_pair_marginal_cap_power hN hs hδ hlaw P A hA E hE)
  apply measure_mono_ae
  filter_upwards [hbase] with p hp
  intro h
  rwa [hp] at h

/-- The input signal and a full-time scalar fit give agreement at the supplied
original observation, with only the two stated error terms. -/
theorem scalarFit_observed_samples
    {X : Type*} {N η d s m S U error τ : ℝ}
    {ν : Measure (ℕ × (Fin 6 → ℝ))}
    {μ : Measure ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {b : (ℕ × (Fin 6 → ℝ)) → Fin 5 → ℝ}
    (hlaw : ProjectedScalarLaw N η d s m S U ν μ b)
    (O : ((ℕ × (Fin 6 → ℝ)) × ℝ) → X)
    (base : X → EuclideanSpace ℝ (Fin 2)) (signal : X → ℝ)
    (hobs : ∀ᵐ p ∂μ, base (O p) = scalarBase b p ∧
      |scalarX (b p.1) p.2 - signal (O p)| ≤ τ)
    {n : ℕ} (P : Fin n → MvPolynomial (Fin 2) ℝ)
    (c : Fin n → Fin 6 → ℝ)
    (hc : ∀ i t y, MvPolynomial.eval ![t, y] (P i) = quadraticValue (c i) t y)
    (A : Fin n → Set (Fin 5 → ℝ)) (hA : ∀ i, A i ⊆ scalarFit (P i) error) :
    ∀ᵐ p ∂μ, ∀ i, b p.1 ∈ A i →
      (base (O p)) 0 ∈ Icc (0 : ℝ) 1 ∧ |(base (O p)) 1| ≤ 2 * N ^ η ∧
      |signal (O p) - quadraticValue (c i) ((base (O p)) 0) ((base (O p)) 1)| ≤
        error + τ := by
  have htime : ∀ᵐ p ∂μ, p.2 ∈ Icc (0 : ℝ) 1 := by
    rw [ae_iff]
    have heq : {p : ((ℕ × (Fin 6 → ℝ)) × ℝ) | ¬p.2 ∈ Icc (0 : ℝ) 1} =
        (univ ×ˢ Icc (0 : ℝ) 1)ᶜ := by ext p; simp
    rw [heq]
    exact hlaw.1.2.2.2.1
  filter_upwards [hobs, htime] with p hp ht
  intro i hi
  rw [hp.1]
  refine ⟨ht, scalarY_bound_of_box (hlaw.1.2.2.2.2.1 p.1) ht, ?_⟩
  change |signal (O p) - quadraticValue (c i) p.2 (scalarY (b p.1) p.2)| ≤ _
  rw [← hc]
  calc
    _ ≤ |signal (O p) - scalarX (b p.1) p.2| +
        |scalarX (b p.1) p.2 - MvPolynomial.eval ![p.2, scalarY (b p.1) p.2] (P i)| :=
      abs_sub_le _ _ _
    _ ≤ τ + error := by
      apply add_le_add
      · simpa only [abs_sub_comm] using hp.2
      · exact hA i hi p.2 ht
    _ = _ := add_comm _ _

end Submission.Obl.k4_fixed_budget_quadratic_recovery
