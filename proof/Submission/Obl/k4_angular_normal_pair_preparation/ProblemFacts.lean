import Submission.Obl.k4_angular_normal_pair_preparation.Definitions
import Submission.Obl.k4_horizon_chart_assembly.NativeGeometry

namespace Submission.Obl.k4_angular_normal_pair_preparation

open MeasureTheory Filter
open scoped ENNReal BigOperators

/-- Precisely the finite original-law facts used in normal pruning. -/
structure SampleFacts (Wk : ℕ) (ωk : Fin Wk → ℝ)
    (νk : Fin Wk → Measure (ℕ × (Fin 6 → ℝ)))
    (Ek : Fin Wk → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (Bk : Fin Wk → ℝ) : Prop where
  weight_nonneg : ∀ γ₀, 0 ≤ ωk γ₀
  weight_sum : ∑ γ₀, ωk γ₀ = 1
  prior_prob : ∀ γ₀, IsProbabilityMeasure (νk γ₀)
  scale_pos : ∀ γ₀, 0 < Bk γ₀
  event_meas : ∀ γ₀, MeasurableSet (Ek γ₀)
  event_time : ∀ γ₀, Ek γ₀ ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1

section Problem

variable {N K : ℕ → ℝ} {L d S η : ℝ} {W : ℕ → ℕ}
    {ω : (k : ℕ) → Fin (W k) → ℝ}
    {ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 6 → ℝ))}
    {E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ}
    {B : (k : ℕ) → Fin (W k) → ℝ} {f : ℝ → ℝ}
    {g : (k : ℕ) → Fin (W k) → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal}
    {G : (k : ℕ) → Fin (W k) → ℝ →
      ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal}

variable (hp : prob N K L d S η W ω ν E P B f g G)

include hp

theorem prob_N_ge (k : ℕ) : 2 ≤ N k := hp.1 k

theorem prob_N_tendsto : Tendsto N atTop atTop := hp.2.1

/-- Extract the finite facts once, keeping the original world laws and weights. -/
theorem prob_sampleFacts (k : ℕ) : SampleFacts (W k) (ω k) (ν k) (E k) (B k) := by
  obtain ⟨M, D, hs⟩ := hp.2.2.2.2.2.2.2.2.1
  have hw γ₀ := (hs k).2.2.2.1 γ₀
  exact {
    weight_nonneg := (hs k).2.1
    weight_sum := (hs k).2.2.1
    prior_prob := fun γ₀ => (hw γ₀).1
    scale_pos := fun γ₀ => (hw γ₀).2.1
    event_meas := fun γ₀ => (hw γ₀).2.2.2.2.2.2.2.1
    event_time := fun γ₀ => (hw γ₀).2.2.2.2.2.2.2.2.1 }

/-- The stated joint density is the density of the unchanged selected incidence law. -/
theorem prob_angular_law (k : ℕ) (γ₀ : Fin (W k)) (u : ℝ)
    (hu : 0 < u) (huL : u ≤ η * L) :
    Measurable (G k γ₀ u) ∧
      Measure.map (fun p : ((ℕ × (Fin 6 → ℝ)) × ℝ) =>
        (obs (B k γ₀) (δ (N k) L) p, fun j : Fin 2 => ⌊v p.1 j / δ (N k) u⌋))
        (((ν k γ₀).prod volume).restrict (E k γ₀)) =
      ((volume.prod Measure.count).prod Measure.count).withDensity (G k γ₀ u) :=
  hp.2.2.2.2.2.2.2.2.2.2.1 k γ₀ u hu huL

end Problem

/-- Positivity and both quantitative comparisons for the actual frozen dyadic width. -/
theorem delta_bounds {N : ℝ} (hN : 0 < N) (r : ℝ) :
    0 < δ N r ∧ N ^ (-r) ≤ δ N r ∧ δ N r ≤ 2 * N ^ (-r) := by
  have hb := Submission.Obl.k4_horizon_chart_assembly.resolution_bounds hN r
  exact ⟨(Real.rpow_pos_of_pos hN _).trans_le hb.1, hb⟩

end Submission.Obl.k4_angular_normal_pair_preparation
