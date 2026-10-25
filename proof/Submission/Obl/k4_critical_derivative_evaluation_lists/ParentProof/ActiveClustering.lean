/- Adapted from this LOT tree, obligation o211, session x0736,
   commit 83b764e828c02e4c2216b0015b1434127ef232e2, ActiveClustering.lean.
   Original source attributions below are retained. -/

import Submission.Obl.k4_plank_estimate
import Submission.Obl.k4_scalar_coefficient_clustering

/-! Adapted from our LOT tree o107 (`k4_finite_narrowness_path_improvement`), session x0353,
`ActiveClustering.lean` (commit 96bcaa7b); namespace and import paths renamed. -/

/-! Scalar clustering returns heavy bins in original active incidence units. -/

namespace Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof

noncomputable section

open MeasureTheory Set
open scoped ENNReal

theorem product_mass_ge_long_prior_floor {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (E : Set (α × ℝ)) (hE : MeasurableSet E)
    (S : Set α) (hS : MeasurableSet S) (τ m : ℝ≥0∞)
    (hfloor : m ≤ ν {l | l ∈ S ∧ τ ≤ volume {t : ℝ | (l, t) ∈ E}}) :
    τ * m ≤ (ν.prod volume) (E ∩ (S ×ˢ Set.univ)) := by
  let T : Set α := {l | l ∈ S ∧ τ ≤ volume {t : ℝ | (l, t) ∈ E}}
  have hT : MeasurableSet T := hS.inter
    (measurableSet_le measurable_const (measurable_measure_prodMk_left hE))
  calc
    _ ≤ τ * ν T := mul_le_mul_of_nonneg_left hfloor (zero_le : (0 : ℝ≥0∞) ≤ τ)
    _ = ∫⁻ l, T.indicator (fun _ => τ) l ∂ν := (lintegral_indicator_const hT _).symm
    _ ≤ (ν.prod volume) (E ∩ (S ×ˢ Set.univ)) := by
      rw [Measure.prod_apply (hE.inter (hS.prod MeasurableSet.univ))]
      apply lintegral_mono
      intro l
      by_cases hl : l ∈ T
      · rw [Set.indicator_of_mem hl]
        have hpre : Prod.mk l ⁻¹' (E ∩ (S ×ˢ Set.univ)) = Prod.mk l ⁻¹' E := by
          ext t
          simp only [mem_preimage, mem_inter_iff, mem_prod, mem_univ, and_true]
          exact and_iff_left hl.1
        change τ ≤ volume (Prod.mk l ⁻¹' (E ∩ (S ×ˢ Set.univ)))
        rw [hpre]
        exact hl.2
      · rw [Set.indicator_of_notMem hl]
        exact zero_le

/-- The duration supplied by accepted scalar clustering converts its prior
floor to a floor on the original active incidences in the same full-time bin. -/
theorem scalar_clustering_active_bin (d c ε : ℝ)
    (hd : 0 ≤ d) (hd1 : d < 1) (hc : 0 < c) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ (α : Type) [MeasurableSpace α] (ν : Measure α)
        (a : α → EuclideanSpace ℝ (Fin 3)) (E : Set (α × ℝ)) (F : Finset (ℤ × ℤ)),
      Measurable a → MeasurableSet E → E ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 →
      (∀ l, ‖a l‖ ≤ N ^ η) → ν Set.univ ≤ ENNReal.ofReal (N ^ η) →
      ENNReal.ofReal (N ^ (-η)) ≤ (ν.prod volume) E →
      (F.card : ℝ) ≤ N ^ η * (N ^ (-c)) ^ (-1 - d) →
      (∀ l t, (l, t) ∈ E →
        (⌊t / (N ^ (-c))⌋, ⌊(a l 0 + t * a l 1 + t ^ 2 * a l 2) / (N ^ (-c))⌋) ∈ F) →
      (∀ (b : EuclideanSpace ℝ (Fin 3)) (r : ℝ), N ^ (-c) ≤ r →
        ν {l | a l ∈ Metric.ball b r} ≤ ENNReal.ofReal (N ^ η * r ^ d)) →
      ∃ q : Fin 3 → ℤ,
        ENNReal.ofReal (N ^ (-c * d - ε)) ≤
          (ν.prod volume) (E ∩ ({l | ∀ j : Fin 3, ⌊a l j / (N ^ (-c))⌋ = q j} ×ˢ Set.univ)) := by
  obtain ⟨η, hη, N₀, hN₀, hcluster⟩ :=
    Submission.k4_scalar_coefficient_clustering Submission.k4_plank_estimate
      d c (ε / 2) hd hd1 hc (by positivity)
  refine ⟨η, hη, N₀, hN₀, ?_⟩
  intro N hN α _ ν a E F ha hE hunit hnorm hν hmass hcard hsupport hcap
  obtain ⟨q, hq⟩ := hcluster N hN α ν a E F ha hE hunit hnorm hν hmass hcard hsupport hcap
  have hS : MeasurableSet {l | ∀ j : Fin 3, ⌊a l j / (N ^ (-c))⌋ = q j} := by
    measurability
  have hprod := product_mass_ge_long_prior_floor ν E hE _ hS
    (ENNReal.ofReal (N ^ (-(ε / 2)))) (ENNReal.ofReal (N ^ (-c * d - ε / 2))) hq
  refine ⟨q, ?_⟩
  convert hprod using 1
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith : 0 ≤ N) _),
    ← Real.rpow_add (by linarith : 0 < N)]
  congr 2
  ring

end

end Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof
