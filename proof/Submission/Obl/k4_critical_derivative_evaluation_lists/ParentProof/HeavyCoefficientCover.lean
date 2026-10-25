/- Adapted from this LOT tree, obligation o211, session x0736,
   commit 83b764e828c02e4c2216b0015b1434127ef232e2, HeavyCoefficientCover.lean.
   Original source attributions below are retained. -/

import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.ActiveClustering
import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.DenseCodeCover

/-! Adapted from our LOT tree o107 (`k4_finite_narrowness_path_improvement`), session x0353,
`HeavyCoefficientCover.lean` (commit 96bcaa7b); namespace and import paths renamed. -/

/-! Full-time coefficient bins cover every dense original incidence law. -/

namespace Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof

noncomputable section

open MeasureTheory Set
open scoped ENNReal Classical
open Submission.Obl.k4_scalar_coefficient_clustering

/-- Scalar clustering on each dense residual yields a full-time coefficient
cover. Floors and the excluded mass are measured in the ORIGINAL product law. -/
theorem scalar_heavy_coefficient_cover (d c ε : ℝ)
    (hd : 0 ≤ d) (hd1 : d < 1) (hc : 0 < c) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ (α : Type) [MeasurableSpace α] (ν : Measure α)
        (a : α → EuclideanSpace ℝ (Fin 3)) (E : Set (α × ℝ)) (F : Finset (ℤ × ℤ)),
      Measurable a → MeasurableSet E → E ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 →
      (∀ l, ‖a l‖ ≤ N ^ η) → ν Set.univ ≤ ENNReal.ofReal (N ^ η) →
      (F.card : ℝ) ≤ N ^ η * (N ^ (-c)) ^ (-1 - d) →
      (∀ l t, (l, t) ∈ E →
        (⌊t / (N ^ (-c))⌋, ⌊(a l 0 + t * a l 1 + t ^ 2 * a l 2) / (N ^ (-c))⌋) ∈ F) →
      (∀ (b : EuclideanSpace ℝ (Fin 3)) (r : ℝ), N ^ (-c) ≤ r →
        ν {l | a l ∈ Metric.ball b r} ≤ ENNReal.ofReal (N ^ η * r ^ d)) →
      ∃ G : Finset (Fin 3 → ℤ),
        (∀ q ∈ G, ENNReal.ofReal (N ^ (-c * d - ε)) ≤
          ((ν.prod volume).restrict E) {p | coefficientCode (N ^ (-c)) (a p.1) = q}) ∧
        (G.card : ℝ) ≤ (ν.prod volume).real E / N ^ (-c * d - ε) ∧
        ((ν.prod volume).restrict E) {p | coefficientCode (N ^ (-c)) (a p.1) ∉ G} <
          ENNReal.ofReal (N ^ (-η)) := by
  obtain ⟨η, hη, N₀, hN₀, hcluster⟩ := scalar_clustering_active_bin d c ε hd hd1 hc hε
  refine ⟨η, hη, N₀, hN₀, ?_⟩
  intro N hN α _ ν a E F ha hE hunit hnorm hν hcard hsupport hcap
  have hNpos : 0 < N := by linarith
  let μ := (ν.prod volume).restrict E
  have hνfinite : ν Set.univ < ∞ := lt_of_le_of_lt hν (ENNReal.ofReal_lt_top)
  letI : IsFiniteMeasure ν := ⟨hνfinite⟩
  letI : IsFiniteMeasure μ := ⟨by
    change ((ν.prod volume).restrict E) Set.univ < ∞
    rw [Measure.restrict_apply_univ]
    refine lt_of_le_of_lt (measure_mono hunit) ?_
    simp only [Measure.prod_prod, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one]
    exact hνfinite⟩
  let code : α × ℝ → Fin 3 → ℤ := fun p => coefficientCode (N ^ (-c)) (a p.1)
  have hcode : Measurable code :=
    ((measurable_coefficientCode _).comp ha).comp measurable_fst
  have hcodes := coefficient_codes_finite a Set.univ (p := N ^ (-c)) (Real.rpow_pos_of_pos hNpos _)
    (fun l _ => hnorm l)
  let C := hcodes.toFinset
  have hcover : ∀ᵐ p ∂μ, code p ∈ C := by
    apply Filter.Eventually.of_forall
    intro p
    exact hcodes.mem_toFinset.mpr ⟨p.1, Set.mem_univ _, rfl⟩
  have hdiscover : ∀ U : Set (α × ℝ), MeasurableSet U →
      ENNReal.ofReal (N ^ (-η)) ≤ μ U →
      ∃ q : Fin 3 → ℤ, ENNReal.ofReal (N ^ (-c * d - ε)) ≤ μ (U ∩ code ⁻¹' {q}) := by
    intro U hU hmass
    have hinc : ENNReal.ofReal (N ^ (-η)) ≤ (ν.prod volume) (E ∩ U) := by
      simpa only [μ, Measure.restrict_apply hU, Set.inter_comm] using hmass
    obtain ⟨q, hq⟩ := hcluster N hN α ν a (E ∩ U) F ha (hE.inter hU)
      (Set.inter_subset_left.trans hunit) hnorm hν hinc hcard
      (fun l t hlt => hsupport l t hlt.1) hcap
    refine ⟨q, ?_⟩
    have hsame : μ (U ∩ code ⁻¹' {q}) = (ν.prod volume)
        ((E ∩ U) ∩ ({l | ∀ j : Fin 3, ⌊a l j / (N ^ (-c))⌋ = q j} ×ˢ Set.univ)) := by
      rw [show μ (U ∩ code ⁻¹' {q}) =
        (ν.prod volume) ((U ∩ code ⁻¹' {q}) ∩ E) from Measure.restrict_apply
          (hU.inter (hcode (measurableSet_singleton q)))]
      congr 1
      ext p
      simp only [code, coefficientCode, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_singleton_iff, Set.mem_prod, Set.mem_setOf_eq, Set.mem_univ, and_true,
        funext_iff]
      tauto
    rwa [hsame]
  obtain ⟨G, _, hfloor, hcount, hexcluded⟩ := finite_heavy_code_cover_of_dense_discovery μ code hcode C hcover
    (N ^ (-c * d - ε)) (ENNReal.ofReal (N ^ (-η))) (Real.rpow_pos_of_pos hNpos _) hdiscover
  refine ⟨G, hfloor, ?_, hexcluded⟩
  simpa only [μ, measureReal_restrict_apply_univ] using hcount

end

end Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof
