/- Adapted from this LOT tree, o092, session x0317, commit d881f97f20e4.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/ClusteringSmallBins.lean -/
import Submission.Obl.k4_scalar_coefficient_clustering
import Submission.Obl.k4_plank_estimate

/-! The accepted plank and scalar clustering theorems exclude heavy occupation by light bins. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

open Set MeasureTheory
open scoped ENNReal

theorem small_coefficient_bins_force_small_occupation (d ε : ℝ)
    (hd : 0 ≤ d) (hd₁ : d < 1) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
      ∀ N : ℝ, N₀ ≤ N → ∀ (X : Type) [MeasurableSpace X] (ν : Measure X)
        (a : X → EuclideanSpace ℝ (Fin 3)) (E : Set (X × ℝ)) (F : Finset (ℤ × ℤ)),
        Measurable a → MeasurableSet E → E ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 →
        (∀ l, ‖a l‖ ≤ N ^ η) → ν Set.univ ≤ ENNReal.ofReal (N ^ η) →
        (F.card : ℝ) ≤ N ^ η * (N ^ (-1 : ℝ)) ^ (-1 - d) →
        (∀ l t, (l,t) ∈ E →
          (⌊t / N ^ (-1 : ℝ)⌋,⌊(a l 0 + t * a l 1 + t ^ 2 * a l 2) / N ^ (-1 : ℝ)⌋) ∈ F) →
        (∀ (b : EuclideanSpace ℝ (Fin 3)) (r : ℝ), N ^ (-1 : ℝ) ≤ r →
          ν {l | a l ∈ Metric.ball b r} ≤ ENNReal.ofReal (N ^ η * r ^ d)) →
        (∀ q : Fin 3 → ℤ, ν {l | ∀ j : Fin 3, (⌊a l j / N ^ (-1 : ℝ)⌋ : ℤ) = q j} <
          ENNReal.ofReal (N ^ (-d - ε))) →
        (ν.prod volume) E < ENNReal.ofReal (N ^ (-η)) := by
  obtain ⟨η,hη,N₀,hN₀,hclust⟩ := Submission.k4_scalar_coefficient_clustering
    Submission.k4_plank_estimate d 1 ε hd hd₁ (by norm_num) hε
  refine ⟨η,hη,N₀,hN₀,?_⟩
  intro N hN X _ ν a E F ha hE hunit hnorm htotal hsize hcover hball hbin
  by_contra hsmall
  have hinc : ENNReal.ofReal (N ^ (-η)) ≤ (ν.prod volume) E := le_of_not_gt hsmall
  obtain ⟨q,hq⟩ := hclust N hN X ν a E F ha hE hunit hnorm htotal hinc hsize hcover hball
  have hlarge : ENNReal.ofReal (N ^ (-d - ε)) ≤
      ν {l | ∀ j : Fin 3, (⌊a l j / N ^ (-1 : ℝ)⌋ : ℤ) = q j} := by
    apply le_trans (by simpa only [neg_one_mul] using hq)
    exact measure_mono fun l hl => hl.1
  exact (not_lt_of_ge hlarge) (hbin q)

end Submission.Obl.k4_scalar_grid_parameter_preparation
