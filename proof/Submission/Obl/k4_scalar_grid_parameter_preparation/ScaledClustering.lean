/- Adapted from this LOT tree, o092, session x0317, commit d881f97f20e4.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/ScaledClustering.lean -/
import Submission.Obl.k4_scalar_grid_parameter_preparation.ClusteringSmallBins

/-! Apply clustering with an unchanged original palette factor, without probability normalization. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

open Set MeasureTheory
open scoped ENNReal

theorem small_coefficient_bins_force_small_original_occupation (d ε : ℝ)
    (hd : 0 ≤ d) (hd₁ : d < 1) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
      ∀ N : ℝ, N₀ ≤ N → ∀ (X : Type) [MeasurableSpace X] (ν : Measure X)
        (a : X → EuclideanSpace ℝ (Fin 3)) (E : Set (X × ℝ)) (F : Finset (ℤ × ℤ))
        (p : ℝ≥0∞), p ≠ 0 → p ≠ ∞ →
        Measurable a → MeasurableSet E → E ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 →
        (∀ l, ‖a l‖ ≤ N ^ η) → ν Set.univ ≤ p * ENNReal.ofReal (N ^ η) →
        (F.card : ℝ) ≤ N ^ η * (N ^ (-1 : ℝ)) ^ (-1 - d) →
        (∀ l t, (l,t) ∈ E →
          (⌊t / N ^ (-1 : ℝ)⌋,⌊(a l 0 + t * a l 1 + t ^ 2 * a l 2) / N ^ (-1 : ℝ)⌋) ∈ F) →
        (∀ (b : EuclideanSpace ℝ (Fin 3)) (r : ℝ), N ^ (-1 : ℝ) ≤ r →
          ν {l | a l ∈ Metric.ball b r} ≤ p * ENNReal.ofReal (N ^ η * r ^ d)) →
        (∀ q : Fin 3 → ℤ, ν {l | ∀ j : Fin 3, (⌊a l j / N ^ (-1 : ℝ)⌋ : ℤ) = q j} <
          p * ENNReal.ofReal (N ^ (-d - ε))) →
        (ν.prod volume) E < p * ENNReal.ofReal (N ^ (-η)) := by
  obtain ⟨η,hη,N₀,hN₀,hclust⟩ := small_coefficient_bins_force_small_occupation d ε hd hd₁ hε
  refine ⟨η,hη,N₀,hN₀,?_⟩
  intro N hN X _ ν a E F p hp₀ hpt ha hE hunit hnorm htotal hsize hcover hball hbin
  let ν' : Measure X := p⁻¹ • ν
  have hcancel (z : ℝ≥0∞) : p⁻¹ * (p * z) = z := by
    rw [← mul_assoc,ENNReal.inv_mul_cancel hp₀ hpt,one_mul]
  have htotal' : ν' Set.univ ≤ ENNReal.ofReal (N ^ η) := by
    change p⁻¹ * ν Set.univ ≤ _
    exact (mul_le_mul' le_rfl htotal).trans_eq (hcancel _)
  have hball' (b : EuclideanSpace ℝ (Fin 3)) (r : ℝ) (hr : N ^ (-1 : ℝ) ≤ r) :
      ν' {l | a l ∈ Metric.ball b r} ≤ ENNReal.ofReal (N ^ η * r ^ d) := by
    change p⁻¹ * ν {l | a l ∈ Metric.ball b r} ≤ _
    exact (mul_le_mul' le_rfl (hball b r hr)).trans_eq (hcancel _)
  have hbin' (q : Fin 3 → ℤ) :
      ν' {l | ∀ j : Fin 3, (⌊a l j / N ^ (-1 : ℝ)⌋ : ℤ) = q j} < ENNReal.ofReal (N ^ (-d - ε)) := by
    have hh := ENNReal.mul_lt_mul_right (ENNReal.inv_ne_zero.mpr hpt) (ENNReal.inv_ne_top.mpr hp₀) (hbin q)
    change p⁻¹ * ν {l | ∀ j : Fin 3, (⌊a l j / N ^ (-1 : ℝ)⌋ : ℤ) = q j} < _
    exact hh.trans_eq (hcancel _)
  have hh := hclust N hN X ν' a E F ha hE hunit hnorm htotal' hsize hcover hball' hbin'
  have hfinal := ENNReal.mul_lt_mul_right hp₀ hpt hh
  simpa only [ν',Measure.prod_smul_left,Measure.smul_apply,smul_eq_mul,← mul_assoc,
    ENNReal.mul_inv_cancel hp₀ hpt,one_mul] using hfinal

end Submission.Obl.k4_scalar_grid_parameter_preparation
