-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
-- Adapted from this LOT tree, o107, session x0735, commit 334b24fb.
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/PolynomialDensityImage.lean.
-- Only the namespace and own-module import prefix are changed here.
-- From this same obligation, x0734, commit bcc5fc2c; power rewrite repaired by x0735.
import Submission.Obl.k4_finite_affine_parent_sources.SignalUpgrade.PolynomialDensityCalibration

/-! Calibration on a measurable image of the unchanged original law. -/

namespace Submission.Obl.k4_finite_affine_parent_sources.SignalUpgrade

open MeasureTheory Filter Set
open scoped ENNReal

/-- The polynomial density calibration is uniform before the original law,
its measurable base coordinates and the polynomial are chosen. -/
theorem polynomial_density_original_grid_calibration (B : ℝ) (hB : 0 ≤ B) :
    ∃ a M N₀ : ℝ, 0 < a ∧ 1 ≤ M ∧ 2 ≤ N₀ ∧
      ∀ N K β m E : ℝ, N₀ ≤ N → 1 ≤ K → K ≤ N →
        0 < β → 0 < m → β / m ≤ N ^ B → 0 ≤ E →
        ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
          (Z : Ω → Fin 3 → ℝ), Measurable Z →
          ENNReal.ofReal m ≤ μ univ →
          (∀ q : Fin 3 → ℤ, μ {p | (fun i => ⌊Z p i / N ^ (-a)⌋) = q} ≤
            ENNReal.ofReal (β * (N ^ (-a)) ^ (3 : ℕ))) →
          ∀ G : MvPolynomial (Fin 3) ℝ, G.totalDegree ≤ 2 →
            (∀ᵐ p ∂μ, (∀ i, |Z p i| ≤ K) ∧ |MvPolynomial.eval (Z p) G| ≤ E) →
            ∀ e, |G.coeff e| ≤ N ^ M * E := by
  obtain ⟨a, M, N₀, ha, hM, hN₀, hcal⟩ := polynomial_density_grid_calibration B hB
  refine ⟨a, M, N₀, ha, hM, hN₀, ?_⟩
  intro N K β m E hN hK hKN hβ hm hratio hE Ω _ μ _ Z hZ hmass hcap G hG hgood e
  have hgrid : Measurable (fun z : Fin 3 → ℝ => fun i => ⌊z i / N ^ (-a)⌋ :
      (Fin 3 → ℝ) → Fin 3 → ℤ) := by fun_prop
  have hmapmass : ENNReal.ofReal m ≤ (μ.map Z) univ := by
    simpa only [Measure.map_apply hZ MeasurableSet.univ, preimage_univ] using hmass
  have hmapcap (q : Fin 3 → ℤ) :
      (μ.map Z) {z | (fun i => ⌊z i / N ^ (-a)⌋) = q} ≤
        ENNReal.ofReal (β * (N ^ (-a)) ^ (3 : ℕ)) := by
    have hset : MeasurableSet {z : Fin 3 → ℝ | (fun i => ⌊z i / N ^ (-a)⌋) = q} :=
      measurableSet_eq_fun hgrid measurable_const
    rw [Measure.map_apply hZ hset]
    exact hcap q
  have hmapgood : ∀ᵐ z ∂μ.map Z,
      (∀ i, |z i| ≤ K) ∧ |MvPolynomial.eval z G| ≤ E := by
    have hset : MeasurableSet {z : Fin 3 → ℝ |
        (∀ i, |z i| ≤ K) ∧ |MvPolynomial.eval z G| ≤ E} := by
      have heq : {z : Fin 3 → ℝ |
          (∀ i, |z i| ≤ K) ∧ |MvPolynomial.eval z G| ≤ E} =
          (⋂ i : Fin 3, {z : Fin 3 → ℝ | |z i| ≤ K}) ∩
          {z : Fin 3 → ℝ | |MvPolynomial.eval z G| ≤ E} := by ext z; simp
      rw [heq]
      exact (MeasurableSet.iInter fun i => measurableSet_le
        (show Measurable (fun z : Fin 3 → ℝ => |z i|) by fun_prop) measurable_const).inter
        (measurableSet_le (G.continuous_eval.abs.measurable) measurable_const)
    exact (ae_map_iff hZ.aemeasurable hset).mpr hgood
  exact hcal N K β m E hN hK hKN hβ hm hratio hE (μ.map Z)
    inferInstance hmapmass hmapcap G hG hmapgood e

end Submission.Obl.k4_finite_affine_parent_sources.SignalUpgrade
