/- Adapted from this LOT tree, obligation o100, session x0340, commit efabdd9,
   Submission/Obl/k4_scalar_marked_profile_selection/RealBands.lean. -/
import Submission.Obl.k4_marked_scalar_grid_selection.Scalar.NodeWeights

noncomputable section

namespace Submission.Obl.k4_marked_scalar_grid_selection.Scalar

open MeasureTheory Set
open scoped ENNReal

/-- A real band on the old node values gives an exact density band with one
polynomial loss, uniformly over all versions of the selected density. -/
theorem selected_joint_real_band {H J : ℕ} (hJ : 0 < J) {σ a ρ K : ℝ}
    (hσ : 0 < σ) (hmesh : 1 ≤ (J : ℝ) * σ) (ha : σ ≤ a)
    (hρ : 0 < ρ) (hK : 1 ≤ K)
    (b : Fin H → Fin 5 → ℝ) (hb : ∀ j e, |b j e| ≤ K)
    (w : Fin H → ℝ) (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1)
    (I T : Finset (AtomIndex H J)) (hT : T ⊆ I)
    {lower upper ε : ℝ} (hε : 0 ≤ ε)
    (hfit : ∀ i ∈ T, lower ≤ realNodeMass I σ ρ w
      (fun i => atomRecord σ a (max σ ρ) b i.1 i.2)
      (atomRecord σ a (max σ ρ) b i.1 i.2) ∧
      realNodeMass I σ ρ w (fun i => atomRecord σ a (max σ ρ) b i.1 i.2)
        (atomRecord σ a (max σ ρ) b i.1 i.2) ≤ upper)
    (g : Canonical → ℝ≥0∞) (hg : Measurable g)
    (hglaw : (law σ H J b w (markOf T)).map (widthObservation a ρ) =
      canonicalReference.withDensity g) :
    law σ H J b w (markOf T)
      {p | g (widthObservation a ρ p) < ENNReal.ofReal (ε * lower) ∨
        ENNReal.ofReal (geometryLoss K * upper) < g (widthObservation a ρ p)} ≤
      ENNReal.ofReal (ε * geometryLoss K) := by
  classical
  have hK0 : 0 ≤ K := by linarith
  have hP : 0 ≤ geometryLoss K := by dsimp [geometryLoss]; positivity
  obtain ⟨f, hf, hflaw, hband⟩ := selected_joint_band hJ hσ hmesh ha hρ
    (le_max_left _ _) (le_max_right _ _) hK0 (le_refl (10 * (K + 1))) b hb w I T hT
    (ENNReal.ofReal lower) (ENNReal.ofReal upper) (ENNReal.ofReal ε) (by
      intro c hc
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hc
      rw [← ofReal_realNodeMass I hσ hρ.le w hw]
      exact ENNReal.ofReal_le_ofReal (hfit i hi).1) (by
      intro c hc
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hc
      rw [← ofReal_realNodeMass I hσ hρ.le w hw]
      exact ENNReal.ofReal_le_ofReal (hfit i hi).2)
  apply (measure_mono (show
      {p | g (widthObservation a ρ p) < ENNReal.ofReal (ε * lower) ∨
        ENNReal.ofReal (geometryLoss K * upper) < g (widthObservation a ρ p)} ⊆
      {p | g (widthObservation a ρ p) < ENNReal.ofReal ε * ENNReal.ofReal lower ∨
        ENNReal.ofReal (jointOverlapLoss (10 * (K + 1))) * ENNReal.ofReal upper <
          g (widthObservation a ρ p)} from ?_)).trans ((hband g hg hglaw).trans ?_)
  · intro p hp
    rcases hp with hp | hp
    · left
      simpa only [ENNReal.ofReal_mul hε] using hp
    · right
      apply lt_of_le_of_lt _ hp
      rw [ENNReal.ofReal_mul hP]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal (geometry_coefficients_le hK).2.1) le_rfl
  · rw [mul_assoc, ENNReal.ofReal_mul hε]
    exact mul_le_mul' le_rfl (joint_record_budget hJ hσ hρ hK w hw hw1 I)

/-- Pure windows use exactly the old unit-slope node masses from the joint
selection, with the same polynomial loss. -/
theorem selected_pure_real_band {H J : ℕ} (hJ : 0 < J) {σ a K : ℝ}
    (hσ : 0 < σ) (hσ₁ : σ ≤ 1) (hmesh : 1 ≤ (J : ℝ) * σ) (ha : σ ≤ a)
    (hK : 1 ≤ K) (b : Fin H → Fin 5 → ℝ) (hb : ∀ j e, |b j e| ≤ K)
    (w : Fin H → ℝ) (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1)
    (I T : Finset (AtomIndex H J)) (hT : T ⊆ I)
    {lower upper ε : ℝ} (hε : 0 ≤ ε)
    (hfit : ∀ i ∈ T, lower ≤ realNodeMass I σ 1 w
      (fun i => atomRecord σ a 1 b i.1 i.2) (atomRecord σ a 1 b i.1 i.2) ∧
      realNodeMass I σ 1 w (fun i => atomRecord σ a 1 b i.1 i.2)
        (atomRecord σ a 1 b i.1 i.2) ≤ upper)
    (g : ObsSpace → ℝ≥0∞) (hg : Measurable g)
    (hglaw : (law σ H J b w (markOf T)).map (pureWidthObservation a) = reference.withDensity g) :
    law σ H J b w (markOf T)
      {p | g (pureWidthObservation a p) < ENNReal.ofReal (ε * lower) ∨
        ENNReal.ofReal (geometryLoss K * upper) < g (pureWidthObservation a p)} ≤
      ENNReal.ofReal (ε * geometryLoss K) := by
  classical
  have hK0 : 0 ≤ K := by linarith
  have hP : 0 ≤ geometryLoss K := by dsimp [geometryLoss]; positivity
  have hweights : jointNodeWeight σ 1 w = pureNodeWeight (J := J) σ w :=
    funext (jointNodeWeight_one hσ hσ₁ w)
  obtain ⟨f, hf, hflaw, hband⟩ := selected_pure_band hJ hσ hσ₁ hmesh ha
    hK0 (le_refl (10 * (K + 1))) b hb w I T hT
    (ENNReal.ofReal lower) (ENNReal.ofReal upper) (ENNReal.ofReal ε) (by
      intro c hc
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hc
      rw [← hweights, ← ofReal_realNodeMass I hσ (by norm_num : (0 : ℝ) ≤ 1) w hw]
      exact ENNReal.ofReal_le_ofReal (hfit i hi).1) (by
      intro c hc
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hc
      rw [← hweights, ← ofReal_realNodeMass I hσ (by norm_num : (0 : ℝ) ≤ 1) w hw]
      exact ENNReal.ofReal_le_ofReal (hfit i hi).2)
  apply (measure_mono (show
      {p | g (pureWidthObservation a p) < ENNReal.ofReal (ε * lower) ∨
        ENNReal.ofReal (geometryLoss K * upper) < g (pureWidthObservation a p)} ⊆
      {p | g (pureWidthObservation a p) < ENNReal.ofReal ε * ENNReal.ofReal lower ∨
        ENNReal.ofReal (pureOverlapLoss K (10 * (K + 1))) * ENNReal.ofReal upper <
          g (pureWidthObservation a p)} from ?_)).trans ((hband g hg hglaw).trans ?_)
  · intro p hp
    rcases hp with hp | hp
    · left
      simpa only [ENNReal.ofReal_mul hε] using hp
    · right
      apply lt_of_le_of_lt _ hp
      rw [ENNReal.ofReal_mul hP]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal (geometry_coefficients_le hK).2.2.1) le_rfl
  · rw [mul_assoc, ENNReal.ofReal_mul hε]
    exact mul_le_mul' le_rfl (pure_record_budget hJ hσ hK w hw hw1 I)

end Submission.Obl.k4_marked_scalar_grid_selection.Scalar
