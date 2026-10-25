/- Adapted from this LOT tree, obligation o119, session x0404, commit b1aa67e,
   Submission/Obl/k4_finite_width_critical_contradiction/CompEncAe.lean. -/
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.CompDyadic
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.CompWorldsFormat

/-!
# Almost-everywhere facts for the encoded prior

`encTraj` is a measurable embedding, so almost-everywhere properties of the world priors
transfer to the encoded prior; the encoded prior of a probability family is a probability
measure; the encoded hidden coordinate is small when the scale `σ` is small.
-/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder.Comp

attribute [local simp] encCoeff_zero encCoeff_one encCoeff_two encCoeff_three encCoeff_four encCoeff_five

open MeasureTheory Set
open scoped ENNReal

theorem measurableEmbedding_encTraj {W : ℕ} (hW : 0 < W) (c : ℕ) {b : ℝ} (hb : b ≠ 0) (o : ℝ) :
    MeasurableEmbedding (encTraj W c b o) := by
  have hinj : Function.Injective (fun i : ℕ => W * i + c) := by
    intro i j h
    simp only at h
    have := Nat.eq_of_mul_eq_mul_left hW (Nat.add_right_cancel h)
    exact this
  have h1' : MeasurableEmbedding (fun i : ℕ => W * i + c) :=
    { injective := hinj
      measurable := measurable_of_countable _
      measurableSet_image' := fun s _ => (Set.to_countable _).measurableSet }
  exact h1'.prodMap (encHomeomorph hb o).toMeasurableEquiv.measurableEmbedding

/-- An a.e. property of every world prior, read through the encoding, holds a.e. for the
encoded prior. -/
theorem ae_encPrior {W : ℕ} (hW : 0 < W) (a b o : Fin W → ℝ) (hb : ∀ c, b c ≠ 0)
    (ν : Fin W → Measure Traj) {P : Traj → Prop}
    (h : ∀ c : Fin W, ∀ᵐ l ∂(ν c), P (encTraj W c (b c) (o c) l)) :
    ∀ᵐ l ∂(encPrior W a b o ν), P l := by
  unfold encPrior
  rw [ae_iff, Measure.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [Measure.smul_apply]
  have hc := h c
  rw [← (measurableEmbedding_encTraj hW c (hb c) (o c)).ae_map_iff] at hc
  rw [ae_iff] at hc
  rw [hc, smul_zero]

theorem encPrior_isProbability {W : ℕ} (a b o : Fin W → ℝ) (ha : ∀ c, 0 ≤ a c)
    (hsum : ∑ c, a c = 1) (ν : Fin W → Measure Traj) (hν : ∀ c, IsProbabilityMeasure (ν c)) :
    IsProbabilityMeasure (encPrior W a b o ν) := by
  constructor
  unfold encPrior
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  have : ∀ c : Fin W, (Measure.map (encTraj W c (b c) (o c)) (ν c)) univ = 1 := by
    intro c
    rw [Measure.map_apply (measurable_encTraj _ _ _ _) MeasurableSet.univ, preimage_univ]
    exact measure_univ
  simp only [this, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun c _ => ha c), hsum, ENNReal.ofReal_one]

end Submission.Obl.k4_native_calibrated_homogeneous_remainder.Comp
