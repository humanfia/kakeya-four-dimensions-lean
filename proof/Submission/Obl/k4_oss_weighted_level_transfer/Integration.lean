import Submission.Obl.k4_oss_weighted_level_transfer.Reflection
import Submission.Obl.k4_oss_bad_direction_extraction.Energy

open MeasureTheory Set
open scoped BigOperators NNReal ENNReal

namespace Submission.Obl.k4_oss_weighted_level_transfer

attribute [local instance] Classical.propDecidable
attribute [local instance] counting_finite atomic_finite ofReal_dirac_finite

lemma measurable_finiteEnergy (A B : Finset ℝ) (δ : ℝ) :
    Measurable (fun t : ℝ => finiteEnergy δ t A B) :=
  Submission.Obl.k4_oss_bad_direction_extraction.measurable_energy A B δ

lemma ofReal_weighted_energy (w v E : ℝ) (hw : 0 ≤ w) (hv : 0 ≤ v) :
    (ENNReal.ofReal w * ENNReal.ofReal v) *
        (ENNReal.ofReal w * ENNReal.ofReal v) * ENNReal.ofReal E =
      ENNReal.ofReal (w ^ 2 * v ^ 2 * E) := by
  have h := ENNReal.ofReal_mul hw (q := v)
  calc
    _ = ENNReal.ofReal (w * v) * ENNReal.ofReal (w * v) * ENNReal.ofReal E := by rw [h]
    _ = ENNReal.ofReal ((w * v) * (w * v) * E) := by
      rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hw hv) (mul_nonneg hw hv)),
        ENNReal.ofReal_mul (mul_nonneg hw hv)]
    _ = _ := by congr 1; ring

lemma averaged_level_sum_le {I J : Type*} [Fintype I] [Fintype J]
    {δ : ℝ} (hδ : 0 < δ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (A : I → Finset ℝ) (B : J → Finset ℝ) (w : I → ℝ) (v : J → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ j, 0 ≤ v j)
    (hsep : ∀ i, ∀ x ∈ A i, ∀ y ∈ A i, x ≠ y → δ ≤ dist x y) :
    (∫⁻ t, collision (16 * δ)
        (projected t (∑ i, ENNReal.ofReal (w i) • counting (A i))
          (∑ j, ENNReal.ofReal (v j) • counting (B j))) ∂ν) ≤
      3 * (Fintype.card I * Fintype.card J : ℝ≥0∞) *
        ∑ i, ∑ j, ENNReal.ofReal (w i ^ 2 * v j ^ 2 * averageEnergy δ ν (A i) (B j)) := by
  let K : ℝ≥0∞ := 3 * (Fintype.card I * Fintype.card J : ℝ≥0∞)
  let f (i : I) (j : J) (t : ℝ) : ℝ≥0∞ :=
    (ENNReal.ofReal (w i) * ENNReal.ofReal (v j)) *
      (ENNReal.ofReal (w i) * ENNReal.ofReal (v j)) *
      ENNReal.ofReal (finiteEnergy δ t (A i) (B j))
  have hf (i : I) (j : J) : Measurable (f i j) :=
    measurable_const.mul (measurable_finiteEnergy _ _ _).ennreal_ofReal
  have hfi (i : I) : Measurable (fun t => ∑ j, f i j t) :=
    Finset.measurable_sum _ (fun j hj => hf i j)
  calc
    _ ≤ ∫⁻ t, K * ∑ i, ∑ j, f i j t ∂ν :=
      lintegral_mono (fun t => collision_level_sum t δ hδ A B
        (fun i => ENNReal.ofReal (w i)) (fun j => ENNReal.ofReal (v j))
        (fun _ => ENNReal.ofReal_ne_top) (fun _ => ENNReal.ofReal_ne_top))
    _ = K * ∑ i, ∑ j, ENNReal.ofReal (w i ^ 2 * v j ^ 2 * averageEnergy δ ν (A i) (B j)) := by
      rw [lintegral_const_mul _ (Finset.measurable_sum _ (fun i hi => hfi i)),
        lintegral_finsetSum _ (fun i hi => hfi i)]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [lintegral_finsetSum _ (fun j hj => hf i j)]
      apply Finset.sum_congr rfl
      intro j hj
      dsimp only [f]
      rw [lintegral_const_mul _ (measurable_finiteEnergy _ _ _).ennreal_ofReal,
        lintegral_finiteEnergy_eq hδ ν _ _ (hsep i)]
      exact ofReal_weighted_energy _ _ _ (hw i) (hv j)

lemma averaged_level_sum_real_le {I J : Type*} [Fintype I] [Fintype J]
    {δ : ℝ} (hδ : 0 < δ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (A : I → Finset ℝ) (B : J → Finset ℝ) (w : I → ℝ) (v : J → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ j, 0 ≤ v j)
    (hsep : ∀ i, ∀ x ∈ A i, ∀ y ∈ A i, x ≠ y → δ ≤ dist x y) :
    (∫⁻ t, collision (16 * δ)
        (projected t (∑ i, ENNReal.ofReal (w i) • counting (A i))
          (∑ j, ENNReal.ofReal (v j) • counting (B j))) ∂ν) ≤
      ENNReal.ofReal (3 * (Fintype.card I : ℝ) * (Fintype.card J : ℝ) *
        ∑ i, ∑ j, w i ^ 2 * v j ^ 2 * averageEnergy δ ν (A i) (B j)) := by
  have he (i : I) (j : J) : 0 ≤ w i ^ 2 * v j ^ 2 * averageEnergy δ ν (A i) (B j) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (averageEnergy_nonneg _ _ _ _)
  have hS : (∑ i, ∑ j, ENNReal.ofReal (w i ^ 2 * v j ^ 2 * averageEnergy δ ν (A i) (B j))) =
      ENNReal.ofReal (∑ i, ∑ j, w i ^ 2 * v j ^ 2 * averageEnergy δ ν (A i) (B j)) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i hi => Finset.sum_nonneg (fun j hj => he i j))]
    apply Finset.sum_congr rfl
    intro i hi
    exact (ENNReal.ofReal_sum_of_nonneg (fun j hj => he i j)).symm
  have hK : (3 * (Fintype.card I * Fintype.card J : ℝ≥0∞)) =
      ENNReal.ofReal (3 * (Fintype.card I : ℝ) * (Fintype.card J : ℝ)) := by
    have hh : 3 * (Fintype.card I : ℝ) * (Fintype.card J : ℝ) =
        ((3 * Fintype.card I * Fintype.card J : ℕ) : ℝ) := by push_cast; ring
    rw [hh, ENNReal.ofReal_natCast]
    push_cast
    ring
  have h := averaged_level_sum_le hδ ν A B w v hw hv hsep
  rw [hS, hK] at h
  simpa only [ENNReal.ofReal_mul (p := 3 * (Fintype.card I : ℝ) * (Fintype.card J : ℝ))
    (by positivity)] using h

end Submission.Obl.k4_oss_weighted_level_transfer
