import Submission.Obl.k4_crop_angular_finite_tail.Observations
import Submission.Obl.k4_crop_angular_finite_tail.Transfer

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Obl.k4_crop_angular_finite_tail

open Submission.Obl.k4_profile_density_bounds (width reference)

/-- Summing over distinct crop cells costs only the four possible intercept bins. -/
lemma crop_low_ratio_sum {N u v : ℝ} (hN : 1 ≤ N) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (r : ℝ) (μ : Measure State) (ht : ∀ᵐ x ∂μ, x.2 ∈ Icc (0 : ℝ) 1)
    {w : ℕ} (q : Fin w → Fin 4 → ℤ) (hq : Function.Injective q)
    (K : Observation → ENNReal) (hK : Measurable K)
    (hfull : μ.map (observeWidth N r (width N u * width N v)) = reference.withDensity K)
    (D : Fin w → Observation → ENNReal) (hD : ∀ γ, Measurable (D γ))
    (hpart : ∀ γ, (μ.restrict (cropBox (width N u) (q γ) ×ˢ univ)).map
      (observeWidth N r (width N u * width N v)) = reference.withDensity (D γ))
    (δ : ENNReal) :
    (∑ γ, μ ((cropBox (width N u) (q γ) ×ˢ univ) ∩
      {x | D γ (observeWidth N r (width N u * width N v) x) <
        δ * K (observeWidth N r (width N u * width N v) x)})) ≤ 4 * δ * μ univ := by
  classical
  apply sum_lower_ratio_le reference μ (measurable_observeWidth _ _ _) hK hfull
    (fun γ => cropBox (width N u) (q γ) ×ˢ univ) D hD hpart
    (fun γ => compatibleCrop (width N u) (height N v) (q γ))
    (fun γ => measurableSet_compatibleCrop _ _ _) _ 4 _ δ
  · intro γ
    filter_upwards [ae_restrict_mem ((measurableSet_cropBox _ _).prod MeasurableSet.univ),
      ae_restrict_of_ae ht] with x hx hxt
    exact cropBox_observeWidth_compatible hN hu hv hx.1 hxt r
  · intro z
    have he : (∑ γ, (compatibleCrop (width N u) (height N v) (q γ)).indicator
        (fun _ => (1 : ENNReal)) z) =
        ((Finset.univ.filter (fun γ => z ∈ compatibleCrop (width N u) (height N v) (q γ))).card : ENNReal) := by
      simp only [Set.indicator_apply]
      simp
    rw [he]
    exact_mod_cast card_compatibleCrop_indices q hq (width N u) (height N v) z

/-- Densities of a restricted law are bounded by densities of the full law. -/
lemma density_restrict_le {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    (ref : Measure Z) [SigmaFinite ref] (μ : Measure X) (S : Set X)
    (Φ : X → Z) (hΦ : Measurable Φ) (D K : Z → ENNReal)
    (hD : Measurable D) (hK : Measurable K)
    (hpart : (μ.restrict S).map Φ = ref.withDensity D)
    (hfull : μ.map Φ = ref.withDensity K) :
    ∀ᵐ x ∂μ.restrict S, D (Φ x) ≤ K (Φ x) := by
  have hle : ref.withDensity D ≤ ref.withDensity K := by
    rw [← hpart, ← hfull]
    exact Measure.map_mono Measure.restrict_le_self hΦ
  have hden : ∀ᵐ z ∂ref, D z ≤ K z := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite hD
    intro A hA _
    rw [← withDensity_apply _ hA, ← withDensity_apply _ hA]
    exact Measure.le_iff'.mp hle A
  exact ae_comp_of_ae hΦ hpart (measurableSet_le hD hK) hden

end Submission.Obl.k4_crop_angular_finite_tail
