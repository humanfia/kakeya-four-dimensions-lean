import Submission.Obl.k4_crop_angular_finite_tail.CropOverlap
import Submission.Obl.k4_adapted_affine_cube_cover.Assembly

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Obl.k4_crop_angular_finite_tail

/-- Distinct restricted laws count the coarse exceptional set only once. -/
lemma sum_restricted_density_tails_le {X Z Γ : Type*}
    [MeasurableSpace X] [MeasurableSpace Z] [Fintype Γ]
    (ref : Measure Z) [SigmaFinite ref] (μ : Measure X)
    (S : Γ → Set X) (hS : ∀ γ, MeasurableSet (S γ))
    (hdisj : Pairwise (fun γ γ' => Disjoint (S γ) (S γ')))
    (Φ : X → Z) (hΦ : Measurable Φ)
    (D : Γ → Z → ENNReal) (hD : ∀ γ, Measurable (D γ))
    (K : Z → ENNReal) (hK : Measurable K)
    (hpart : ∀ γ, (μ.restrict (S γ)).map Φ = ref.withDensity (D γ))
    (hfull : μ.map Φ = ref.withDensity K)
    (δ lo hi err : ENNReal) (hδ : δ ≠ 0) (hδt : δ ≠ ∞)
    (hlow : (∑ γ, μ (S γ ∩ {x | D γ (Φ x) < δ * K (Φ x)})) ≤ err) :
    (∑ γ, (μ.restrict (S γ)) {x | D γ (Φ x) < δ * lo ∨ hi / δ < D γ (Φ x)}) ≤
      μ {x | K (Φ x) < lo ∨ hi < δ * K (Φ x)} + err := by
  classical
  let B : Set X := {x | K (Φ x) < lo ∨ hi < δ * K (Φ x)}
  let T : Γ → Set X := fun γ => {x | D γ (Φ x) < δ * K (Φ x)}
  have hB : MeasurableSet B :=
    (measurableSet_lt (hK.comp hΦ) measurable_const).union
      (measurableSet_lt measurable_const (measurable_const.mul (hK.comp hΦ)))
  have hT (γ : Γ) : MeasurableSet (T γ) :=
    measurableSet_lt ((hD γ).comp hΦ) (measurable_const.mul (hK.comp hΦ))
  have hterm (γ : Γ) :
      (μ.restrict (S γ)) {x | D γ (Φ x) < δ * lo ∨ hi / δ < D γ (Φ x)} ≤
        (μ.restrict (S γ)) B + μ (S γ ∩ T γ) := by
    have hmono := density_restrict_le ref μ (S γ) Φ hΦ (D γ) K (hD γ) hK (hpart γ) hfull
    have hsub : ∀ᵐ x ∂μ.restrict (S γ),
        x ∈ {x | D γ (Φ x) < δ * lo ∨ hi / δ < D γ (Φ x)} → x ∈ B ∪ T γ := by
      filter_upwards [hmono] with x hx hbad
      rcases hbad with hbad | hbad
      · by_cases hklow : K (Φ x) < lo
        · exact Or.inl (Or.inl hklow)
        · exact Or.inr (hbad.trans_le (mul_le_mul' le_rfl (not_lt.mp hklow)))
      · apply Or.inl
        apply Or.inr
        have hh : hi / δ < K (Φ x) := hbad.trans_le hx
        exact (ENNReal.div_lt_iff (Or.inl hδ) (Or.inl hδt)).mp hh |>.trans_le (le_of_eq (mul_comm _ _))
    calc
      _ ≤ (μ.restrict (S γ)) (B ∪ T γ) := measure_mono_ae hsub
      _ ≤ (μ.restrict (S γ)) B + (μ.restrict (S γ)) (T γ) := measure_union_le _ _
      _ = _ := by rw [Measure.restrict_apply (hT γ), inter_comm (T γ) (S γ)]
  have hsum : (∑ γ, (μ.restrict (S γ)) B) ≤ μ B := by
    have hle := Submission.Obl.k4_adapted_affine_cube_cover.sum_restrict_le_of_disjoint
      μ S univ hS hdisj (fun _ => subset_univ _)
    simpa only [Measure.restrict_univ, Measure.finsetSum_apply] using (Measure.le_iff'.mp hle B)
  calc
    _ ≤ ∑ γ, ((μ.restrict (S γ)) B + μ (S γ ∩ T γ)) :=
      Finset.sum_le_sum fun γ _ => hterm γ
    _ = (∑ γ, (μ.restrict (S γ)) B) + ∑ γ, μ (S γ ∩ T γ) := Finset.sum_add_distrib
    _ ≤ μ B + err := add_le_add hsum hlow

end Submission.Obl.k4_crop_angular_finite_tail
