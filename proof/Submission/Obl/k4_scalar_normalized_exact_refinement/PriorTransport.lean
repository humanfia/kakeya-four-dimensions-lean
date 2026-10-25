import Submission.Obl.k4_scalar_normalized_exact_refinement.Coordinates
import Submission.Obl.k4_scalar_conditional_crop_worlds.CropPrior
import Submission.Obl.k4_scalar_conditional_crop_worlds.FormatLemmas

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_normalized_exact_refinement

open MeasureTheory Set
open scoped ENNReal

noncomputable section

lemma map_coefficient_restrict (σ : (Fin 5 → ℝ) ≃ᵐ (Fin 5 → ℝ)) (c : ℝ)
    (hσ : (volume : Measure (Fin 5 → ℝ)).map σ = ENNReal.ofReal c • volume)
    (B : Set (Fin 5 → ℝ)) :
    (volume.restrict B).map σ =
      ENNReal.ofReal c • volume.restrict (σ.symm ⁻¹' B) := by
  have h := σ.restrict_map (volume : Measure (Fin 5 → ℝ)) (σ.symm ⁻¹' B)
  have hp : σ ⁻¹' (σ.symm ⁻¹' B) = B := by ext a; simp
  rw [hp, hσ, Measure.restrict_smul] at h
  exact h.symm

lemma map_prior_component (σ : (Fin 5 → ℝ) ≃ᵐ (Fin 5 → ℝ)) (c : ℝ)
    (hσ : (volume : Measure (Fin 5 → ℝ)).map σ = ENNReal.ofReal c • volume)
    (A : Set Line) (hA : MeasurableSet A) (label : ℕ) (B : Set (Fin 5 → ℝ)) :
    (((volume.restrict B).map (fun a => (label, a))).restrict A).map
      ((MeasurableEquiv.refl ℕ).prodCongr σ) =
      ENNReal.ofReal c • (volume.restrict
        (σ.symm ⁻¹' (B ∩ (fun a => (label, a)) ⁻¹' A))).map (fun a => (label, a)) := by
  have hi : Measurable (fun a : Fin 5 → ℝ => (label, a)) := measurable_const.prodMk measurable_id
  rw [Measure.restrict_map hi hA, Measure.restrict_restrict (hA.preimage hi),
    Measure.map_map ((MeasurableEquiv.refl ℕ).prodCongr σ).measurable hi]
  have he : ((MeasurableEquiv.refl ℕ).prodCongr σ) ∘ (fun a : Fin 5 → ℝ => (label, a)) =
      (fun a => (label, a)) ∘ σ := rfl
  rw [he, ← Measure.map_map hi σ.measurable, map_coefficient_restrict σ c hσ,
    Measure.map_smul _ hi.aemeasurable]
  congr 3
  ext a
  exact and_comm

/-- Exact finite-mixture description of a transformed, fully assigned conditional prior. -/
lemma normalized_prior_representation (σ : (Fin 5 → ℝ) ≃ᵐ (Fin 5 → ℝ)) (c : ℝ)
    (_hc : 0 ≤ c) (hσ : (volume : Measure (Fin 5 → ℝ)).map σ = ENNReal.ofReal c • volume)
    (ν : Measure Line) [IsFiniteMeasure ν] (A : Set Line) (hA : MeasurableSet A)
    (hApos : ν A ≠ 0) (n : ℕ) (h : Fin n → ℝ) (label : Fin n → ℕ)
    (B : Fin n → Set (Fin 5 → ℝ)) (hh : ∀ j, 0 ≤ h j)
    (hν : ν = ∑ j, ENNReal.ofReal (h j) • (volume.restrict (B j)).map (fun a => (label j, a))) :
    (ν A)⁻¹ • (ν.restrict A).map ((MeasurableEquiv.refl ℕ).prodCongr σ) =
      ∑ j, ENNReal.ofReal (h j * c / (ν A).toReal) •
        (volume.restrict (σ.symm ⁻¹' (B j ∩ (fun a => (label j, a)) ⁻¹' A))).map
          (fun a => (label j, a)) := by
  have hAfin : ν A ≠ ∞ := measure_ne_top ν A
  have hp : 0 < (ν A).toReal := ENNReal.toReal_pos hApos hAfin
  rw [show ν.restrict A = (∑ j, ENNReal.ofReal (h j) •
      (volume.restrict (B j)).map (fun a => (label j, a))).restrict A from
    congrArg (fun μ : Measure Line => μ.restrict A) hν]
  rw [k4_scalar_conditional_crop_worlds.restrict_finset_sum,
    Measure.map_finset_sum ((MeasurableEquiv.refl ℕ).prodCongr σ).measurable.aemeasurable,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Measure.restrict_smul,
    Measure.map_smul _ ((MeasurableEquiv.refl ℕ).prodCongr σ).measurable.aemeasurable,
    map_prior_component σ c hσ A hA, smul_smul, smul_smul]
  congr 1
  rw [ENNReal.ofReal_div_of_pos hp, ENNReal.ofReal_mul (hh j),
    ENNReal.ofReal_toReal hAfin, div_eq_mul_inv]
  ring

/-- Finite prior format is preserved by a coefficient change with a constant
volume factor, polynomial inverse, and bounded image of the assignment. -/
theorem normalized_prior_data {R RA R' c : ℝ} {D DA D' : ℕ}
    (ν : Measure Line) [IsFiniteMeasure ν]
    (hν : k4_scalar_conditional_crop_worlds.PriorData R D ν)
    (A : Set Line) (hA : MeasurableSet A) (hApos : ν A ≠ 0)
    (hFA : ∀ label, k4_scalar_conditional_crop_worlds.Format 5 RA DA {a | (label, a) ∈ A})
    (σ : (Fin 5 → ℝ) ≃ᵐ (Fin 5 → ℝ)) (hc : 0 ≤ c)
    (hσ : (volume : Measure (Fin 5 → ℝ)).map σ = ENNReal.ofReal c • volume)
    (hpre : ∀ B, k4_scalar_conditional_crop_worlds.Format 5 (R + RA) (max D DA) B →
      k4_scalar_conditional_crop_worlds.Format 5 R' D' (σ.symm ⁻¹' B))
    (hRR' : R ≤ R') (hheight : R * c / (ν A).toReal ≤ R')
    (hbound : ∀ label a, (label, a) ∈ A → ∀ i, |σ a i| ≤ R') :
    k4_scalar_conditional_crop_worlds.PriorData R' D'
      ((ν A)⁻¹ • (ν.restrict A).map ((MeasurableEquiv.refl ℕ).prodCongr σ)) := by
  obtain ⟨n, hn, h, label, B, hB, hrep⟩ := hν
  have hp : 0 < (ν A).toReal := ENNReal.toReal_pos hApos (measure_ne_top ν A)
  refine ⟨n, hn.trans hRR', (fun j => h j * c / (ν A).toReal), label,
    (fun j => σ.symm ⁻¹' (B j ∩ (fun a => (label j, a)) ⁻¹' A)), ?_, ?_⟩
  · intro j
    refine ⟨div_nonneg (mul_nonneg (hB j).1 hc) hp.le, ?_, (hB j).2.2.1.trans hRR', ?_, ?_⟩
    · calc
        h j * c / (ν A).toReal ≤ R * c / (ν A).toReal := by gcongr; exact (hB j).2.1
        _ ≤ R' := hheight
    · apply hpre
      exact ((hB j).2.2.2.1.mono le_rfl (le_max_left D DA)).inter
        ((hFA (label j)).mono le_rfl (le_max_right D DA))
    · intro a ha i
      simpa using hbound (label j) (σ.symm a) ha.2 i
  · exact normalized_prior_representation σ c hc hσ ν A hA hApos n h label B
      (fun j => (hB j).1) hrep

end

end Submission.Obl.k4_scalar_normalized_exact_refinement
