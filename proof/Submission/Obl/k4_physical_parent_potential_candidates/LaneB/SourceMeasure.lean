import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.SourceNormalization

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set MeasureTheory

noncomputable section

namespace SourceNormalization

/-- Convert the localization's real mass floor into retention of the
original measure, keeping its original normalization. -/
theorem mass_retained_of_real_floor {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (G Gz : Set Ω) {E : ℝ} (hE : 0 < E)
    (hG : μ G ≠ ⊤) (hfloor : ENNReal.ofReal (μ.real G/E) ≤ μ Gz) :
    μ G ≤ ENNReal.ofReal E*μ Gz := by
  have hreal : 0 ≤ μ.real G := ENNReal.toReal_nonneg
  calc
    _ = ENNReal.ofReal E*ENNReal.ofReal (μ.real G/E) := by
      rw [←ENNReal.ofReal_mul hE.le,mul_div_cancel₀ _ hE.ne',Measure.real,ENNReal.ofReal_toReal hG]
    _ ≤ _ := mul_le_mul_right hfloor _

/-- The absolute zoom cap becomes a relative cap by precisely the mass
retention factor. No normalized probability law is substituted. -/
theorem relative_density_of_zoom_floor {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (G Gz : Set Ω) (X : Ω → P3) {D lam E : ℝ}
    (hD : 0 ≤ D) (hlam : 1 ≤ lam) (hE : 0 < E) (hG : μ G ≠ ⊤)
    (hfloor : ENNReal.ofReal (μ.real G/E) ≤ μ Gz)
    (hdom : ∀ U : Set P3, MeasurableSet U →
      μ (Gz ∩ X ⁻¹' U) ≤ ENNReal.ofReal (D*μ.real G/lam^3)*volume U) :
    μ G ≤ ENNReal.ofReal E*μ Gz ∧
      (∀ U : Set P3, MeasurableSet U →
        μ (Gz ∩ X ⁻¹' U) ≤ ENNReal.ofReal (D*E)*μ Gz*volume U) := by
  have hmass := mass_retained_of_real_floor μ G Gz hE hG hfloor
  refine ⟨hmass,?_⟩
  intro U hU
  have hden : 1 ≤ lam^3 := one_le_pow₀ hlam
  have hreal : 0 ≤ μ.real G := ENNReal.toReal_nonneg
  have hcoef : D*μ.real G/lam^3 ≤ D*μ.real G := div_le_self (by positivity) hden
  calc
    _ ≤ ENNReal.ofReal (D*μ.real G/lam^3)*volume U := hdom U hU
    _ ≤ ENNReal.ofReal (D*μ.real G)*volume U :=
      mul_le_mul_left (ENNReal.ofReal_le_ofReal hcoef) _
    _ = ENNReal.ofReal D*μ G*volume U := by
      rw [ENNReal.ofReal_mul hD,Measure.real,ENNReal.ofReal_toReal hG]
    _ ≤ ENNReal.ofReal D*(ENNReal.ofReal E*μ Gz)*volume U := by gcongr
    _ = _ := by rw [ENNReal.ofReal_mul hD]; ac_rfl

end SourceNormalization

end

end Submission.Obl.k4_physical_parent_potential_candidates
