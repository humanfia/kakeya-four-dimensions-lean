import Submission.Lib.K4FinitePlankAtlases.ScalePlanks

/-!
Adapted from: here:o049

Original proof developed by session x0147 in
Submission/Obl/k4_cap_class_terminal_charts/ScaleDensity.lean.
Uses the accepted K4ContinuousPlanks finite-approximation and weighted APIs.
-/

namespace Submission.Lib.K4FinitePlankAtlases

open MeasureTheory Set
open scoped ENNReal
open Submission.Lib.K4ContinuousPlanks

/-- Dense marks convert the mesh-scale plank cap into a bound for the original
trajectory law itself. The mark loss is absorbed into the chosen exponent. -/
theorem scale_plank_mass_estimate (H : PlankEstimate) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 < C ∧ ∀ (D : ℕ), 1 ≤ D →
    ∀ (α : Type*) [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
      (b u : α → Plane), Measurable b → Measurable u →
      (∀ x, ‖b x‖ ≤ 1 ∧ ‖u x‖ ≤ 1) →
    ∀ J : α → Finset (Fin D), (∀ S, MeasurableSet (J ⁻¹' {S})) →
      (∀ x, (D : ℝ) ^ (1 - η) ≤ ((J x).card : ℝ)) →
    ∀ A : ℝ, 0 < A → ScalePlankCap D μ b u A →
    ∀ F : Finset (ℕ × (Fin 2 → ℤ)),
      (∀ x, ∀ j ∈ J x, ((j : ℕ), fun k : Fin 2 =>
        ⌊(D : ℝ) * (b x + (((((j : ℕ) : ℝ) + 1 / 2) / D) • u x)) k⌋) ∈ F) →
    μ.real univ ≤ C * A * (D : ℝ) ^ ε / (D : ℝ) ^ 3 * (F.card : ℝ) := by
  have he : 0 < ε / 2 := by positivity
  obtain ⟨η₀, hη₀, C, hC, hbound⟩ := scale_weighted_plank_estimate H (ε / 2) he
  let η := min η₀ (ε / 2)
  refine ⟨η, lt_min hη₀ he, C, hC, ?_⟩
  intro D hD α _ μ _ b u hb hu hbu J hJ hlong A hA hcap F hF
  have hd : 0 < (D : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  have hd₁ : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hlong₀ (x : α) : (D : ℝ) ^ (1 - η₀) ≤ ((J x).card : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hd₁ (by dsimp [η]; linarith [min_le_left η₀ (ε / 2)])).trans (hlong x)
  have hupper := hbound D hD α μ b u hb hu hbu J hJ hlong₀ A hA hcap F hF
  have hp : 0 < (D : ℝ) ^ (1 - η) := Real.rpow_pos_of_pos hd _
  have hlower : ENNReal.ofReal ((D : ℝ) ^ (1 - η)) * μ univ ≤
      ∫⁻ x, ((J x).card : ℝ≥0∞) ∂μ := by
    rw [← lintegral_const]
    apply lintegral_mono
    intro x
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal (hlong x)
  have hreal := ENNReal.toReal_le_of_le_ofReal (by positivity) (hlower.trans hupper)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hp.le] at hreal
  have hprod : (D : ℝ) ^ (1 - η) * (D : ℝ) ^ η = D := by
    rw [← Real.rpow_add hd, sub_add_cancel, Real.rpow_one]
  have hrecip : 1 / (D : ℝ) ^ (1 - η) ≤ (D : ℝ) ^ (ε / 2) / D := by
    apply (div_le_div_iff₀ hp hd).mpr
    rw [one_mul]
    calc
      (D : ℝ) = (D : ℝ) ^ (1 - η) * (D : ℝ) ^ η := hprod.symm
      _ ≤ (D : ℝ) ^ (1 - η) * (D : ℝ) ^ (ε / 2) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hd₁ (min_le_right η₀ (ε / 2))) hp.le
      _ = _ := mul_comm _ _
  have hsquare : ((D : ℝ) ^ (ε / 2)) ^ 2 = (D : ℝ) ^ ε := by
    rw [pow_two, ← Real.rpow_add hd]
    congr 1
    ring
  calc
    μ.real univ ≤ (C * A * (D : ℝ) ^ (ε / 2) / (D : ℝ) ^ 2 * (F.card : ℝ)) /
        (D : ℝ) ^ (1 - η) := (le_div_iff₀ hp).mpr
          (by simpa only [measureReal_def, mul_comm] using hreal)
    _ = (C * A * (D : ℝ) ^ (ε / 2) / (D : ℝ) ^ 2 * (F.card : ℝ)) *
        (1 / (D : ℝ) ^ (1 - η)) := by ring
    _ ≤ (C * A * (D : ℝ) ^ (ε / 2) / (D : ℝ) ^ 2 * (F.card : ℝ)) *
        ((D : ℝ) ^ (ε / 2) / D) := mul_le_mul_of_nonneg_left hrecip (by positivity)
    _ = _ := by rw [← hsquare]; field_simp <;> ring

/-- An excess of original mass over the visited-cell budget forces a heavy
whole-time plank with polynomially controlled widths. -/
theorem continuous_density_plank_inverse (H : PlankEstimate) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 < C ∧ ∀ (D : ℕ), 1 ≤ D →
    ∀ (α : Type*) [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
      (b u : α → Plane), Measurable b → Measurable u →
      (∀ x, ‖b x‖ ≤ 1 ∧ ‖u x‖ ≤ 1) →
    ∀ J : α → Finset (Fin D), (∀ S, MeasurableSet (J ⁻¹' {S})) →
      (∀ x, (D : ℝ) ^ (1 - η) ≤ ((J x).card : ℝ)) →
    ∀ (F : Finset (ℕ × (Fin 2 → ℤ))),
      (∀ x, ∀ j ∈ J x, ((j : ℕ), fun k : Fin 2 =>
        ⌊(D : ℝ) * (b x + (((((j : ℕ) : ℝ) + 1 / 2) / D) • u x)) k⌋) ∈ F) →
    ∀ mass ρ : ℝ, 0 < mass → 0 < ρ → mass ≤ μ.real univ →
      (F.card : ℝ) ≤ mass * (D : ℝ) ^ 3 / ρ →
    ∃ (c w e₁ e₂ : Plane) (a β : ℝ),
      ‖e₁‖ = 1 ∧ ‖e₂‖ = 1 ∧ inner ℝ e₁ e₂ = 0 ∧
      1 / (D : ℝ) ≤ a ∧ a ≤ β ∧ β ≤ 2 ∧
      (ρ / (C * (D : ℝ) ^ ε)) * a * β <
        μ.real {x | InFullTracePlank (b x) (u x) c w e₁ e₂ a β} := by
  obtain ⟨η, hη, C, hC, hbound⟩ := scale_plank_mass_estimate H ε hε
  refine ⟨η, hη, 2 * C, by positivity, ?_⟩
  intro D hD α _ μ _ b u hb hu hbu J hJ hlong F hF mass ρ hmass hρ hm hcells
  have hd : 0 < (D : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  let A := ρ / ((2 * C) * (D : ℝ) ^ ε)
  have hA : 0 < A := div_pos hρ (by positivity)
  by_contra hnone
  have hcap : ScalePlankCap D μ b u A := by
    intro c w e₁ e₂ a β he₁ he₂ he ha hab hβ
    have hr : μ.real {x | InFullTracePlank (b x) (u x) c w e₁ e₂ a β} ≤ A * a * β := by
      by_contra! hheavy
      exact hnone ⟨c, w, e₁, e₂, a, β, he₁, he₂, he, ha, hab, hβ, hheavy⟩
    calc
      _ = ENNReal.ofReal (μ.real {x | InFullTracePlank (b x) (u x) c w e₁ e₂ a β}) :=
        (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hr
  have hμ := hbound D hD α μ b u hb hu hbu J hJ hlong A hA hcap F hF
  have hscale : C * A * (D : ℝ) ^ ε / (D : ℝ) ^ 3 *
      (mass * (D : ℝ) ^ 3 / ρ) = mass / 2 := by dsimp [A]; field_simp
  have hμ' : μ.real univ ≤ mass / 2 := by
    apply hμ.trans
    rw [← hscale]
    exact mul_le_mul_of_nonneg_left hcells (by positivity)
  linarith

end Submission.Lib.K4FinitePlankAtlases
