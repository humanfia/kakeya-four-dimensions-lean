import Submission.Obl.k4_initial_horizon_bound.ResidualCap
import Submission.Obl.k4_initial_horizon_bound.TimeMarks
import Submission.Obl.k4_plank_estimate

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Obl.k4_initial_horizon_bound

open Submission.Lib.K4ContinuousPlanks
open Submission.Lib.K4PlankGeometry (cellCode)

/-- A stopped residual is small up to short-duration deletion and its
original visited-cell count. This is the quantitative inequality used
before summing over worlds and native groups. -/
theorem stopped_residual_mass_le (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 < C ∧ ∀ (D : ℕ), 1 ≤ D →
    ∀ (α : Type*) [MeasurableSpace α] (ν : Measure α) [IsFiniteMeasure ν]
      (b u : α → EuclideanSpace ℝ (Fin 2)),
      Measurable b → Measurable u → (∀ x, ‖b x‖ ≤ 1 ∧ ‖u x‖ ≤ 1) →
      ∀ E : Set (α × ℝ), MeasurableSet E → E ⊆ univ ×ˢ Icc (0 : ℝ) 1 →
      ∀ τ A : ℝ, 0 < τ → 0 < A → (D : ℝ) ^ (-η) ≤ τ →
      (∀ (c w e₁ e₂ : EuclideanSpace ℝ (Fin 2)) (a β : ℝ),
        ‖e₁‖ = 1 → ‖e₂‖ = 1 → inner ℝ e₁ e₂ = 0 → 0 < a → a ≤ β →
        (ν.withDensity (incidenceDuration E))
          {x | InFullTracePlank (b x) (u x) c w e₁ e₂ a β} ≤
            ENNReal.ofReal (A * a * β)) →
      ∀ F : Finset (ℕ × (Fin 2 → ℤ)),
      (∀ x, ENNReal.ofReal τ ≤ incidenceDuration E x →
        ∀ j ∈ positiveTimeMarks D E x, cellCode D (b x) (u x) j ∈ F) →
      (ν.prod volume) E ≤ ENNReal.ofReal τ * ν univ +
        ENNReal.ofReal (C * (A / τ) * (D : ℝ) ^ ε / (D : ℝ) ^ 3 * (F.card : ℝ)) := by
  classical
  obtain ⟨η, hη, C, hC, Hpl⟩ :=
    continuous_weighted_plank_estimate Submission.k4_plank_estimate ε hε
  refine ⟨η, hη, C, hC, ?_⟩
  intro D hD α _ ν _ b u hb hu hbu E hE hunit τ A hτ hA hlong hstop F hF
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  let H : Set α := {x | ENNReal.ofReal τ ≤ incidenceDuration E x}
  have hH : MeasurableSet H := measurableSet_le measurable_const (measurable_incidenceDuration hE)
  let νH : Measure H := ν.comap ((↑) : H → α)
  let bH : H → EuclideanSpace ℝ (Fin 2) := fun x => b x
  let uH : H → EuclideanSpace ℝ (Fin 2) := fun x => u x
  let J : H → Finset (Fin D) := fun x => positiveTimeMarks D E x
  have hJ : Measurable J := (measurable_positiveTimeMarks D hE).comp measurable_subtype_coe
  have hmap : νH.map ((↑) : H → α) = ν.restrict H := map_comap_subtype_coe hH ν
  have hcap : MeasureFullPlankCap νH bH uH (A / τ) := by
    have hcap' := residual_incidence_cap_to_prior ν E hE b u hb hu H hH hτ
      (fun x hx => hx) hstop
    intro c w e₁ e₂ a β he₁ he₂ he ha hab
    have h := hcap' c w e₁ e₂ a β he₁ he₂ he ha hab
    rw [← hmap, Measure.map_apply measurable_subtype_coe
      (measurableSet_fullTracePlank b u hb hu c w e₁ e₂ a β)] at h
    exact h
  have hJlong (x : H) : (D : ℝ) ^ (1 - η) ≤ ((J x).card : ℝ) := by
    have hpow : (D : ℝ) ^ (1 - η) = (D : ℝ) * (D : ℝ) ^ (-η) := by
      rw [sub_eq_add_neg, Real.rpow_add hDpos, Real.rpow_one]
    rw [hpow]
    exact (mul_le_mul_of_nonneg_left hlong hDpos.le).trans
      (positiveTimeMarks_card_lower hD E hunit x hτ.le x.property)
  have hbound : (∫⁻ x, ((J x).card : ℝ≥0∞) ∂νH) ≤
      ENNReal.ofReal (C * (A / τ) * (D : ℝ) ^ ε / (D : ℝ) ^ 2 * (F.card : ℝ)) := by
    apply Hpl D hD H νH bH uH (hb.comp measurable_subtype_coe)
      (hu.comp measurable_subtype_coe) (fun x => hbu x) J
      (fun S => hJ (measurableSet_singleton S)) hJlong (A / τ) (div_pos hA hτ) hcap F
    intro x j hj
    exact hF x x.property j hj
  have hhigh : (ν.withDensity (incidenceDuration E)) H ≤
      ENNReal.ofReal (C * (A / τ) * (D : ℝ) ^ ε / (D : ℝ) ^ 3 * (F.card : ℝ)) := by
    rw [withDensity_apply _ hH, ← hmap,
      lintegral_map (measurable_incidenceDuration hE) measurable_subtype_coe]
    calc
      _ ≤ ∫⁻ x : H, ENNReal.ofReal (1 / (D : ℝ)) * ((J x).card : ℝ≥0∞) ∂νH := by
        apply lintegral_mono
        intro x
        have h := duration_le_positiveTimeMarks hD E hunit (x : α)
        have heq : ((J x).card : ℝ) / (D : ℝ) = (1 / (D : ℝ)) * ((J x).card : ℝ) := by ring
        rw [heq, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast] at h
        exact h
      _ = ENNReal.ofReal (1 / (D : ℝ)) * ∫⁻ x, ((J x).card : ℝ≥0∞) ∂νH := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (1 / (D : ℝ)) *
          ENNReal.ofReal (C * (A / τ) * (D : ℝ) ^ ε / (D : ℝ) ^ 2 * (F.card : ℝ)) :=
        mul_le_mul (le_refl _) hbound zero_le zero_le
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
  have hlow : (ν.withDensity (incidenceDuration E)) Hᶜ ≤ ENNReal.ofReal τ * ν univ := by
    have heq : Hᶜ = {x | incidenceDuration E x < ENNReal.ofReal τ} := by
      ext x
      simp only [H, mem_compl_iff, mem_ofPred_eq, not_le]
    rw [heq]
    exact short_duration_mass_le ν hE (ENNReal.ofReal τ)
  have htotal : (ν.withDensity (incidenceDuration E)) univ = (ν.prod volume) E := by
    simpa only [univ_prod_univ, inter_univ] using duration_withDensity_apply ν hE MeasurableSet.univ
  rw [← htotal, ← measure_add_measure_compl hH]
  exact (add_le_add hhigh hlow).trans_eq (add_comm _ _)

end Submission.Obl.k4_initial_horizon_bound
