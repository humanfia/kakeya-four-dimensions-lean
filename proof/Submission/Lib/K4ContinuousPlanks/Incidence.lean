/-
Adapted from: here:o018
-/
import Submission.Lib.K4ContinuousPlanks.Continuous

/-! Converting marked time bins to the original, unnormalized incidence measure. -/

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Lib.K4ContinuousPlanks

theorem incidence_le_mark_integral {α : Type*} [MeasurableSpace α] {D : ℕ}
    (μ : Measure α) (hD : 1 ≤ D) (J : α → Finset (Fin D))
    (hJ : ∀ S, MeasurableSet (J ⁻¹' {S}))
    (E : Set (α × ℝ)) (hE : MeasurableSet E)
    (hcover : ∀ x t, (x, t) ∈ E → ∃ j ∈ J x,
      t ∈ Icc (((j : ℕ) : ℝ) / D) ((((j : ℕ) : ℝ) + 1) / D)) :
    (μ.prod volume) E ≤ ENNReal.ofReal (1 / (D : ℝ)) *
      ∫⁻ x, ((J x).card : ℝ≥0∞) ∂μ := by
  classical
  have hvolume (j : Fin D) : volume (Icc (((j : ℕ) : ℝ) / D)
      ((((j : ℕ) : ℝ) + 1) / D)) = ENNReal.ofReal (1 / (D : ℝ)) := by
    rw [Real.volume_Icc]
    congr 1
    ring
  have hsection (x : α) : volume (Prod.mk x ⁻¹' E) ≤
      ENNReal.ofReal (1 / (D : ℝ)) * ((J x).card : ℝ≥0∞) := by
    calc
      _ ≤ volume (⋃ j ∈ J x, Icc (((j : ℕ) : ℝ) / D) ((((j : ℕ) : ℝ) + 1) / D)) := by
        apply measure_mono
        intro t ht
        obtain ⟨j, hj, hjt⟩ := hcover x t ht
        exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hj, hjt⟩⟩
      _ ≤ ∑ j ∈ J x, volume (Icc (((j : ℕ) : ℝ) / D)
          ((((j : ℕ) : ℝ) + 1) / D)) := measure_biUnion_finset_le _ _
      _ = _ := by simp only [hvolume, Finset.sum_const, nsmul_eq_mul, mul_comm]
  let cards : SimpleFunc α ℝ≥0∞ :=
    (⟨J, hJ, Set.toFinite _⟩ : SimpleFunc α (Finset (Fin D))).map
      (fun S => (S.card : ℝ≥0∞))
  rw [Measure.prod_apply hE]
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (1 / (D : ℝ)) * ((J x).card : ℝ≥0∞) ∂μ :=
      lintegral_mono hsection
    _ = _ := lintegral_const_mul _ cards.measurable

/-- Continuous prior incidence mass is bounded by the visited-cell count times
the physical cell volume and the subpower factor from the weighted plank input. -/
theorem continuous_weighted_plank_incidence (Hplank : PlankEstimate) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 < C ∧ ∀ (D : ℕ), 1 ≤ D →
    ∀ (α : Type*) [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
      (b u : α → EuclideanSpace ℝ (Fin 2)),
      Measurable b → Measurable u → (∀ x, ‖b x‖ ≤ 1 ∧ ‖u x‖ ≤ 1) →
      ∀ (J : α → Finset (Fin D)), (∀ S, MeasurableSet (J ⁻¹' {S})) →
      (∀ x, (D : ℝ) ^ (1 - η) ≤ ((J x).card : ℝ)) →
      ∀ A : ℝ, 0 < A → MeasureFullPlankCap μ b u A →
      ∀ F : Finset (ℕ × (Fin 2 → ℤ)),
      (∀ x, ∀ j ∈ J x, ((j : ℕ), fun k : Fin 2 =>
        ⌊(D : ℝ) * (b x + (((((j : ℕ) : ℝ) + 1 / 2) / D) • u x)) k⌋) ∈ F) →
      ∀ E : Set (α × ℝ), MeasurableSet E →
      (∀ x t, (x, t) ∈ E → ∃ j ∈ J x,
        t ∈ Icc (((j : ℕ) : ℝ) / D) ((((j : ℕ) : ℝ) + 1) / D)) →
      (μ.prod volume) E ≤
        ENNReal.ofReal (C * A * (D : ℝ) ^ ε / (D : ℝ) ^ 3 * (F.card : ℝ)) := by
  obtain ⟨η, hη, C, hC, H⟩ := continuous_weighted_plank_estimate Hplank ε hε
  refine ⟨η, hη, C, hC, ?_⟩
  intro D hD α _ μ _ b u hb hu hbu J hJ hlong A hA hcap F hF E hE hcover
  have hd : (D : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hD))
  have hm := H D hD α μ b u hb hu hbu J hJ hlong A hA hcap F hF
  calc
    _ ≤ ENNReal.ofReal (1 / (D : ℝ)) * ∫⁻ x, ((J x).card : ℝ≥0∞) ∂μ :=
      incidence_le_mark_integral μ hD J hJ E hE hcover
    _ ≤ ENNReal.ofReal (1 / (D : ℝ)) *
        ENNReal.ofReal (C * A * (D : ℝ) ^ ε / (D : ℝ) ^ 2 * (F.card : ℝ)) :=
      mul_le_mul (le_refl _) hm zero_le zero_le
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / D)]
      congr 1
      field_simp

end Submission.Lib.K4ContinuousPlanks
