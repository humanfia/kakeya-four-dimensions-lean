import Submission.Obl.k4_scalar_candidate_original_return.SourceLaw

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

open MeasureTheory Set
open scoped ENNReal

noncomputable section

def mixtureDensity {m : ℕ} (c : Fin m → ℝ)
    (S : Fin m → Set (Fin 6 → ℝ)) (w : Fin 6 → ℝ) : ℝ :=
  ∑ j, c j * (S j).indicator 1 w

lemma mixtureDensity_nonneg {m : ℕ} (c : Fin m → ℝ) (hc : ∀ j, 0 ≤ c j)
    (S : Fin m → Set (Fin 6 → ℝ)) (w : Fin 6 → ℝ) : 0 ≤ mixtureDensity c S w := by
  classical
  apply Finset.sum_nonneg
  intro j _
  by_cases h : w ∈ S j <;> simp [h, hc j]

lemma mixtureDensity_measurable {m : ℕ} (c : Fin m → ℝ)
    (S : Fin m → Set (Fin 6 → ℝ)) (hS : ∀ j, MeasurableSet (S j)) :
    Measurable (mixtureDensity c S) := by
  apply Finset.measurable_sum
  intro j _
  exact measurable_const.mul (measurable_const.indicator (hS j))

lemma mixtureDensity_bound {m : ℕ} {H : ℝ} (c : Fin m → ℝ)
    (hc : ∀ j, 0 ≤ c j ∧ c j ≤ H) (S : Fin m → Set (Fin 6 → ℝ))
    (w : Fin 6 → ℝ) : |mixtureDensity c S w| ≤ (m : ℝ) * H := by
  classical
  rw [abs_of_nonneg (mixtureDensity_nonneg c (fun j => (hc j).1) S w)]
  calc
    _ ≤ ∑ _j : Fin m, H := by
      apply Finset.sum_le_sum
      intro j _
      by_cases h : w ∈ S j
      · simpa [h] using (hc j).2
      · simpa [h] using (hc j).1.trans (hc j).2
    _ = (m : ℝ) * H := by simp

/-- Finite tempered prior mixtures have an exact selected density after any
volume-preserving coefficient/time change of coordinates. -/
theorem mixture_law_in_coordinates
    (e : (Fin 5 → ℝ) × ℝ ≃ᵐ (Fin 6 → ℝ))
    (he : MeasurePreserving e ((volume : Measure (Fin 5 → ℝ)).prod volume) volume)
    {m : ℕ} (c : Fin m → ℝ) (hc : ∀ j, 0 ≤ c j) (copy : Fin m → ℕ)
    (B : Fin m → Set (Fin 5 → ℝ)) (hB : ∀ j, MeasurableSet (B j))
    (ν : Measure Line)
    (hν : ν = ∑ j, ENNReal.ofReal (c j) •
      Measure.map (fun a : Fin 5 → ℝ => (copy j, a)) (volume.restrict (B j)))
    (C : Set Inc) (hC : MeasurableSet C) :
    (((ν.prod volume).restrict C).map (fun q => e (q.1.2, q.2))) =
      (volume : Measure (Fin 6 → ℝ)).withDensity
        (fun w => ENNReal.ofReal (mixtureDensity c
          (fun j => {w | (e.symm w).1 ∈ B j ∧
            ((copy j, (e.symm w).1), (e.symm w).2) ∈ C}) w)) := by
  classical
  let F : Inc → Fin 6 → ℝ := fun q => e (q.1.2, q.2)
  have hF : Measurable F :=
    e.measurable.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  let S : Fin m → Set (Fin 6 → ℝ) := fun j =>
    {w | (e.symm w).1 ∈ B j ∧ ((copy j, (e.symm w).1), (e.symm w).2) ∈ C}
  have hS (j : Fin m) : MeasurableSet (S j) :=
    ((hB j).preimage (measurable_fst.comp e.symm.measurable)).inter
      (hC.preimage ((measurable_componentIncidence (copy j)).comp e.symm.measurable))
  have hpiece (j : Fin m) :
      (((Measure.map (fun a : Fin 5 → ℝ => (copy j, a)) (volume.restrict (B j))).prod
        (volume : Measure ℝ)).restrict C).map F = volume.restrict (S j) :=
    component_law_in_coordinates e he (copy j) (hB j) hC
  let q : Fin m → (Fin 6 → ℝ) → ℝ≥0∞ :=
    fun j => ENNReal.ofReal (c j) • (S j).indicator 1
  have hq (j : Fin m) : Measurable (q j) :=
    measurable_const.smul (measurable_const.indicator (hS j))
  have hdensity : (∑' j, q j) = fun w => ENNReal.ofReal (mixtureDensity c S w) := by
    funext w
    rw [tsum_fintype]
    simp only [Finset.sum_apply, mixtureDensity]
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => by
      by_cases h : w ∈ S j <;> simp [h, hc j])]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : w ∈ S j <;> simp [q, h]
  calc
    _ = Measure.sum (fun j => ENNReal.ofReal (c j) • volume.restrict (S j)) := by
      rw [hν, ← Measure.sum_fintype, Measure.prod_sum_left,
        Measure.restrict_sum _ hC, Measure.map_sum hF.aemeasurable]
      congr 1
      funext j
      rw [Measure.prod_smul_left, Measure.restrict_smul,
        Measure.map_smul _ hF.aemeasurable, hpiece]
    _ = volume.withDensity (∑' j, q j) := by
      rw [withDensity_tsum hq]
      congr 1
      funext j
      dsimp only [q]
      have hh := withDensity_smul (μ := (volume : Measure (Fin 6 → ℝ)))
        (ENNReal.ofReal (c j)) (f := (S j).indicator (1 : (Fin 6 → ℝ) → ℝ≥0∞))
        (measurable_const.indicator (hS j))
      rw [withDensity_indicator_one (hS j)] at hh
      exact hh.symm
    _ = _ := by rw [hdensity]

end

end Submission.Obl.k4_scalar_candidate_original_return
