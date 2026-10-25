import Submission.Obl.k4_scalar_marked_packet_recovery.MarkedMeasure

namespace Submission.Obl.k4_scalar_marked_packet_recovery

open Set MeasureTheory
open scoped ENNReal

noncomputable def referenceMass {H J : ℕ} (w : Fin H → ℝ)
    (mark : Fin H → Fin J → Bool) (j : Fin H) : ℝ≥0∞ :=
  ENNReal.ofReal (w j) * volume (markTimes mark j)

noncomputable def sliceMass {H J : ℕ} (b₀ : Fin H → Coeff) (w : Fin H → ℝ)
    (mark : Fin H → Fin J → Bool) (A : Set Label) (u : Coeff) : ℝ≥0∞ := by
  classical
  exact ∑ j, if embed b₀ j u ∈ A then referenceMass w mark j else 0

theorem measurable_sliceMass {H J : ℕ} (b₀ : Fin H → Coeff) (w : Fin H → ℝ)
    (mark : Fin H → Fin J → Bool) {A : Set Label} (hA : MeasurableSet A) :
    Measurable (sliceMass b₀ w mark A) := by
  classical
  exact Finset.measurable_sum _ fun j _ =>
    Measurable.ite (hA.preimage (measurable_embed b₀ j)) measurable_const measurable_const

/-- Integrating one common jitter reproduces the marked cylinder mass. -/
theorem markedLaw_cylinder {σ : ℝ} {H J : ℕ} (b₀ : Fin H → Coeff)
    (w : Fin H → ℝ) (mark : Fin H → Fin J → Bool) {A : Set Label}
    (hA : MeasurableSet A) :
    MarkedLaw σ H J b₀ w mark (A ×ˢ (univ : Set ℝ)) =
      ∫⁻ u, sliceMass b₀ w mark A u ∂Noise σ := by
  classical
  let E := (A ×ˢ (univ : Set ℝ)) ∩ MarkedEvent H J mark
  have hE : MeasurableSet E :=
    (hA.prod MeasurableSet.univ).inter (measurableSet_markedEvent mark)
  have hsec : ∀ j u, Prod.mk (embed b₀ j u) ⁻¹' E =
      if embed b₀ j u ∈ A then markTimes mark j else ∅ := by
    intro j u
    ext t
    simp only [E, mem_preimage, mem_inter_iff, mem_prod, mem_univ, and_true,
      embed_mem_event]
    split_ifs with h <;> simp [h]
  change ((MarkedPrior σ H b₀ w).prod volume).restrict _ (A ×ˢ univ) = _
  rw [Measure.restrict_apply (hA.prod MeasurableSet.univ), Measure.prod_apply hE]
  change (∫⁻ l, volume (Prod.mk l ⁻¹' E) ∂∑ j, ENNReal.ofReal (w j) •
    Measure.map (embed b₀ j) (Noise σ)) = _
  rw [lintegral_finsetSum_measure]
  simp_rw [lintegral_smul_measure, smul_eq_mul,
    lintegral_map (measurable_measure_prodMk_left hE) (measurable_embed b₀ _), hsec]
  unfold sliceMass
  rw [lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro u
    split_ifs <;> simp [referenceMass]
  · intro j _
    exact Measurable.ite (hA.preimage (measurable_embed b₀ j)) measurable_const measurable_const

/-- A positive integral can be retained, up to a factor two, at one supported jitter. -/
theorem exists_common_jitter {σ : ℝ} (hσ : 0 < σ) {H J : ℕ}
    (b₀ : Fin H → Coeff) (w : Fin H → ℝ) (mark : Fin H → Fin J → Bool)
    {A : Set Label} (hA : MeasurableSet A) {a : ℝ} (ha : 0 < a)
    (hmass : ENNReal.ofReal a ≤ MarkedLaw σ H J b₀ w mark (A ×ˢ (univ : Set ℝ))) :
    ∃ u : Coeff, (∀ e, u e ∈ Icc (0 : ℝ) σ) ∧
      ENNReal.ofReal (a / 2) ≤ sliceMass b₀ w mark A u := by
  haveI := noise_probability hσ
  by_contra! h
  have hb : ∀ᵐ u ∂Noise σ, sliceMass b₀ w mark A u ≤ ENNReal.ofReal (a / 2) :=
    (noise_ae_cube hσ).mono fun u hu => (h u hu).le
  have hi := lintegral_mono_ae hb
  rw [lintegral_const, measure_univ, mul_one, ← markedLaw_cylinder b₀ w mark hA] at hi
  have := hmass.trans hi
  have : a ≤ a / 2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp this
  linarith

end Submission.Obl.k4_scalar_marked_packet_recovery
