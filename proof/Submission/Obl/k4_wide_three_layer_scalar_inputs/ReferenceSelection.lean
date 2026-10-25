import Submission.Lib.K4FinalLawSelection

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open Set MeasureTheory Finset

noncomputable section

/-- A finite cover with total original reference budget one contains an
entry with the same absolute density as the entire retained law. -/
theorem exists_dense_reference_entry {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (E : ι → Set Ω) (reference : ι → ENNReal) {mass : ℝ}
    (hmass : 0 < mass) (hμ : ENNReal.ofReal mass ≤ μ univ)
    (hcover : ∀ᵐ p ∂μ, ∃ i, p ∈ E i) (hbudget : ∑ i, reference i ≤ 1) :
    ∃ i, ENNReal.ofReal mass * reference i ≤ μ (E i) := by
  classical
  have hcov : μ univ ≤ ∑ i, μ (E i) := by
    apply (measure_mono_ae ?_).trans (measure_iUnion_fintype_le _ _)
    filter_upwards [hcover] with p hp _
    exact mem_iUnion.mpr hp
  rcases isEmpty_or_nonempty ι with hEmpty | hNonempty
  · have hzero : μ univ = 0 := by simpa using hcov
    have hp : 0 < ENNReal.ofReal mass := ENNReal.ofReal_pos.mpr hmass
    rw [hzero] at hμ
    exact (not_le_of_gt hp hμ).elim
  · by_contra hn
    push Not at hn
    have hstrict : ∑ i, μ (E i) < ∑ i, ENNReal.ofReal mass * reference i :=
      ENNReal.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => hn i)
    have ht : ∑ i, ENNReal.ofReal mass * reference i ≤ ENNReal.ofReal mass := by
      rw [← Finset.mul_sum]
      simpa using mul_le_mul' (le_refl (ENNReal.ofReal mass)) hbudget
    exact (not_lt_of_ge (hμ.trans hcov)) (hstrict.trans_le ht)

/-- Renew two complete finite reference tables simultaneously on one
original submeasure, charging each table's budget once. -/
theorem exists_common_reference_core {Ω ι κ : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype κ]
    (μ : Measure Ω) (E : ι → Set Ω) (F : κ → Set Ω)
    (hE : ∀ i, MeasurableSet (E i)) (hF : ∀ j, MeasurableSet (F j))
    (wE : ι → ENNReal) (wF : κ → ENNReal) (δ : ENNReal) {mass : ℝ}
    (hmass : 0 < mass) (hμ : ENNReal.ofReal mass ≤ μ univ)
    (hbudget : δ * ((∑ i, wE i) + ∑ j, wF j) ≤ ENNReal.ofReal (mass / 2)) :
    ∃ ν : Measure Ω, ν ≤ μ ∧ ENNReal.ofReal (mass / 2) ≤ ν univ ∧
      (∀ i, ν (E i) = 0 ∨ δ * wE i ≤ ν (E i)) ∧
      (∀ j, ν (F j) = 0 ∨ δ * wF j ≤ ν (F j)) := by
  classical
  let events : ι ⊕ κ → Set Ω := Sum.elim E F
  let weights : ι ⊕ κ → ENNReal := Sum.elim (fun i => δ * wE i) (fun j => δ * wF j)
  have hEvents : ∀ z, MeasurableSet (events z) := by
    intro z
    cases z with
    | inl i => exact hE i
    | inr j => exact hF j
  obtain ⟨ν, hν, hloss, hfloors⟩ :=
    Submission.Lib.K4FinalLawSelection.exists_simultaneous_floor_measure
      Finset.univ events hEvents weights μ
  have hsum : (∑ z ∈ Finset.univ, weights z) =
      δ * ((∑ i, wE i) + ∑ j, wF j) := by
    simp only [Fintype.sum_sum_type, weights, Sum.elim_inl, Sum.elim_inr,
      ← Finset.mul_sum, ← mul_add]
  have hhalf : ENNReal.ofReal mass = ENNReal.ofReal (mass / 2) +
      ENNReal.ofReal (mass / 2) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  have hh : ENNReal.ofReal (mass / 2) ≤ ν univ := by
    have h := hμ.trans (hloss.trans (add_le_add le_rfl (hsum.le.trans hbudget)))
    rw [hhalf] at h
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp h
  refine ⟨ν, hν, hh, ?_, ?_⟩
  · intro i
    exact hfloors (Sum.inl i) (Finset.mem_univ _)
  · intro j
    exact hfloors (Sum.inr j) (Finset.mem_univ _)

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs
