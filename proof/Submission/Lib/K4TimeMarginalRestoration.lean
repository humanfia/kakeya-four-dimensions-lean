import Submission.Lib.K4IncidenceWitnesses

/-!
Restore original incidence mass at times selected by a long trajectory witness.
Adapted from: here:o202 (session x0698).
These are the already checked measure kernels requested by o249/x0876; the
polynomial coefficient application stays in the obligation and imports accepted APIs.
-/

namespace Submission.Lib.K4TimeMarginalRestoration

open MeasureTheory Set

/-- Restore all paired lines at the times supplied by one long trajectory witness. -/
lemma exists_restored_time_witness {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (ρ : Measure (α × ℝ))
    {C m c : ℝ} (hC : 0 < C) (hm : 0 < m) (hc : 0 ≤ c)
    (hdom : ρ ≤ ENNReal.ofReal C • (ν.prod volume))
    {E : Set (α × ℝ)} {T₀ : Set ℝ} (hE : MeasurableSet E)
    (hmass : ENNReal.ofReal m ≤ ρ E) (hsub : E ⊆ univ ×ˢ T₀)
    (hrestore : ∀ T : Set ℝ, MeasurableSet T → T ⊆ T₀ →
      ENNReal.ofReal c * volume T ≤ ρ (E ∩ (univ ×ˢ T))) :
    ∃ l : α, MeasurableSet (Prod.mk l ⁻¹' E) ∧
      ENNReal.ofReal (m / (2 * C)) ≤ volume (Prod.mk l ⁻¹' E) ∧
      ENNReal.ofReal (c * m / (2 * C)) ≤ ρ (E ∩ (univ ×ˢ (Prod.mk l ⁻¹' E))) := by
  have hlong := Submission.Lib.K4IncidenceWitnesses.longTimeIncidences_mass
    ν ρ hC hm hdom hE hmass
  have hpos : 0 < ρ (Submission.Lib.K4IncidenceWitnesses.longTimeIncidences E
      (m / (2 * C))) := (ENNReal.ofReal_pos.mpr (by positivity)).trans_le hlong
  obtain ⟨p, hp⟩ := nonempty_of_measure_ne_zero hpos.ne'
  refine ⟨p.1, hE.preimage (measurable_const.prodMk measurable_id), hp.2, ?_⟩
  have hT : Prod.mk p.1 ⁻¹' E ⊆ T₀ := by
    intro t ht
    exact (hsub ht).2
  calc
    ENNReal.ofReal (c * m / (2 * C)) =
        ENNReal.ofReal c * ENNReal.ofReal (m / (2 * C)) := by
      rw [← ENNReal.ofReal_mul hc]
      congr 1
      ring
    _ ≤ ENNReal.ofReal c * volume (Prod.mk p.1 ⁻¹' E) := mul_le_mul' le_rfl hp.2
    _ ≤ _ := hrestore _ (hE.preimage (measurable_const.prodMk measurable_id)) hT

open MeasureTheory Set

/-- A Hahn set retains half the mass while dominating half the prescribed
mass times a reference measure of total mass at most one. -/
lemma exists_half_mass_floor {X : Type*} [MeasurableSpace X]
    (σ γ : Measure X) [IsFiniteMeasure σ] [IsFiniteMeasure γ]
    {m : ℝ} (hm : 0 ≤ m) (hγ : γ univ ≤ 1)
    (hmass : ENNReal.ofReal m ≤ σ univ) :
    ∃ T : Set X, MeasurableSet T ∧ ENNReal.ofReal (m / 2) ≤ σ T ∧
      ∀ U : Set X, MeasurableSet U → U ⊆ T →
        ENNReal.ofReal (m / 2) * γ U ≤ σ U := by
  let c := ENNReal.ofReal (m / 2)
  have : IsFiniteMeasure (c • γ) := γ.smul_finite ENNReal.ofReal_ne_top
  obtain ⟨T, hT, hpos, hneg⟩ := hahn_decomposition σ (c • γ)
  have hbad : σ Tᶜ ≤ c := by
    refine (hneg Tᶜ hT.compl Subset.rfl).trans ?_
    change c * γ Tᶜ ≤ c
    exact (mul_le_mul' le_rfl ((measure_mono (subset_univ _)).trans hγ)).trans_eq
      (mul_one c)
  have hsplit : c + c ≤ σ T + c := by
    calc c + c = ENNReal.ofReal m := by
          dsimp [c]
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
      _ ≤ σ univ := hmass
      _ = σ T + σ Tᶜ := (measure_add_measure_compl hT).symm
      _ ≤ σ T + c := add_le_add le_rfl hbad
  refine ⟨T, hT, ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top hsplit, ?_⟩
  intro U hU hUT
  exact hpos U hU hUT

/-- The paired event itself supplies a substantial set of times on which
every time restriction has a uniform original-law lower mass bound. -/
lemma exists_paired_time_floor {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (ρ : Measure (α × ℝ))
    {C m : ℝ} (hm : 0 ≤ m)
    (hdom : ρ ≤ ENNReal.ofReal C • (ν.prod volume))
    {E : Set (α × ℝ)} (_hE : MeasurableSet E)
    (hmass : ENNReal.ofReal m ≤ ρ E) (hsub : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) :
    ∃ T₀ : Set ℝ, MeasurableSet T₀ ∧ T₀ ⊆ Icc (0 : ℝ) 1 ∧
      ENNReal.ofReal (m / 2) ≤ ρ (E ∩ (univ ×ˢ T₀)) ∧
      ∀ T : Set ℝ, MeasurableSet T → T ⊆ T₀ →
        ENNReal.ofReal (m / 2) * volume T ≤ ρ (E ∩ (univ ×ˢ T)) := by
  have hupper : ρ E ≤ ENNReal.ofReal C := by
    refine (hdom E).trans ?_
    calc (ENNReal.ofReal C • (ν.prod volume)) E
        ≤ (ENNReal.ofReal C • (ν.prod volume)) (univ ×ˢ Icc (0 : ℝ) 1) :=
          measure_mono hsub
      _ = ENNReal.ofReal C := by
        simp [Measure.smul_apply, Measure.prod_prod, Real.volume_Icc]
  have : IsFiniteMeasure (ρ.restrict E) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hupper.trans_lt ENNReal.ofReal_lt_top⟩
  let σ := (ρ.restrict E).map Prod.snd
  let γ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  have hσ (T : Set ℝ) (hT : MeasurableSet T) :
      σ T = ρ (E ∩ (univ ×ˢ T)) := by
    change (ρ.restrict E).map Prod.snd T = _
    rw [Measure.map_apply measurable_snd hT, Measure.restrict_apply
      (measurable_snd hT)]
    congr 1
    ext p
    simp [and_comm]
  have hσmass : ENNReal.ofReal m ≤ σ univ := by
    simpa only [hσ univ MeasurableSet.univ, univ_prod_univ, inter_univ] using hmass
  have hσsupp : σ (Icc (0 : ℝ) 1)ᶜ = 0 := by
    rw [hσ _ measurableSet_Icc.compl]
    have hempty : E ∩ (univ ×ˢ (Icc (0 : ℝ) 1)ᶜ) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact hp.2.2 (hsub hp.1).2
    rw [hempty, measure_empty]
  have hγ : γ univ ≤ 1 := by simp [γ, Real.volume_Icc]
  obtain ⟨T, hT, hmassT, hfloor⟩ := exists_half_mass_floor σ γ hm hγ hσmass
  refine ⟨T ∩ Icc (0 : ℝ) 1, hT.inter measurableSet_Icc, inter_subset_right, ?_, ?_⟩
  · rw [← hσ _ (hT.inter measurableSet_Icc), measure_inter_conull hσsupp]
    exact hmassT
  · intro U hU hUT
    have hUT' : U ⊆ T := hUT.trans inter_subset_left
    have hUI : U ⊆ Icc (0 : ℝ) 1 := hUT.trans inter_subset_right
    have hbound := hfloor U hU hUT'
    rw [hσ U hU] at hbound
    simpa only [γ, Measure.restrict_apply hU, inter_eq_left.mpr hUI] using hbound

end Submission.Lib.K4TimeMarginalRestoration
