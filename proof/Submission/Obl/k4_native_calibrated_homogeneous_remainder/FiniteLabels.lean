import Mathlib

/-! Forgetting a countable label supported on a finite set. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder

open MeasureTheory Set
open scoped ENNReal

section

variable {X I Ω : Type*} [MeasurableSpace X] [MeasurableSpace I] [MeasurableSpace Ω]
  [Countable I] [MeasurableSingletonClass I]

/-- The continuous marginal of a counted density is the sum of its slices. -/
theorem map_fst_counted_density (ρ : Measure X) [SFinite ρ]
    (G : X × I → ENNReal) (hG : Measurable G) :
    ((ρ.prod Measure.count).withDensity G).map Prod.fst =
      ρ.withDensity (fun x => ∑' i, G (x, i)) := by
  ext A hA
  rw [Measure.map_apply measurable_fst hA]
  have hpre : Prod.fst ⁻¹' A = A ×ˢ (univ : Set I) := by ext p; simp
  rw [hpre, withDensity_apply _ (hA.prod MeasurableSet.univ), ← Measure.prod_restrict,
    Measure.restrict_univ, lintegral_prod _ hG.aemeasurable, withDensity_apply _ hA]
  simp_rw [lintegral_count]

/-- A counted density is at most its marginal density at sampled observations. -/
theorem counted_density_le_marginal (ρ : Measure X) [SigmaFinite ρ]
    (μ : Measure Ω) (obs : Ω → X) (label : Ω → I)
    (hobs : Measurable obs) (hlabel : Measurable label)
    (g : X → ENNReal) (G : X × I → ENNReal) (hg : Measurable g) (hG : Measurable G)
    (hpure : μ.map obs = ρ.withDensity g)
    (hjoint : μ.map (fun p => (obs p, label p)) = (ρ.prod Measure.count).withDensity G) :
    ∀ᵐ p ∂μ, G (obs p, label p) ≤ g (obs p) := by
  have hsum : Measurable (fun x => ∑' i, G (x, i)) :=
    Measurable.tsum fun i => hG.comp (measurable_id.prodMk measurable_const)
  have heq : (fun x => ∑' i, G (x, i)) =ᵐ[ρ] g := by
    apply (withDensity_eq_iff_of_sigmaFinite hsum.aemeasurable hg.aemeasurable).mp
    rw [← map_fst_counted_density ρ G hG, ← hjoint,
      Measure.map_map measurable_fst (hobs.prodMk hlabel)]
    exact hpure
  have hac : μ.map obs ≪ ρ := by rw [hpure]; exact withDensity_absolutelyContinuous _ _
  have hsample := ae_of_ae_map hobs.aemeasurable (hac.ae_le heq)
  filter_upwards [hsample] with p hp
  exact (ENNReal.le_tsum (label p)).trans_eq hp

/-- On finitely many labels the low-density refinement loss is their number. -/
theorem finite_label_lowDensity_integral (ρ : Measure X) [SFinite ρ]
    (g : X → ENNReal) (G : X × I → ENNReal) (hg : Measurable g) (hG : Measurable G)
    (L : Finset I) (ε : ENNReal) :
    ((ρ.prod Measure.count).withDensity G)
      {p | p.2 ∈ L ∧ G p < ε * g p.1} ≤
      ε * (L.card : ENNReal) * ∫⁻ x, g x ∂ρ := by
  classical
  let B : Set (X × I) := {p | p.2 ∈ L ∧ G p < ε * g p.1}
  have hB : MeasurableSet B :=
    ((L.finite_toSet.measurableSet).preimage measurable_snd).inter
      (measurableSet_lt hG (measurable_const.mul (hg.comp measurable_fst)))
  have hpt (x : X) : (∑' i, B.indicator G (x, i)) ≤ ε * (L.card : ENNReal) * g x := by
    rw [tsum_eq_sum (s := L) (fun i hi => by simp [B, Set.indicator, hi])]
    calc
      _ ≤ ∑ _i ∈ L, ε * g x := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hb : (x, i) ∈ B
        · rw [indicator_of_mem hb]
          exact hb.2.le
        · rw [indicator_of_notMem hb]
          exact zero_le
      _ = (L.card : ENNReal) * (ε * g x) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = _ := by ring
  change (ρ.prod Measure.count).withDensity G B ≤ _
  rw [withDensity_apply _ hB, ← lintegral_indicator hB,
    lintegral_prod _ ((hG.indicator hB).aemeasurable)]
  simp_rw [lintegral_count]
  exact (lintegral_mono hpt).trans_eq (lintegral_const_mul _ hg)

/-- The finite-label estimate on the actual incidence law. -/
theorem finite_label_lowDensity_mass (ρ : Measure X) [SigmaFinite ρ]
    (μ : Measure Ω) (obs : Ω → X) (label : Ω → I)
    (hobs : Measurable obs) (hlabel : Measurable label)
    (g : X → ENNReal) (G : X × I → ENNReal) (hg : Measurable g) (hG : Measurable G)
    (hpure : μ.map obs = ρ.withDensity g)
    (hjoint : μ.map (fun p => (obs p, label p)) = (ρ.prod Measure.count).withDensity G)
    (L : Finset I) (hL : ∀ᵐ p ∂μ, label p ∈ L) (ε : ENNReal) :
    μ {p | G (obs p, label p) < ε * g (obs p)} ≤ ε * (L.card : ENNReal) * μ univ := by
  have hbad : MeasurableSet {p : X × I | p.2 ∈ L ∧ G p < ε * g p.1} :=
    ((L.finite_toSet.measurableSet).preimage measurable_snd).inter
      (measurableSet_lt hG (measurable_const.mul (hg.comp measurable_fst)))
  have hmass : (∫⁻ x, g x ∂ρ) = μ univ := by
    rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ, ← hpure,
      Measure.map_apply hobs MeasurableSet.univ, preimage_univ]
  calc
    _ ≤ μ {p | label p ∈ L ∧ G (obs p, label p) < ε * g (obs p)} := by
      apply measure_mono_ae
      filter_upwards [hL] with p hp hbad
      exact ⟨hp, hbad⟩
    _ = ((ρ.prod Measure.count).withDensity G)
        {p | p.2 ∈ L ∧ G p < ε * g p.1} := by
      rw [← hjoint, Measure.map_apply (hobs.prodMk hlabel) hbad]
      rfl
    _ ≤ _ := by
      simpa only [hmass] using finite_label_lowDensity_integral ρ g G hg hG L ε

end

end Submission.Obl.k4_native_calibrated_homogeneous_remainder
