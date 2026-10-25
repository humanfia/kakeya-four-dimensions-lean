import Submission.Obl.k4_original_prior_line_extraction.TranslatedWindows

namespace Submission.Obl.k4_original_prior_line_extraction

open MeasureTheory Set Filter
open scoped ENNReal

/-- A single normalization of a translated joint window preserves both original priors. -/
lemma extract_window_law {n₁ n₂ : ℕ}
    (μ : Measure ((Fin n₁ × Fin n₂) × Base)) [IsFiniteMeasure μ]
    (π₁ : Fin n₁ → ℝ) (π₂ : Fin n₂ → ℝ)
    (hπ₁ : ∀ i, 0 ≤ π₁ i) (hπ₂ : ∀ j, 0 ≤ π₂ j)
    (hsum₁ : ∑ i, π₁ i = 1)
    {S q : ℝ} (hS : 0 < S) (hq : 0 < q)
    (hcap₁ : ∀ i U, MeasurableSet U →
      μ {p | p.1.1 = i ∧ p.2 ∈ U} ≤ ENNReal.ofReal (S * π₁ i) * volume U)
    (hcap₂ : ∀ j U, MeasurableSet U →
      μ {p | p.1.2 = j ∧ p.2 ∈ U} ≤ ENNReal.ofReal (S * π₂ j) * volume U)
    {E : Set ((Fin n₁ × Fin n₂) × Base)} (hE : MeasurableSet E)
    (hsupp : ∀ p ∈ E, ‖p.2‖ ≤ (1 : ℝ) / 2)
    (hmass : ENNReal.ofReal q ≤ μ E) (v : Base) (hv : ‖v‖ = 1) :
    ∃ y : Base, ‖y‖ ≤ (9 : ℝ) / 16 ∧
      ∃ ν : Measure ((Fin n₁ × Fin n₂) × ℝ), IsProbabilityMeasure ν ∧
        (∀ i U, MeasurableSet U → ν {p | p.1.1 = i ∧ p.2 ∈ U} ≤
          ENNReal.ofReal (windowVolume * S / q * π₁ i) * volume U) ∧
        (∀ j U, MeasurableSet U → ν {p | p.1.2 = j ∧ p.2 ∈ U} ≤
          ENNReal.ofReal (windowVolume * S / q * π₂ j) * volume U) ∧
        ν {p | p.2 ∈ Icc (0 : ℝ) 1 ∧ (p.1, y + (windowStep * p.2) • v) ∈ E}ᶜ = 0 := by
  classical
  obtain ⟨f, hf, hlaw, hf₁, hf₂⟩ := exists_pair_densities μ volume
    (fun i => ENNReal.ofReal (S * π₁ i)) (fun j => ENNReal.ofReal (S * π₂ j)) hcap₁ hcap₂
  let g : (Fin n₁ × Fin n₂) → Base → ℝ≥0∞ :=
    fun a => {x | (a, x) ∈ E}.indicator (f a)
  have hg (a : Fin n₁ × Fin n₂) : Measurable (g a) :=
    (hf a).indicator (hE.preimage (measurable_const.prodMk measurable_id))
  have hgf (a : Fin n₁ × Fin n₂) (x : Base) : g a x ≤ f a x := by
    by_cases hx : (a, x) ∈ E <;> simp [g, hx]
  have hg₁ (x : Base) (i : Fin n₁) : ∑ j, g (i, j) x ≤ ENNReal.ofReal (S * π₁ i) :=
    (Finset.sum_le_sum (fun j _ => hgf (i, j) x)).trans (hf₁ x i)
  have hg₂ (x : Base) (j : Fin n₂) : ∑ i, g (i, j) x ≤ ENNReal.ofReal (S * π₂ j) :=
    (Finset.sum_le_sum (fun i _ => hgf (i, j) x)).trans (hf₂ x j)
  have hgE (a : Fin n₁ × Fin n₂) (x : Base) (hx : g a x ≠ 0) : (a, x) ∈ E := by
    by_contra hn
    simp [g, hn] at hx
  have hgball (a : Fin n₁ × Fin n₂) (x : Base) (hx : g a x ≠ 0) :
      ‖x‖ ≤ (1 : ℝ) / 2 := hsupp (a, x) (hgE a x hx)
  have hgmass : ENNReal.ofReal q ≤ ∑ a, ∫⁻ x, g a x := by
    apply hmass.trans_eq
    rw [measure_eq_sum_components μ hE]
    apply Finset.sum_congr rfl
    intro a _
    have hm : Measurable (Prod.mk a : Base → (Fin n₁ × Fin n₂) × Base) :=
      measurable_const.prodMk measurable_id
    have hsection : MeasurableSet {x : Base | (a, x) ∈ E} := hE.preimage hm
    rw [← hlaw a, withDensity_apply _ hsection]
    exact (lintegral_indicator hsection (f a)).symm
  have hgtotal (x : Base) : ∑ a, g a x ≤ ENNReal.ofReal S := by
    calc
      _ = ∑ i, ∑ j, g (i, j) x := Fintype.sum_prod_type _
      _ ≤ ∑ i, ENNReal.ofReal (S * π₁ i) := Finset.sum_le_sum (fun i _ => hg₁ x i)
      _ = ENNReal.ofReal S := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg hS.le (hπ₁ i)),
          ← Finset.mul_sum, hsum₁, mul_one]
  obtain ⟨y, hy, hmassY⟩ := exists_mass_window hg v hv hgball hq hgmass
  let w : (Fin n₁ × Fin n₂) → ℝ → ℝ≥0∞ := fun a t => g a (y + (windowStep * t) • v)
  have hw (a : Fin n₁ × Fin n₂) : Measurable (w a) := (hg a).comp (by fun_prop)
  let τ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  let ν₀ : Measure ((Fin n₁ × Fin n₂) × ℝ) := indexedLaw τ w
  let z : ℝ≥0∞ := ν₀ univ
  have hz : z = windowMass g v y := indexedLaw_univ τ w
  have hzfinite : z ≠ ∞ := by
    have hle : z ≤ ENNReal.ofReal S := hz ▸ windowMass_le hg v y _ hgtotal
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have hzlower : ENNReal.ofReal (q / windowVolume) ≤ z := hmassY.trans_eq hz.symm
  have hzpos : 0 < z := (ENNReal.ofReal_pos.mpr (div_pos hq windowVolume_pos)).trans_le hzlower
  have hzrealpos : 0 < z.toReal := ENNReal.toReal_pos hzpos.ne' hzfinite
  have hzreal : q / windowVolume ≤ z.toReal := by
    have := ENNReal.toReal_mono hzfinite hzlower
    simpa [ENNReal.toReal_ofReal (div_nonneg hq.le windowVolume_pos.le)] using this
  have hinv : z⁻¹ ≤ ENNReal.ofReal (windowVolume / q) := by
    rw [← ENNReal.ofReal_toReal hzfinite, ← ENNReal.ofReal_inv_of_pos hzrealpos]
    apply ENNReal.ofReal_le_ofReal
    simpa only [inv_div] using inv_anti₀ (div_pos hq windowVolume_pos) hzreal
  let ν : Measure ((Fin n₁ × Fin n₂) × ℝ) := z⁻¹ • ν₀
  have hνprob : IsProbabilityMeasure ν := by
    constructor
    exact ENNReal.inv_mul_cancel hzpos.ne' hzfinite
  have hnormalized {I : Type} [MeasurableSpace I] [MeasurableSingletonClass I]
      [DecidableEq I] (ℓ : (Fin n₁ × Fin n₂) → I) (π : I → ℝ)
      (hπ : ∀ i, 0 ≤ π i)
      (hbound : ∀ x i, (∑ a, if ℓ a = i then g a x else 0) ≤ ENNReal.ofReal (S * π i))
      (i : I) (U : Set ℝ) (hU : MeasurableSet U) :
      ν {p | ℓ p.1 = i ∧ p.2 ∈ U} ≤
        ENNReal.ofReal (windowVolume * S / q * π i) * volume U := by
    have hbase : ν₀ {p | ℓ p.1 = i ∧ p.2 ∈ U} ≤ ENNReal.ofReal (S * π i) * volume U := by
      calc
        _ ≤ ENNReal.ofReal (S * π i) * τ U :=
          indexedLaw_label_bound τ w hw ℓ i _ (fun t => hbound _ i) hU
        _ ≤ ENNReal.ofReal (S * π i) * volume U :=
          mul_le_mul' le_rfl (show τ U ≤ volume U from Measure.restrict_le_self U)
    calc
      ν {p | ℓ p.1 = i ∧ p.2 ∈ U} = z⁻¹ * ν₀ {p | ℓ p.1 = i ∧ p.2 ∈ U} := rfl
      _ ≤ ENNReal.ofReal (windowVolume / q) *
          (ENNReal.ofReal (S * π i) * volume U) := mul_le_mul' hinv hbase
      _ = ENNReal.ofReal (windowVolume * S / q * π i) * volume U := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (div_nonneg windowVolume_pos.le hq.le)]
        congr 2
        ring
  have hν₀supp : ∀ᵐ p ∂ν₀,
      p.2 ∈ Icc (0 : ℝ) 1 ∧ (p.1, y + (windowStep * p.2) • v) ∈ E := by
    apply indexedLaw_ae τ w hw
    intro a
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc] with t ht htne
    exact ⟨ht, hgE a _ htne⟩
  refine ⟨y, hy, ν, hνprob, ?_, ?_, ?_⟩
  · exact hnormalized Prod.fst π₁ hπ₁
      (fun x i => by simpa [Fintype.sum_prod_type, Finset.sum_comm] using hg₁ x i)
  · exact hnormalized Prod.snd π₂ hπ₂
      (fun x j => by simpa [Fintype.sum_prod_type] using hg₂ x j)
  · exact Measure.ae_smul_measure hν₀supp z⁻¹

end Submission.Obl.k4_original_prior_line_extraction
