import Mathlib
set_option autoImplicit false

/-! Covering and offset estimates for observation densities: if a new discrete label
determines the old fine label up to finitely many offsets, the new density is dominated
by the sum of shifted old densities, and its large values carry at most a fixed multiple
of the old large-density mass. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder.Cmp

open MeasureTheory Set
open scoped ENNReal

section Cover

variable {X I : Type*} [MeasurableSpace X] [MeasurableSpace I] [MeasurableSingletonClass I]
  [Countable I]

theorem setLIntegral_prod_count_singleton (ρ : Measure X) [SFinite ρ]
    {H : X × I → ℝ≥0∞} (hH : Measurable H) (Y : Set X) (d : I) :
    ∫⁻ p in Y ×ˢ {d}, H p ∂(ρ.prod Measure.count) = ∫⁻ o in Y, H (o, d) ∂ρ := by
  rw [← Measure.prod_restrict, Measure.restrict_singleton, Measure.count_singleton, one_smul,
    lintegral_prod _ hH.aemeasurable]
  simp

theorem withDensity_prod_count_singleton (ρ : Measure X) [SFinite ρ]
    {H : X × I → ℝ≥0∞} (hH : Measurable H) {Y : Set X} (hY : MeasurableSet Y) (d : I) :
    (ρ.prod Measure.count).withDensity H (Y ×ˢ {d}) = ∫⁻ o in Y, H (o, d) ∂ρ := by
  rw [withDensity_apply _ (hY.prod (measurableSet_singleton d)),
    setLIntegral_prod_count_singleton ρ hH Y d]

end Cover


theorem map_add_count {I : Type*} [MeasurableSpace I] [MeasurableSingletonClass I]
    [Countable I] [AddGroup I] (Δ : I) :
    Measure.map (fun d : I => d + Δ) (Measure.count : Measure I) = Measure.count := by
  ext S hS
  rw [Measure.map_apply (measurable_of_countable _) hS]
  have h : (fun d : I => d + Δ) ⁻¹' S = (fun d : I => d + -Δ) '' S := by
    ext d
    simp only [mem_preimage, mem_image]
    constructor
    · intro hd; exact ⟨d + Δ, hd, by simp [add_assoc]⟩
    · rintro ⟨e, he, rfl⟩; simpa [add_assoc] using he
  rw [h, Measure.count_injective_image (add_left_injective _)]

theorem measurePreserving_shift {X I : Type*} [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [Countable I] [AddGroup I] (ρ : Measure X) [SigmaFinite ρ]
    (Δ : I) :
    MeasurePreserving (fun p : X × I => (p.1, p.2 + Δ)) (ρ.prod Measure.count)
      (ρ.prod Measure.count) := by
  refine ⟨measurable_fst.prodMk ((measurable_of_countable (fun d : I => d + Δ)).comp
    measurable_snd), ?_⟩
  have := Measure.map_prod_map ρ (Measure.count : Measure I) measurable_id
    (measurable_of_countable (fun d : I => d + Δ))
  rw [Measure.map_id, map_add_count] at this
  exact this.symm

/-- **Offset bad mass.** The mass where a sum of old densities over finitely many label
offsets is large is at most twice the number of offsets times the mass where the old
density itself is large. -/
theorem offset_bad_mass {Ω X I : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [MeasurableSpace I] [MeasurableSingletonClass I] [Countable I] [AddGroup I]
    (μ : Measure Ω) (ρ : Measure X) [SigmaFinite ρ]
    (Jf : Ω → X × I) (hJf : Measurable Jf)
    {H : X × I → ℝ≥0∞} (hH : Measurable H)
    (hlawH : μ.map Jf = (ρ.prod Measure.count).withDensity H)
    (Off : Finset I) (X₀ : ℝ≥0∞) :
    μ {z | (Off.card : ℝ≥0∞) * X₀ < ∑ Δ ∈ Off, H ((Jf z).1, (Jf z).2 + Δ)} ≤
      2 * Off.card * μ {z | X₀ < H (Jf z)} := by
  classical
  set ref := ρ.prod (Measure.count : Measure I)
  have hshift : ∀ Δ : I, Measurable (fun p : X × I => H (p.1, p.2 + Δ)) := fun Δ =>
    hH.comp (measurePreserving_shift ρ Δ).measurable
  have hbad : MeasurableSet {p : X × I | X₀ < H p} := measurableSet_lt measurable_const hH
  -- each offset costs at most twice the bad mass
  have hone : ∀ Δ : I, μ {z | X₀ < H ((Jf z).1, (Jf z).2 + Δ)} ≤ 2 * μ {z | X₀ < H (Jf z)} := by
    intro Δ
    have hsetΔ : MeasurableSet {p : X × I | X₀ < H (p.1, p.2 + Δ)} :=
      measurableSet_lt measurable_const (hshift Δ)
    have e1 : μ {z | X₀ < H ((Jf z).1, (Jf z).2 + Δ)} =
        ∫⁻ p in {p : X × I | X₀ < H (p.1, p.2 + Δ)}, H p ∂ref := by
      rw [← withDensity_apply _ hsetΔ, ← hlawH, Measure.map_apply hJf hsetΔ]
      rfl
    have e2 : μ {z | X₀ < H (Jf z)} = ∫⁻ p in {p : X × I | X₀ < H p}, H p ∂ref := by
      rw [← withDensity_apply _ hbad, ← hlawH, Measure.map_apply hJf hbad]
      rfl
    rw [e1, e2, two_mul]
    calc ∫⁻ p in {p : X × I | X₀ < H (p.1, p.2 + Δ)}, H p ∂ref
        ≤ ∫⁻ p, {p : X × I | X₀ < H p}.indicator H p +
            {p : X × I | X₀ < H (p.1, p.2 + Δ)}.indicator (fun p => H (p.1, p.2 + Δ)) p ∂ref := by
          rw [← lintegral_indicator hsetΔ]
          apply lintegral_mono
          intro p
          dsimp only
          by_cases h1 : X₀ < H (p.1, p.2 + Δ)
          · rw [indicator_of_mem (show p ∈ {p : X × I | X₀ < H (p.1, p.2 + Δ)} from h1),
              indicator_of_mem (show p ∈ {p : X × I | X₀ < H (p.1, p.2 + Δ)} from h1)]
            by_cases h2 : X₀ < H p
            · rw [indicator_of_mem (show p ∈ {p : X × I | X₀ < H p} from h2)]
              exact le_self_add
            · rw [indicator_of_notMem (show p ∉ {p : X × I | X₀ < H p} from h2), zero_add]
              exact (le_of_not_gt h2).trans h1.le
          · rw [indicator_of_notMem (show p ∉ {p : X × I | X₀ < H (p.1, p.2 + Δ)} from h1)]
            exact zero_le
      _ = ∫⁻ p in {p : X × I | X₀ < H p}, H p ∂ref +
            ∫⁻ p in {p : X × I | X₀ < H (p.1, p.2 + Δ)}, H (p.1, p.2 + Δ) ∂ref := by
          rw [lintegral_add_left (hH.indicator hbad), lintegral_indicator hbad,
            lintegral_indicator hsetΔ]
      _ = ∫⁻ p in {p : X × I | X₀ < H p}, H p ∂ref +
            ∫⁻ p in {p : X × I | X₀ < H p}, H p ∂ref := by
          congr 1
          rw [← lintegral_indicator hsetΔ, ← lintegral_indicator hbad]
          have := (measurePreserving_shift ρ Δ).lintegral_comp
            (f := {p : X × I | X₀ < H p}.indicator H) (hH.indicator hbad)
          rw [← this]
          rfl
  -- union over offsets
  have hsub : {z | (Off.card : ℝ≥0∞) * X₀ < ∑ Δ ∈ Off, H ((Jf z).1, (Jf z).2 + Δ)} ⊆
      ⋃ Δ ∈ Off, {z | X₀ < H ((Jf z).1, (Jf z).2 + Δ)} := by
    intro z hz
    by_contra hnot
    simp only [mem_iUnion, mem_ofPred_eq, not_exists, not_lt] at hnot
    have : ∑ Δ ∈ Off, H ((Jf z).1, (Jf z).2 + Δ) ≤ (Off.card : ℝ≥0∞) * X₀ := by
      calc ∑ Δ ∈ Off, H ((Jf z).1, (Jf z).2 + Δ) ≤ ∑ _Δ ∈ Off, X₀ :=
            Finset.sum_le_sum fun Δ hΔ => hnot Δ hΔ
        _ = _ := by simp
    exact (not_lt_of_ge this) hz
  calc _ ≤ μ (⋃ Δ ∈ Off, {z | X₀ < H ((Jf z).1, (Jf z).2 + Δ)}) := measure_mono hsub
    _ ≤ ∑ Δ ∈ Off, μ {z | X₀ < H ((Jf z).1, (Jf z).2 + Δ)} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _Δ ∈ Off, 2 * μ {z | X₀ < H (Jf z)} := Finset.sum_le_sum fun Δ _ => hone Δ
    _ = _ := by simp [mul_assoc, mul_left_comm]


/-- **Covering density bound.** If a law `G` in the old continuous coordinates
satisfies `c • map Jn μ = withDensity G`, and the new discrete label determines the
old fine label up to the offsets `Off`, then almost surely the new density is at most
`c` times the sum of the old fine densities over the offsets. -/
theorem cover_density_ae {Ω X I I' : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [MeasurableSpace I] [MeasurableSingletonClass I] [Countable I] [AddCommGroup I]
    [MeasurableSpace I'] [MeasurableSingletonClass I'] [Countable I']
    (μ : Measure Ω) (ρ : Measure X) [SigmaFinite ρ]
    (Jf : Ω → X × I) (hJf : Measurable Jf) (Jn : Ω → X × I') (hJn : Measurable Jn)
    (hcont : ∀ z, (Jn z).1 = (Jf z).1)
    {H : X × I → ℝ≥0∞} (hH : Measurable H)
    (hlawH : μ.map Jf = (ρ.prod Measure.count).withDensity H)
    {G : X × I' → ℝ≥0∞} (hG : Measurable G) (c : ℝ≥0∞)
    (hlawG : c • μ.map Jn = (ρ.prod Measure.count).withDensity G)
    (Off : Finset I) (hOff : ∀ z z', (Jn z).2 = (Jn z').2 → (Jf z').2 - (Jf z).2 ∈ Off) :
    ∀ᵐ z ∂μ, G (Jn z) ≤ c * ∑ Δ ∈ Off, H ((Jf z).1, (Jf z).2 + Δ) := by
  classical
  -- the bound at almost every continuous point, for each realized pair of labels
  have hpair : ∀ (d' : I') (d₀ : I), (∃ z₀, (Jn z₀).2 = d' ∧ (Jf z₀).2 = d₀) →
      ∀ᵐ o ∂ρ, G (o, d') ≤ c * ∑ Δ ∈ Off, H (o, d₀ + Δ) := by
    rintro d' d₀ ⟨z₀, hz₀n, hz₀f⟩
    have hGd : Measurable fun o => G (o, d') := hG.comp (measurable_id.prodMk measurable_const)
    have hHd : Measurable fun o => c * ∑ Δ ∈ Off, H (o, d₀ + Δ) :=
      measurable_const.mul (Finset.measurable_sum _ fun Δ _ =>
        hH.comp (measurable_id.prodMk measurable_const))
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite hGd
    intro Y hY _
    have hYd : ∀ d : I, MeasurableSet (Y ×ˢ ({d} : Set I)) := fun d =>
      hY.prod (measurableSet_singleton d)
    have hYd' : MeasurableSet (Y ×ˢ ({d'} : Set I')) := hY.prod (measurableSet_singleton d')
    have hleft : ∫⁻ o in Y, G (o, d') ∂ρ = c * μ (Jn ⁻¹' (Y ×ˢ {d'})) := by
      rw [← withDensity_prod_count_singleton ρ hG hY d', ← hlawG, Measure.smul_apply,
        Measure.map_apply hJn hYd', smul_eq_mul]
    have hsub : Jn ⁻¹' (Y ×ˢ {d'}) ⊆ ⋃ Δ ∈ Off, Jf ⁻¹' (Y ×ˢ {d₀ + Δ}) := by
      intro z hz
      simp only [mem_preimage, mem_prod, mem_singleton_iff] at hz
      simp only [mem_iUnion, mem_preimage, mem_prod, mem_singleton_iff]
      refine ⟨(Jf z).2 - d₀, ?_, ?_, by abel⟩
      · rw [← hz₀f]; exact hOff z₀ z (by rw [hz.2, hz₀n])
      · rw [← hcont]; exact hz.1
    have hright : ∀ Δ : I, μ (Jf ⁻¹' (Y ×ˢ {d₀ + Δ})) = ∫⁻ o in Y, H (o, d₀ + Δ) ∂ρ := by
      intro Δ
      rw [← Measure.map_apply hJf (hYd _), hlawH, withDensity_prod_count_singleton ρ hH hY]
    calc ∫⁻ o in Y, G (o, d') ∂ρ = c * μ (Jn ⁻¹' (Y ×ˢ {d'})) := hleft
      _ ≤ c * ∑ Δ ∈ Off, μ (Jf ⁻¹' (Y ×ˢ {d₀ + Δ})) := by
          gcongr
          exact (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
      _ = c * ∑ Δ ∈ Off, ∫⁻ o in Y, H (o, d₀ + Δ) ∂ρ := by simp_rw [hright]
      _ = c * ∫⁻ o in Y, ∑ Δ ∈ Off, H (o, d₀ + Δ) ∂ρ := by
          congr 1
          exact (lintegral_finsetSum _ fun Δ _ =>
            hH.comp (measurable_id.prodMk measurable_const)).symm
      _ = ∫⁻ o in Y, c * ∑ Δ ∈ Off, H (o, d₀ + Δ) ∂ρ :=
          (lintegral_const_mul c (Finset.measurable_sum _ fun Δ _ =>
            hH.comp (measurable_id.prodMk measurable_const))).symm
  -- all pairs at once
  have hall : ∀ᵐ o ∂ρ, ∀ (d' : I') (d₀ : I), (∃ z₀, (Jn z₀).2 = d' ∧ (Jf z₀).2 = d₀) →
      G (o, d') ≤ c * ∑ Δ ∈ Off, H (o, d₀ + Δ) := by
    rw [ae_all_iff]; intro d'
    rw [ae_all_iff]; intro d₀
    by_cases h : ∃ z₀, (Jn z₀).2 = d' ∧ (Jf z₀).2 = d₀
    · exact (hpair d' d₀ h).mono fun o ho _ => ho
    · exact ae_of_all _ fun o hh => (h hh).elim
  -- transfer to incidences
  have habs : μ.map Jf ≪ ρ.prod Measure.count := by
    rw [hlawH]; exact withDensity_absolutelyContinuous _ _
  have hprod : ∀ᵐ p ∂(ρ.prod (Measure.count : Measure I)), ∀ (d' : I') (d₀ : I),
      (∃ z₀, (Jn z₀).2 = d' ∧ (Jf z₀).2 = d₀) →
      G (p.1, d') ≤ c * ∑ Δ ∈ Off, H (p.1, d₀ + Δ) :=
    Measure.QuasiMeasurePreserving.ae (Measure.quasiMeasurePreserving_fst) hall
  have hz := ae_of_ae_map hJf.aemeasurable (habs.ae_le hprod)
  filter_upwards [hz] with z hz
  have := hz (Jn z).2 (Jf z).2 ⟨z, rfl, rfl⟩
  rwa [show Jn z = ((Jf z).1, (Jn z).2) from Prod.ext (hcont z) rfl]


/-- **Covering bad mass.** Under the hypotheses of `cover_density_ae`, the mass where the
new density exceeds `c · #Off · X₀` is at most `2 #Off` times the mass where the old fine
density exceeds `X₀`. -/
theorem cover_bad_mass {Ω X I I' : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [MeasurableSpace I] [MeasurableSingletonClass I] [Countable I] [AddCommGroup I]
    [MeasurableSpace I'] [MeasurableSingletonClass I'] [Countable I']
    (μ : Measure Ω) (ρ : Measure X) [SigmaFinite ρ]
    (Jf : Ω → X × I) (hJf : Measurable Jf) (Jn : Ω → X × I') (hJn : Measurable Jn)
    (hcont : ∀ z, (Jn z).1 = (Jf z).1)
    {H : X × I → ℝ≥0∞} (hH : Measurable H)
    (hlawH : μ.map Jf = (ρ.prod Measure.count).withDensity H)
    {G : X × I' → ℝ≥0∞} (hG : Measurable G) (c : ℝ≥0∞)
    (hlawG : c • μ.map Jn = (ρ.prod Measure.count).withDensity G)
    (Off : Finset I) (hOff : ∀ z z', (Jn z).2 = (Jn z').2 → (Jf z').2 - (Jf z).2 ∈ Off)
    (X₀ : ℝ≥0∞) :
    μ {z | c * ((Off.card : ℝ≥0∞) * X₀) < G (Jn z)} ≤
      2 * Off.card * μ {z | X₀ < H (Jf z)} := by
  have hae := cover_density_ae μ ρ Jf hJf Jn hJn hcont hH hlawH hG c hlawG Off hOff
  calc μ {z | c * ((Off.card : ℝ≥0∞) * X₀) < G (Jn z)}
      ≤ μ {z | (Off.card : ℝ≥0∞) * X₀ < ∑ Δ ∈ Off, H ((Jf z).1, (Jf z).2 + Δ)} := by
        apply measure_mono_ae
        filter_upwards [hae] with z hz hlt
        by_contra hnot
        have hle : ∑ Δ ∈ Off, H ((Jf z).1, (Jf z).2 + Δ) ≤ (Off.card : ℝ≥0∞) * X₀ :=
          le_of_not_gt hnot
        have : G (Jn z) ≤ c * ((Off.card : ℝ≥0∞) * X₀) :=
          hz.trans (by gcongr)
        exact (not_lt_of_ge this) hlt
    _ ≤ _ := offset_bad_mass μ ρ Jf hJf hH hlawH Off X₀

end Submission.Obl.k4_native_calibrated_homogeneous_remainder.Cmp
