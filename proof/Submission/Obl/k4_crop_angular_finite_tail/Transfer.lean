/- Adapted from this LOT tree, obligation o091, session x0299, commit 918e44ebabf26b3b2fd56f3cccbf12b4ac1bac6e,
Submission/Obl/k4_dyadic_crop_typicality/Transfer.lean. Transfer.lean in that branch was written by session x0302 (9db252b). -/

import Mathlib

/-!
# Abstract density transfer

Densities of observation laws with respect to a product `m × count` with a countable label set:
* `lintegral_prod_count`: an integral over `m × count` is the sum of its label slices;
* `density_le_of_coarsening`: a density of a smaller law at a finer label is at most a density of
  the larger law at the coarser label;
* `sum_lower_ratio_le`: restricted laws concentrated on boundedly overlapping sets have
  densities below `δ` times the full density only on total mass `K δ`;
* `map_pair_const_label`: a law whose label is almost surely constant;
* `map_density_pullback`: densities through a measurable bijection scaling the reference measure.
-/

open MeasureTheory Set Filter
open scoped ENNReal

namespace Submission.Obl.k4_crop_angular_finite_tail

section Slices

variable {Y ι : Type*} [MeasurableSpace Y] [MeasurableSpace ι] [Countable ι]
  [MeasurableSingletonClass ι]

lemma lintegral_prod_count (m : Measure Y) [SFinite m] {f : Y × ι → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ z, f z ∂(m.prod Measure.count) = ∑' i, ∫⁻ y, f (y, i) ∂m := by
  rw [lintegral_prod_symm _ hf.aemeasurable, lintegral_count]

lemma setLIntegral_prod_count (m : Measure Y) [SFinite m] {f : Y × ι → ℝ≥0∞}
    (hf : Measurable f) {U : Set (Y × ι)} (hU : MeasurableSet U) :
    ∫⁻ z in U, f z ∂(m.prod Measure.count) =
      ∑' i, ∫⁻ y in {y | (y, i) ∈ U}, f (y, i) ∂m := by
  rw [← lintegral_indicator hU, lintegral_prod_count m (hf.indicator hU)]
  congr 1
  funext i
  have hUi : MeasurableSet {y : Y | (y, i) ∈ U} := measurable_prodMk_right hU
  rw [← lintegral_indicator hUi]
  congr 1

lemma withDensity_prod_singleton (m : Measure Y) [SFinite m] {D : Y × ι → ℝ≥0∞}
    (hD : Measurable D) {U : Set Y} (hU : MeasurableSet U) (i : ι) :
    ((m.prod Measure.count).withDensity D) (U ×ˢ {i}) = ∫⁻ y in U, D (y, i) ∂m := by
  rw [withDensity_apply _ (hU.prod (measurableSet_singleton i)),
    setLIntegral_prod_count m hD (hU.prod (measurableSet_singleton i))]
  rw [tsum_eq_single i]
  · congr 2
    ext y
    simp
  · intro j hj
    have : {y | (y, j) ∈ U ×ˢ ({i} : Set ι)} = ∅ := by
      ext y
      simp [hj]
    rw [this, Measure.restrict_empty, lintegral_zero_measure]

end Slices

section Coarsening

variable {X Y ι κ : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
  [MeasurableSpace κ] [Countable κ] [MeasurableSingletonClass κ]

/-- Splitting a measure by the value of a countable label. -/
lemma measure_eq_tsum_label (μ : Measure X) {s : X → ι} (hs : Measurable s) {A : Set X}
    (hA : MeasurableSet A) : μ A = ∑' i, μ (A ∩ s ⁻¹' {i}) := by
  rw [← measure_iUnion]
  · congr 1
    ext x
    simp
  · intro i j hij
    exact Disjoint.mono inter_subset_right inter_subset_right
      ((disjoint_singleton.2 hij).preimage s)
  · exact fun i => hA.inter (hs (measurableSet_singleton i))

/-- A density of a smaller law, observed with a finer label, is almost everywhere at most a
density of a larger law observed with a coarser label `J` of it. -/
theorem density_le_of_coarsening (m : Measure Y) [SigmaFinite m]
    {μ μ' : Measure X} (hμ' : μ' ≤ μ)
    {ψ : X → Y} (hψ : Measurable ψ) {s : X → ι} (hs : Measurable s)
    {sc : X → κ} (hsc : Measurable sc) (J : ι → κ) (hJ : ∀ᵐ x ∂μ', sc x = J (s x))
    {D' : Y × ι → ℝ≥0∞} (hD' : Measurable D')
    (h' : μ'.map (fun x => (ψ x, s x)) = (m.prod Measure.count).withDensity D')
    {D : Y × κ → ℝ≥0∞} (hD : Measurable D)
    (h : μ.map (fun x => (ψ x, sc x)) = (m.prod Measure.count).withDensity D) :
    ∀ᵐ z ∂(m.prod Measure.count), D' z ≤ D (z.1, J z.2) := by
  have hJm : Measurable (fun z : Y × ι => D (z.1, J z.2)) :=
    hD.comp (measurable_fst.prodMk ((measurable_of_countable J).comp measurable_snd))
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite hD'
  intro U hU _
  have hpair : Measurable (fun x => (ψ x, s x)) := hψ.prodMk hs
  have hpairc : Measurable (fun x => (ψ x, sc x)) := hψ.prodMk hsc
  calc ∫⁻ z in U, D' z ∂(m.prod Measure.count)
      = μ' ((fun x => (ψ x, s x)) ⁻¹' U) := by
        rw [← withDensity_apply _ hU, ← h', Measure.map_apply hpair hU]
    _ = ∑' i, μ' ((fun x => (ψ x, s x)) ⁻¹' U ∩ s ⁻¹' {i}) :=
        measure_eq_tsum_label μ' hs (hpair hU)
    _ ≤ ∑' i, μ ((fun x => (ψ x, sc x)) ⁻¹' ({y | (y, i) ∈ U} ×ˢ {J i})) := by
        refine ENNReal.tsum_le_tsum fun i => ?_
        calc μ' ((fun x => (ψ x, s x)) ⁻¹' U ∩ s ⁻¹' {i})
            ≤ μ' ((fun x => (ψ x, sc x)) ⁻¹' ({y | (y, i) ∈ U} ×ˢ {J i})) := by
              apply measure_mono_ae
              filter_upwards [hJ] with x hx hmem
              obtain ⟨hU', hi⟩ := hmem
              simp only [mem_preimage, mem_singleton_iff] at hU' hi
              simp only [mem_preimage, mem_prod, mem_ofPred_eq, mem_singleton_iff]
              subst hi
              exact ⟨hU', hx⟩
          _ ≤ _ := Measure.le_iff'.1 hμ' _
    _ = ∑' i, ∫⁻ y in {y | (y, i) ∈ U}, D (y, J i) ∂m := by
        congr 1
        funext i
        have hUi : MeasurableSet {y : Y | (y, i) ∈ U} := measurable_prodMk_right hU
        rw [← Measure.map_apply hpairc (hUi.prod (measurableSet_singleton _)), h,
          withDensity_prod_singleton m hD hUi]
    _ = ∫⁻ z in U, D (z.1, J z.2) ∂(m.prod Measure.count) :=
        (setLIntegral_prod_count m hJm hU).symm

/-- A law whose label is almost surely `i₀`. -/
theorem map_pair_const_label (m : Measure Y) [SFinite m] {μ : Measure X}
    {ψ : X → Y} (hψ : Measurable ψ) {s : X → ι} (i₀ : ι)
    (hconst : ∀ᵐ x ∂μ, s x = i₀) {H : Y → ℝ≥0∞} (hH : Measurable H)
    (hlaw : μ.map ψ = m.withDensity H) :
    μ.map (fun x => (ψ x, s x)) =
      (m.prod Measure.count).withDensity ({z | z.2 = i₀}.indicator (fun z => H z.1)) := by
  have hmeas : Measurable ({z : Y × ι | z.2 = i₀}.indicator (fun z => H z.1)) :=
    (hH.comp measurable_fst).indicator (measurable_snd (measurableSet_singleton i₀))
  have hcongr : μ.map (fun x => (ψ x, s x)) = μ.map (fun x => (ψ x, i₀)) := by
    apply Measure.map_congr
    filter_upwards [hconst] with x hx
    rw [hx]
  rw [hcongr]
  ext U hU
  rw [Measure.map_apply (hψ.prodMk measurable_const) hU, withDensity_apply _ hU,
    setLIntegral_prod_count m hmeas hU, tsum_eq_single i₀]
  · have : (fun x => (ψ x, i₀)) ⁻¹' U = ψ ⁻¹' {y | (y, i₀) ∈ U} := rfl
    have hUi : MeasurableSet {y : Y | (y, i₀) ∈ U} := measurable_prodMk_right hU
    rw [this, ← Measure.map_apply hψ hUi, hlaw, withDensity_apply _ hUi]
    congr 1
    funext y
    simp [Set.indicator]
  · intro j hj
    have : ∀ y, ({z : Y × ι | z.2 = i₀}.indicator (fun z => H z.1)) (y, j) = 0 := by
      intro y
      simp [Set.indicator, hj]
    simp [this]

end Coarsening

section Overlap

variable {X Z Γ : Type*} [MeasurableSpace X] [MeasurableSpace Z] [Fintype Γ]

/-- Restricted laws concentrated on sets of bounded overlap `K` have densities below `δ` times the
full density only on total original mass `K δ`. -/
theorem sum_lower_ratio_le (ref : Measure Z) (μ : Measure X)
    {Φ : X → Z} (hΦ : Measurable Φ) {G : Z → ℝ≥0∞} (hG : Measurable G)
    (hlaw : μ.map Φ = ref.withDensity G)
    (S : Γ → Set X)
    (D : Γ → Z → ℝ≥0∞) (hD : ∀ γ, Measurable (D γ))
    (hlawγ : ∀ γ, (μ.restrict (S γ)).map Φ = ref.withDensity (D γ))
    (C : Γ → Set Z) (hC : ∀ γ, MeasurableSet (C γ))
    (hsupp : ∀ γ, ∀ᵐ x ∂(μ.restrict (S γ)), Φ x ∈ C γ)
    (K : ℝ≥0∞) (hK : ∀ z, ∑ γ, (C γ).indicator (fun _ => (1 : ℝ≥0∞)) z ≤ K) (δ : ℝ≥0∞) :
    ∑ γ, μ (S γ ∩ {x | D γ (Φ x) < δ * G (Φ x)}) ≤ K * δ * μ univ := by
  have hB : ∀ γ, MeasurableSet {z | D γ z < δ * G z} := fun γ =>
    measurableSet_lt (hD γ) (measurable_const.mul hG)
  have hterm : ∀ γ, μ (S γ ∩ {x | D γ (Φ x) < δ * G (Φ x)}) ≤
      ∫⁻ z, δ * (C γ).indicator G z ∂ref := by
    intro γ
    have hzero : (ref.withDensity (D γ)) (C γ)ᶜ = 0 := by
      rw [← hlawγ γ, Measure.map_apply hΦ (hC γ).compl]
      exact ae_iff.1 (hsupp γ)
    calc μ (S γ ∩ {x | D γ (Φ x) < δ * G (Φ x)})
        = (ref.withDensity (D γ)) {z | D γ z < δ * G z} := by
          rw [← hlawγ γ, Measure.map_apply hΦ (hB γ), Measure.restrict_apply (hΦ (hB γ)),
            inter_comm]
          rfl
      _ ≤ (ref.withDensity (D γ)) ({z | D γ z < δ * G z} ∩ C γ) +
            (ref.withDensity (D γ)) (C γ)ᶜ := by
          calc (ref.withDensity (D γ)) {z | D γ z < δ * G z}
              ≤ (ref.withDensity (D γ)) (({z | D γ z < δ * G z} ∩ C γ) ∪ (C γ)ᶜ) := by
                apply measure_mono
                intro z hz
                by_cases hzC : z ∈ C γ
                · exact Or.inl ⟨hz, hzC⟩
                · exact Or.inr hzC
            _ ≤ _ := measure_union_le _ _
      _ = ∫⁻ z in {z | D γ z < δ * G z} ∩ C γ, D γ z ∂ref := by
          rw [hzero, add_zero, withDensity_apply _ ((hB γ).inter (hC γ))]
      _ ≤ ∫⁻ z in {z | D γ z < δ * G z} ∩ C γ, δ * G z ∂ref := by
          apply setLIntegral_mono (measurable_const.mul hG)
          intro z hz
          exact hz.1.le
      _ ≤ ∫⁻ z in C γ, δ * G z ∂ref := lintegral_mono_set inter_subset_right
      _ = ∫⁻ z, δ * (C γ).indicator G z ∂ref := by
          rw [← lintegral_indicator (hC γ)]
          congr 1
          funext z
          by_cases hz : z ∈ C γ <;> simp [Set.indicator, hz]
  calc ∑ γ, μ (S γ ∩ {x | D γ (Φ x) < δ * G (Φ x)})
      ≤ ∑ γ, ∫⁻ z, δ * (C γ).indicator G z ∂ref := Finset.sum_le_sum fun γ _ => hterm γ
    _ = ∫⁻ z, ∑ γ, δ * (C γ).indicator G z ∂ref := by
        rw [lintegral_finsetSum]
        intro γ _
        exact measurable_const.mul (hG.indicator (hC γ))
    _ ≤ ∫⁻ z, δ * (K * G z) ∂ref := by
        apply lintegral_mono
        intro z
        simp only
        rw [← Finset.mul_sum]
        gcongr
        calc ∑ γ, (C γ).indicator G z
            = (∑ γ, (C γ).indicator (fun _ => (1 : ℝ≥0∞)) z) * G z := by
              rw [Finset.sum_mul]
              congr 1
              funext γ
              by_cases hz : z ∈ C γ <;> simp [Set.indicator, hz]
          _ ≤ K * G z := by gcongr; exact hK z
    _ = K * δ * μ univ := by
        have e1 : (fun z => δ * (K * G z)) = fun z => (δ * K) * G z := by
          funext z
          ring
        rw [e1, lintegral_const_mul _ hG]
        have h1 : ∫⁻ z, G z ∂ref = μ univ := by
          rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ, ← hlaw,
            Measure.map_apply hΦ MeasurableSet.univ, preimage_univ]
        rw [h1]
        ring

/-- A sub-law of a law with a density has a density. -/
theorem exists_density_of_le (ref : Measure Z) [SigmaFinite ref] {μ μ' : Measure X}
    [IsFiniteMeasure μ] (hμ' : μ' ≤ μ) {Φ : X → Z} (hΦ : Measurable Φ) {G : Z → ℝ≥0∞}
    (hlaw : μ.map Φ = ref.withDensity G) :
    ∃ D : Z → ℝ≥0∞, Measurable D ∧ μ'.map Φ = ref.withDensity D := by
  have hle : μ'.map Φ ≤ μ.map Φ := Measure.map_mono hμ' hΦ
  have hac : μ'.map Φ ≪ ref := by
    have h1 : μ.map Φ ≪ ref := hlaw ▸ withDensity_absolutelyContinuous ref G
    exact (Measure.absolutelyContinuous_of_le hle).trans h1
  have : IsFiniteMeasure μ' := isFiniteMeasure_of_le μ hμ'
  exact ⟨(μ'.map Φ).rnDeriv ref, Measure.measurable_rnDeriv _ _,
    (Measure.withDensity_rnDeriv_eq _ _ hac).symm⟩

/-- An almost everywhere property of the reference holds along observations. -/
lemma ae_comp_of_ae {ref : Measure Z} {μ : Measure X} {Φ : X → Z}
    (hΦ : Measurable Φ) {D : Z → ℝ≥0∞} (hlaw : μ.map Φ = ref.withDensity D)
    {P : Set Z} (hP : MeasurableSet P) (h : ∀ᵐ z ∂ref, z ∈ P) : ∀ᵐ x ∂μ, Φ x ∈ P := by
  have hmap : ∀ᵐ z ∂(μ.map Φ), z ∈ P := by
    rw [hlaw]
    exact (withDensity_absolutelyContinuous ref D).ae_le h
  exact (ae_map_iff hΦ.aemeasurable hP).mp hmap

end Overlap

section Pullback

variable {X X' Y : Type*} [MeasurableSpace X] [MeasurableSpace X'] [MeasurableSpace Y]

lemma map_symm_withDensity (A : Y ≃ᵐ Y) (m : Measure Y) (g : Y → ℝ≥0∞) :
    (m.withDensity g).map A.symm = (m.map A.symm).withDensity (fun y => g (A y)) := by
  ext U hU
  rw [Measure.map_apply A.symm.measurable hU, withDensity_apply _ (A.symm.measurable hU),
    withDensity_apply _ hU, Measure.restrict_map A.symm.measurable hU, lintegral_map_equiv]
  simp

/-- Densities through a measurable bijection `A` scaling the reference measure by `s`, for a law
which is `c` times the image of another one. -/
theorem map_density_pullback (e : X → X') (he : Measurable e) (A : Y ≃ᵐ Y) {m : Measure Y}
    {s c : ℝ≥0∞} (hs0 : s ≠ 0) (hsT : s ≠ ∞) (hA : m.map A = s • m)
    {μ : Measure X'} {μ' : Measure X} (hμ : μ = c • μ'.map e) (hc0 : c ≠ 0) (hcT : c ≠ ∞)
    {φ : X' → Y} {ψ : X → Y} (hφ : Measurable φ) (hψ : Measurable ψ)
    (hconj : ∀ x, φ (e x) = A (ψ x))
    {g : Y → ℝ≥0∞} (hlaw : μ.map φ = m.withDensity g) :
    μ'.map ψ = m.withDensity (fun y => c⁻¹ * s⁻¹ * g (A y)) := by
  have hmapA : (μ'.map ψ).map A = c⁻¹ • m.withDensity g := by
    rw [← hlaw, hμ, Measure.map_smul _ hφ.aemeasurable, Measure.map_map hφ he,
      Measure.map_map A.measurable hψ,
      smul_smul, ENNReal.inv_mul_cancel hc0 hcT, one_smul]
    congr 1
    funext x
    exact (hconj x).symm
  have hsymm : m.map A.symm = s⁻¹ • m := by
    have h1 : (m.map A).map A.symm = m := A.map_symm_map
    rw [hA, Measure.map_smul _ A.symm.measurable.aemeasurable] at h1
    calc m.map A.symm = s⁻¹ • (s • m.map A.symm) := by
          rw [smul_smul, ENNReal.inv_mul_cancel hs0 hsT, one_smul]
      _ = s⁻¹ • m := by rw [h1]
  calc μ'.map ψ = ((μ'.map ψ).map A).map A.symm := A.map_symm_map.symm
    _ = (c⁻¹ • m.withDensity g).map A.symm := by rw [hmapA]
    _ = c⁻¹ • (m.map A.symm).withDensity (fun y => g (A y)) := by
        rw [Measure.map_smul _ A.symm.measurable.aemeasurable, map_symm_withDensity]
    _ = c⁻¹ • (s⁻¹ • m).withDensity (fun y => g (A y)) := by rw [hsymm]
    _ = m.withDensity (fun y => c⁻¹ * s⁻¹ * g (A y)) := by
        rw [withDensity_smul_measure]
        have e1 : (fun y => c⁻¹ * s⁻¹ * g (A y)) = c⁻¹ • (s⁻¹ • fun y => g (A y)) := by
          funext y
          simp [mul_assoc]
        rw [e1, withDensity_smul' _ _ (ENNReal.inv_ne_top.2 hc0),
          withDensity_smul' _ _ (ENNReal.inv_ne_top.2 hs0)]

end Pullback

end Submission.Obl.k4_crop_angular_finite_tail
