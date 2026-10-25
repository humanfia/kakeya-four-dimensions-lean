import Submission.Lib.K4Homogenization.AngularCoarsening
import Submission.Obl.k4_crop_angular_finite_tail.Transfer

namespace Submission.Obl.k4_scalar_chart_normalization

open MeasureTheory Set Filter
open scoped ENNReal

/-- A good submeasure with a conditional density ceiling controls the original
law outside twice the mass that was omitted. -/
theorem angular_high_mass_le_omitted {Ω X V : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace V]
    (ν ξ ζ : Measure Ω) [IsFiniteMeasure ν] (hν : ν = ξ + ζ)
    (ref : Measure X) [SigmaFinite ref] (κ : Measure V) [SigmaFinite κ]
    (obs : Ω → X) (hobs : Measurable obs) (ang : Ω → V) (hang : Measurable ang)
    (f : X → ENNReal) (F : X × V → ENNReal)
    (hf : Measurable f) (hF : Measurable F)
    (hpure : ν.map obs = ref.withDensity f)
    (hjoint : ν.map (fun p => (obs p, ang p)) = (ref.prod κ).withDensity F)
    (c : ENNReal) (hgood : ξ.map (fun p => (obs p, ang p)) ≤ c • (ν.map obs).prod κ) :
    ν {p | 2 * c * f (obs p) < F (obs p, ang p)} ≤ 2 * ζ univ := by
  have hff : Measurable (fun z : X × V => f z.1) := hf.comp measurable_fst
  let A : Set (X × V) := {z | 2 * c * f z.1 < F z}
  have hA : MeasurableSet A :=
    measurableSet_lt (measurable_const.mul (hf.comp measurable_fst)) hF
  let o : Ω → X × V := fun p => (obs p, ang p)
  have ho : Measurable o := hobs.prodMk hang
  have hgood' := hgood A
  rw [Measure.map_apply ho hA, hpure, prod_withDensity_left hf,
    Measure.smul_apply, withDensity_apply _ hA] at hgood'
  have h2 : 2 * ξ (o ⁻¹' A) ≤ ν (o ⁻¹' A) := by
    calc
      _ ≤ 2 * (c * ∫⁻ z in A, f z.1 ∂ref.prod κ) := mul_le_mul' le_rfl hgood'
      _ = ∫⁻ z in A, 2 * c * f z.1 ∂ref.prod κ := by
        rw [lintegral_const_mul (2 * c) hff]
        exact (mul_assoc 2 c _).symm
      _ ≤ ∫⁻ z in A, F z ∂ref.prod κ := setLIntegral_mono' hA (fun z hz => hz.le)
      _ = ν (o ⁻¹' A) := by
        rw [← withDensity_apply _ hA, ← hjoint, Measure.map_apply ho hA]
  have hsplit : ν (o ⁻¹' A) = ξ (o ⁻¹' A) + ζ (o ⁻¹' A) := by
    rw [hν, Measure.add_apply]
  have hξfinite : ξ (o ⁻¹' A) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (measure_ne_top ν _)
    rw [hsplit]
    exact le_self_add
  rw [two_mul, hsplit] at h2
  have hle : ξ (o ⁻¹' A) ≤ ζ (o ⁻¹' A) :=
    (ENNReal.add_le_add_iff_left hξfinite).mp h2
  change ν (o ⁻¹' A) ≤ _
  rw [hsplit, two_mul]
  exact add_le_add (hle.trans (measure_mono (subset_univ _))) (measure_mono (subset_univ _))


/-- The incidence law splits exactly according to a finite measurable label. -/
theorem measure_eq_sum_label {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (ν : Measure Ω) (tag : Ω → ι) (htag : Measurable tag) :
    ν = ∑ i, ν.restrict (tag ⁻¹' {i}) := by
  classical
  ext S hS
  simp only [Measure.finsetSum_apply, Measure.restrict_apply hS]
  exact (Submission.Obl.k4_crop_angular_finite_tail.measure_eq_tsum_label ν htag hS).trans
    (tsum_fintype _)

/-- Upper bounds on a density can be applied after restricting to a set in
observation space. -/
theorem restrict_observation_le {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (ν : Measure Ω) (ref : Measure X) (obs : Ω → X) (hobs : Measurable obs)
    (f g : X → ENNReal) (hlaw : ν.map obs = ref.withDensity f)
    (S : Set X) (hS : MeasurableSet S) (hfg : ∀ z ∈ S, f z ≤ g z) :
    (ν.restrict (obs ⁻¹' S)).map obs ≤ ref.withDensity g := by
  rw [← Measure.restrict_map hobs hS, hlaw, restrict_withDensity hS,
    ← withDensity_indicator hS]
  apply withDensity_mono
  filter_upwards [] with z
  by_cases hz : z ∈ S
  · simpa only [Set.indicator_of_mem hz] using hfg z hz
  · simp only [Set.indicator_of_notMem hz, zero_le]


/-- A conditional angular ceiling survives an observation obtained by adjoining
finitely many labels and then forgetting information. The two losses are explicit. -/
theorem finite_label_angular_coarsening {Ω X Y V ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace V]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [Fintype ι]
    (ν : Measure Ω) [IsFiniteMeasure ν]
    (ref : Measure X) [SigmaFinite ref] (ref' : Measure Y) [SigmaFinite ref']
    (κ : Measure V) [SigmaFinite κ]
    (obs : Ω → X) (hobs : Measurable obs) (obs' : Ω → Y) (hobs' : Measurable obs')
    (ang : Ω → V) (hang : Measurable ang)
    (tag : Ω → ι) (htag : Measurable tag) (q : ι → X → Y) (hq : ∀ i, Measurable (q i))
    (hrec : ∀ p, q (tag p) (obs p) = obs' p)
    (f : X → ENNReal) (G : X × V → ENNReal)
    (f' : Y → ENNReal) (G' : Y × V → ENNReal)
    (hf : Measurable f) (hG : Measurable G) (hf' : Measurable f') (hG' : Measurable G')
    (hpure : ν.map obs = ref.withDensity f)
    (hjoint : ν.map (fun p => (obs p, ang p)) = (ref.prod κ).withDensity G)
    (hpure' : ν.map obs' = ref'.withDensity f')
    (hjoint' : ν.map (fun p => (obs' p, ang p)) = (ref'.prod κ).withDensity G')
    (g : ι → X → ENNReal) (hg : ∀ i, Measurable (g i))
    (htaglaw : ∀ i, (ν.restrict (tag ⁻¹' {i})).map obs = ref.withDensity (g i))
    (c δ : ENNReal) (hδ : δ ≠ 0) (hδtop : δ ≠ ⊤) :
    ν {p | 2 * (c / δ) * f' (obs' p) < G' (obs' p, ang p)} ≤
      2 * (ν {p | c * f (obs p) < G (obs p, ang p)} +
        δ * (Fintype.card ι : ENNReal) * ν univ) := by
  classical
  let o : Ω → X × V := fun p => (obs p, ang p)
  have ho : Measurable o := hobs.prodMk hang
  let OldBad : Set Ω := {p | c * f (obs p) < G (o p)}
  let Low : ι → Set Ω := fun i => {p | g i (obs p) < δ * f (obs p)}
  let Tags : ι → Set Ω := fun i => tag ⁻¹' {i}
  let Bad : Set Ω := OldBad ∪ ⋃ i, Tags i ∩ Low i
  let S : Set Ω := Badᶜ
  have hOld : MeasurableSet OldBad := measurableSet_lt
    (measurable_const.mul (hf.comp hobs)) (hG.comp ho)
  have hLow (i : ι) : MeasurableSet (Low i) := measurableSet_lt
    ((hg i).comp hobs) (measurable_const.mul (hf.comp hobs))
  have hTags (i : ι) : MeasurableSet (Tags i) := htag (measurableSet_singleton i)
  have hBad : MeasurableSet Bad := hOld.union
    (MeasurableSet.iUnion fun i => (hTags i).inter (hLow i))
  have hS : MeasurableSet S := hBad.compl
  have hbadmass : ν Bad ≤ ν OldBad + δ * (Fintype.card ι : ENNReal) * ν univ := by
    calc
      _ ≤ ν OldBad + ν (⋃ i, Tags i ∩ Low i) := measure_union_le _ _
      _ ≤ ν OldBad + ∑ i, ν (Tags i ∩ Low i) := by
        gcongr
        simpa only [tsum_fintype] using measure_iUnion_le (fun i => Tags i ∩ Low i)
      _ ≤ ν OldBad + ∑ _i : ι, δ * ν univ := by
        gcongr with i
        have H := Submission.Lib.K4Homogenization.observation_lowDensity_mass
          ν ref (Tags i) obs hobs δ hf (hg i) hpure (htaglaw i)
        change (ν.restrict (Tags i)) (Low i) ≤ δ * ν univ at H
        simpa only [Measure.restrict_apply (hLow i), inter_comm] using H
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  let ξ := ν.restrict S
  let ξi : ι → Measure Ω := fun i => ξ.restrict (Tags i)
  have hξsplit : ξ = ∑ i, ξi i := measure_eq_sum_label ξ tag htag
  have hνsplit : ν = ∑ i, ν.restrict (Tags i) := measure_eq_sum_label ν tag htag
  have hsource (i : ι) :
      (ξi i).map o ≤ (c / δ) • ((ν.restrict (Tags i)).map obs).prod κ := by
    let H : Set (X × V) := {z | G z ≤ c * f z.1 ∧ δ * f z.1 ≤ g i z.1}
    have hH : MeasurableSet H :=
      (measurableSet_le hG (measurable_const.mul (hf.comp measurable_fst))).inter
        (measurableSet_le (measurable_const.mul (hf.comp measurable_fst))
          ((hg i).comp measurable_fst))
    have hsub : S ∩ Tags i ⊆ o ⁻¹' H := by
      intro p hp
      have hpS : p ∉ Bad := hp.1
      have hpTag : tag p = i := hp.2
      have hn : ¬ (g i (obs p) < δ * f (obs p)) := by
        intro hl
        exact hpS (Or.inr (mem_iUnion.mpr ⟨i, hp.2, hl⟩))
      exact ⟨le_of_not_gt (fun hb => hpS (Or.inl hb)), le_of_not_gt hn⟩
    have hpoint : ∀ z ∈ H, G z ≤ (c / δ) * g i z.1 := by
      intro z hz
      calc
        G z ≤ c * f z.1 := hz.1
        _ = (c / δ) * (δ * f z.1) := by
          rw [div_eq_mul_inv, mul_assoc, ← mul_assoc δ⁻¹, ENNReal.inv_mul_cancel hδ hδtop,
            one_mul]
        _ ≤ _ := mul_le_mul' le_rfl hz.2
    have hupper := restrict_observation_le ν (ref.prod κ) o ho G
      (fun z => (c / δ) * g i z.1) hjoint H hH hpoint
    have hrestr : ξi i ≤ ν.restrict (o ⁻¹' H) := by
      dsimp [ξi, ξ]
      rw [Measure.restrict_restrict (hTags i)]
      exact Measure.restrict_mono (by simpa only [inter_comm] using hsub) le_rfl
    apply (Measure.map_mono hrestr ho).trans
    convert hupper using 1
    rw [htaglaw i, prod_withDensity_left (hg i)]
    have hgg : Measurable (fun z : X × V => g i z.1) := (hg i).comp measurable_fst
    rw [← withDensity_smul _ hgg]
    rfl
  have hpush (i : ι) :
      (ξi i).map (fun p => (obs' p, ang p)) ≤
        (c / δ) • ((ν.restrict (Tags i)).map obs').prod κ := by
    have H := Submission.Lib.K4Homogenization.coarsened_observation_measure_le
      (ν.restrict (Tags i)) (ξi i) κ obs hobs ang hang (q i) (hq i) (c / δ) (hsource i)
    have hrec₁ : ∀ᵐ p ∂ν.restrict (Tags i), q i (obs p) = obs' p := by
      filter_upwards [ae_restrict_mem (hTags i)] with p hp
      have hi : tag p = i := hp
      simpa only [hi] using hrec p
    have hrec₂ : ∀ᵐ p ∂ξi i, q i (obs p) = obs' p := by
      filter_upwards [ae_restrict_mem (μ := ξ) (hTags i)] with p hp
      have hi : tag p = i := hp
      simpa only [hi] using hrec p
    have e₁ : (ν.restrict (Tags i)).map (q i ∘ obs) =
        (ν.restrict (Tags i)).map obs' := Measure.map_congr hrec₁
    have e₂ : (ξi i).map (fun p => (q i (obs p), ang p)) =
        (ξi i).map (fun p => (obs' p, ang p)) :=
      Measure.map_congr (hrec₂.mono fun p hp => congrArg (fun y => (y, ang p)) hp)
    rwa [e₁, e₂] at H
  have hglobal : ξ.map (fun p => (obs' p, ang p)) ≤ (c / δ) • (ν.map obs').prod κ := by
    calc
      _ = ∑ i, (ξi i).map (fun p => (obs' p, ang p)) := by
        rw [hξsplit, Measure.map_finset_sum (hobs'.prodMk hang).aemeasurable]
      _ ≤ ∑ i, (c / δ) • ((ν.restrict (Tags i)).map obs').prod κ :=
        Finset.sum_le_sum fun i _ => hpush i
      _ = _ := by
        rw [← Finset.smul_sum, ← Measure.sum_fintype, ← Measure.prod_sum_left,
          Measure.sum_fintype, ← Measure.map_finset_sum hobs'.aemeasurable, ← hνsplit]
  have H := angular_high_mass_le_omitted ν ξ (ν.restrict Sᶜ)
    (Measure.restrict_add_restrict_compl hS).symm ref' κ obs' hobs' ang hang
    f' G' hf' hG' hpure' hjoint' (c / δ) hglobal
  exact H.trans (mul_le_mul' le_rfl (by simpa only [S, compl_compl, Measure.restrict_apply_univ, OldBad, o] using hbadmass))


/-- Appending a countable discrete label preserves absolute continuity of
the continuous observation. -/
theorem append_discrete_absolutelyContinuous {Ω X ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace ι]
    [Countable ι] [MeasurableSingletonClass ι]
    (ν : Measure Ω) (ref : Measure X) [SFinite ref]
    (z : Ω → X) (hz : Measurable z) (label : Ω → ι) (hl : Measurable label)
    (habs : ν.map z ≪ ref) :
    ν.map (fun p => (z p, label p)) ≪ ref.prod Measure.count := by
  apply Measure.AbsolutelyContinuous.mk
  intro A hA hnull
  have hslices : ∀ i : ι, ref ((fun x => (x, i)) ⁻¹' A) = 0 := by
    rw [Measure.prod_apply_symm hA, lintegral_count, ENNReal.tsum_eq_zero] at hnull
    exact hnull
  have hνslices (i : ι) : ν (z ⁻¹' ((fun x => (x, i)) ⁻¹' A)) = 0 := by
    rw [← Measure.map_apply hz (measurable_prodMk_right hA)]
    exact habs (hslices i)
  rw [Measure.map_apply (hz.prodMk hl) hA]
  apply le_antisymm _ zero_le
  calc
    _ ≤ ν (⋃ i : ι, z ⁻¹' ((fun x => (x, i)) ⁻¹' A)) := by
      apply measure_mono
      intro p hp
      exact mem_iUnion.mpr ⟨label p, hp⟩
    _ ≤ ∑' i : ι, ν (z ⁻¹' ((fun x => (x, i)) ⁻¹' A)) := measure_iUnion_le _
    _ = 0 := by simp only [hνslices, tsum_zero]

/-- Forgetting a countable label preserves absolute continuity of the base. -/
theorem forget_discrete_absolutelyContinuous {Ω X ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace ι]
    [Countable ι] [MeasurableSingletonClass ι]
    (ν : Measure Ω) (ref : Measure X)
    (z : Ω → X) (hz : Measurable z) (label : Ω → ι) (hl : Measurable label)
    (habs : ν.map (fun p => (z p, label p)) ≪ ref.prod Measure.count) :
    ν.map z ≪ ref := by
  apply Measure.AbsolutelyContinuous.mk
  intro A hA hnull
  have hn : (ref.prod (Measure.count : Measure ι)) (A ×ˢ univ) = 0 := by
    rw [Measure.prod_prod, hnull, zero_mul]
  have hν := habs hn
  rw [Measure.map_apply (hz.prodMk hl) (hA.prod MeasurableSet.univ)] at hν
  rw [Measure.map_apply hz hA]
  convert hν using 1
  congr 1
  ext p
  simp only [mem_preimage, mem_prod, mem_univ, and_true]

/-- Any measurable countable refinement of an absolutely continuous observation
has a measurable Radon--Nikodym density. -/
theorem exists_discrete_density {Ω X ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace ι]
    [Countable ι] [MeasurableSingletonClass ι]
    (ν : Measure Ω) [IsFiniteMeasure ν] (ref : Measure X) [SigmaFinite ref]
    (z : Ω → X) (hz : Measurable z) (label : Ω → ι) (hl : Measurable label)
    (habs : ν.map z ≪ ref) :
    ∃ f : X × ι → ENNReal, Measurable f ∧
      ν.map (fun p => (z p, label p)) = (ref.prod Measure.count).withDensity f := by
  have H := append_discrete_absolutelyContinuous ν ref z hz label hl habs
  exact ⟨_, Measure.measurable_rnDeriv _ _, (Measure.withDensity_rnDeriv_eq _ _ H).symm⟩

end Submission.Obl.k4_scalar_chart_normalization
