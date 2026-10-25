/- Adapted from this LOT tree: o199, session x0695, branch x0695,
   commit 9136fa89, Submission/Obl/k4_finite_path_candidate_conversion/AngularCharge.lean.
   This file retains the source's own provenance comments below. -/
import Submission.Lib.K4ListedExceptions.ObservationCaps
import Submission.Lib.K4Homogenization.ObservationBounds
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.ListDensity
import Submission.Obl.k4_remainder_pure_profile_normalization.Overlap

/-!
Angular charging under the original observation law. A label that meets only
V velocity cells has pure marginal density at most V times the joint cap.
Known lists replace the total number of labels in the resulting mass bound.
No measurability is imposed on the original lists.
-/

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

open MeasureTheory Set
open scoped ENNReal

/-- Finite velocity support converts a joint observation cap into a pure
observation cap, without changing or normalizing the source measure. -/
theorem finite_velocity_marginal_bound {Ω X V : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace V]
    [Countable V] [MeasurableSingletonClass V]
    (ρ : Measure Ω) (ν : Measure X) (obs : Ω → X) (vel : Ω → V)
    (hobs : Measurable obs) (hvel : Measurable vel)
    (C : Finset V) {a v : ENNReal}
    (hdom : ρ.map (fun p => (obs p, vel p)) ≤ a • ν.prod Measure.count)
    (hsupport : ρ {p | vel p ∉ C} = 0) (hcard : (C.card : ENNReal) ≤ v) :
    ρ.map obs ≤ (a * v) • ν := by
  classical
  let S : Set (X × V) := univ ×ˢ (C : Set V)
  have hS : MeasurableSet S := MeasurableSet.univ.prod C.finite_toSet.measurableSet
  have hpre : (fun p => (obs p, vel p)) ⁻¹' Sᶜ = {p | vel p ∉ C} := by
    ext p
    simp [S]
  have hfiber (x : X) : Prod.mk x ⁻¹' S = (C : Set V) := by
    ext v
    simp [S]
  apply Measure.le_iff.mpr
  intro U hU
  rw [Measure.map_apply hobs hU, Measure.smul_apply, smul_eq_mul]
  apply Submission.Lib.K4ListedExceptions.observation_base_marginal_bound
    ρ ν Measure.count (fun p => (obs p, vel p)) (hobs.prodMk hvel) S hS
    (by rw [hpre]; exact hsupport)
    hdom (fun x => ?_) U hU
  simpa only [hfiber, Measure.count_apply_finset] using hcard

/-- Integrating a finite family of densities known on lists costs only the
pointwise list size. The lists themselves need not be measurable. -/
theorem listed_density_mass_le {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (ν : Measure X) (f : X → ENNReal) (g : ι → X → ENNReal)
    (hf : Measurable f) (hg : ∀ i, Measurable (g i))
    (lst : X → Finset ι) (C K : ENNReal)
    (hcard : ∀ x, ((lst x).card : ENNReal) ≤ K)
    (hsupport : ∀ᵐ x ∂ν, ∀ i, g i x ≠ 0 → i ∈ lst x)
    (hbound : ∀ᵐ x ∂ν, ∀ i, g i x ≤ C * f x) :
    (∑ i, ∫⁻ x, g i x ∂ν) ≤ C * K * ∫⁻ x, f x ∂ν := by
  classical
  have hpoint : ∀ᵐ x ∂ν, (∑ i, g i x) ≤ C * K * f x := by
    filter_upwards [hsupport, hbound] with x hx hb
    have hsum : (∑ i, g i x) = ∑ i ∈ lst x, g i x := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      exact by_contra fun hne => hi (hx i hne)
    calc
      _ = ∑ i ∈ lst x, g i x := hsum
      _ ≤ ∑ _i ∈ lst x, C * f x := Finset.sum_le_sum fun i _ => hb i
      _ = ((lst x).card : ENNReal) * (C * f x) := by simp [nsmul_eq_mul]
      _ ≤ K * (C * f x) := mul_le_mul' (hcard x) le_rfl
      _ = C * K * f x := by ring
  rw [← lintegral_finsetSum _ (fun i _ => hg i)]
  exact (lintegral_mono_ae hpoint).trans_eq (lintegral_const_mul _ hf)

/-- A pure density lower threshold and capped label densities give the
angular charge with the original total mass on the right. -/
theorem known_lists_capped_density_mass
    {Ω X ι : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    [MeasurableSpace X] [MeasurableEq X] [Fintype ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ν : Measure X) [SigmaFinite ν]
    (obs : Ω → X) (hobs : Measurable obs)
    (g : X → ENNReal) (hg : Measurable g) (hlaw : μ.map obs = ν.withDensity g)
    (E : ι → Set Ω) (hE : ∀ i, MeasurableSet (E i))
    (h : ι → X → ENNReal) (hh : ∀ i, Measurable (h i))
    (hrestrict : ∀ i, (μ.restrict (E i)).map obs = ν.withDensity (h i))
    (lst : X → Finset ι) (hknown : ∀ i p, p ∈ E i → i ∈ lst (obs p))
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (K : ENNReal)
    (hcard : ∀ x, ((lst x).card : ENNReal) ≤ K)
    (hcap : ∀ᵐ x ∂ν, ∀ i, h i x ≤ ENNReal.ofReal a) :
    (∑ i, μ {p | p ∈ E i ∧ ENNReal.ofReal b ≤ g (obs p)}) ≤
      ENNReal.ofReal (a / b) * K * μ univ := by
  classical
  let S : Set X := {x | ENNReal.ofReal b ≤ g x}
  have hS : MeasurableSet S := measurableSet_le measurable_const hg
  let H : ι → X → ENNReal := fun i => S.indicator (h i)
  have hH (i : ι) : Measurable (H i) := (hh i).indicator hS
  have hsupport :=
    k4_native_calibrated_homogeneous_remainder.observation_list_density_support
      μ obs hobs ν g hg hlaw E hE h hh hrestrict lst hknown
  have hsupport' : ∀ᵐ x ∂ν, ∀ i, H i x ≠ 0 → i ∈ lst x := by
    filter_upwards [hsupport] with x hx
    intro i hi
    apply hx i
    intro hz
    apply hi
    simp only [H, indicator_apply, hz, ite_self]
  have hmul : ENNReal.ofReal a = ENNReal.ofReal (a / b) * ENNReal.ofReal b := by
    rw [← ENNReal.ofReal_mul (div_nonneg ha hb.le)]
    congr 1
    field_simp
  have hbound : ∀ᵐ x ∂ν, ∀ i, H i x ≤ ENNReal.ofReal (a / b) * g x := by
    filter_upwards [hcap] with x hx
    intro i
    by_cases hs : x ∈ S
    · rw [show H i x = h i x from indicator_of_mem hs _]
      exact (hx i).trans (hmul ▸ mul_le_mul' le_rfl hs)
    · simp only [H, indicator_of_notMem hs, zero_le]
  have hmass : (∫⁻ x, g x ∂ν) = μ univ := by
    rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ, ← hlaw,
      Measure.map_apply hobs MeasurableSet.univ, preimage_univ]
  have heq (i : ι) : μ {p | p ∈ E i ∧ ENNReal.ofReal b ≤ g (obs p)} =
      ∫⁻ x, H i x ∂ν := by
    rw [lintegral_indicator hS]
    have hset : {p | p ∈ E i ∧ ENNReal.ofReal b ≤ g (obs p)} = obs ⁻¹' S ∩ E i := by
      ext p
      exact and_comm
    rw [hset, ← Measure.restrict_apply (hS.preimage hobs),
      ← Measure.map_apply hobs hS, hrestrict i, withDensity_apply _ hS]
  simp_rw [heq]
  exact (listed_density_mass_le ν g H hg hH lst (ENNReal.ofReal (a / b)) K
    hcard hsupport' hbound).trans_eq (by rw [hmass])

/-- The joint angular cap charges all labels meeting at most `v` velocity
cells. The original pure density supplies the reference mass, and the only
label loss is the size of its original known list. -/
theorem known_label_velocity_charge
    {Ω X V ι : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    [MeasurableSpace X] [MeasurableEq X] [MeasurableSpace V]
    [Countable V] [MeasurableSingletonClass V] [Fintype ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ν : Measure X) [SigmaFinite ν]
    (obs : Ω → X) (vel : Ω → V) (hobs : Measurable obs) (hvel : Measurable vel)
    (g : X → ENNReal) (hg : Measurable g) (hlaw : μ.map obs = ν.withDensity g)
    (G : X × V → ENNReal) (hG : Measurable G)
    (hjoint : μ.map (fun p => (obs p, vel p)) = (ν.prod Measure.count).withDensity G)
    (F : ι → Set Ω) (hF : ∀ i, MeasurableSet (F i))
    (C : ι → Finset V) (hvelocity : ∀ i p, p ∈ F i → vel p ∈ C i)
    (lst : X → Finset ι) (hknown : ∀ i p, p ∈ F i → i ∈ lst (obs p))
    {a b v : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hv : 0 ≤ v)
    (hcard : ∀ i, ((C i).card : ℝ) ≤ v)
    (K : ENNReal) (hlst : ∀ x, ((lst x).card : ENNReal) ≤ K) :
    (∑ i, μ {p | p ∈ F i ∧ G (obs p, vel p) ≤ ENNReal.ofReal a ∧
      ENNReal.ofReal b ≤ g (obs p)}) ≤
        ENNReal.ofReal (a * v / b) * K * μ univ := by
  classical
  let Good : Set Ω := {p | G (obs p, vel p) ≤ ENNReal.ofReal a}
  have hGood : MeasurableSet Good :=
    measurableSet_le (hG.comp (hobs.prodMk hvel)) measurable_const
  let E : ι → Set Ω := fun i => F i ∩ Good
  have hE (i : ι) : MeasurableSet (E i) := (hF i).inter hGood
  have hjointcap : (μ.restrict Good).map (fun p => (obs p, vel p)) ≤
      ENNReal.ofReal a • ν.prod Measure.count :=
    Submission.Lib.K4ListedExceptions.map_restrict_observation_cap_le
      μ (ν.prod Measure.count) (fun p => (obs p, vel p)) (hobs.prodMk hvel)
      G hG hjoint (ENNReal.ofReal a)
  have hpurecap (i : ι) : (μ.restrict (E i)).map obs ≤ ENNReal.ofReal (a * v) • ν := by
    have hsupport : (μ.restrict (E i)) {p | vel p ∉ C i} = 0 := by
      apply measure_mono_null (t := (E i)ᶜ)
      · intro p hp hpE
        exact hp (hvelocity i p hpE.1)
      · rw [Measure.restrict_apply' (hE i)]
        simp
    have hdom : (μ.restrict (E i)).map (fun p => (obs p, vel p)) ≤
        ENNReal.ofReal a • ν.prod Measure.count :=
      (Measure.map_mono (Measure.restrict_mono inter_subset_right le_rfl)
        (hobs.prodMk hvel)).trans hjointcap
    have hc : ((C i).card : ENNReal) ≤ ENNReal.ofReal v := by
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal (hcard i)
    have hp := finite_velocity_marginal_bound (μ.restrict (E i)) ν obs vel hobs hvel
      (C i) hdom hsupport hc
    simpa only [← ENNReal.ofReal_mul ha] using hp
  let h : ι → X → ENNReal := fun i => ((μ.restrict (E i)).map obs).rnDeriv ν
  have hh (i : ι) : Measurable (h i) := Measure.measurable_rnDeriv _ _
  have hrestrict (i : ι) : (μ.restrict (E i)).map obs = ν.withDensity (h i) := by
    exact (Measure.withDensity_rnDeriv_eq _ ν
      (Measure.absolutelyContinuous_of_le_smul (hpurecap i))).symm
  have hcap : ∀ᵐ x ∂ν, ∀ i, h i x ≤ ENNReal.ofReal (a * v) := by
    apply ae_all_iff.mpr
    intro i
    apply Submission.Lib.K4Homogenization.density_le_of_measure_bound ν (h i) (hh i)
      (ENNReal.ofReal (a * v))
    rw [← hrestrict i]
    exact hpurecap i
  have hc := known_lists_capped_density_mass μ ν obs hobs g hg hlaw E hE h hh hrestrict
    lst (fun i p hp => hknown i p hp.1) (mul_nonneg ha hv) hb K hlst hcap
  simpa only [E, Good, mem_inter_iff, mem_ofPred_eq, and_assoc] using hc

/-- Including the pure and angular exceptional sets gives a bound for the
complete original label mass. Each exception pays only the known-list size. -/
theorem known_label_velocity_mass_le
    {Ω X V ι : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    [MeasurableSpace X] [MeasurableEq X] [MeasurableSpace V]
    [Countable V] [MeasurableSingletonClass V] [Fintype ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ν : Measure X) [SigmaFinite ν]
    (obs : Ω → X) (vel : Ω → V) (hobs : Measurable obs) (hvel : Measurable vel)
    (g : X → ENNReal) (hg : Measurable g) (hlaw : μ.map obs = ν.withDensity g)
    (G : X × V → ENNReal) (hG : Measurable G)
    (hjoint : μ.map (fun p => (obs p, vel p)) = (ν.prod Measure.count).withDensity G)
    (F : ι → Set Ω) (hF : ∀ i, MeasurableSet (F i))
    (C : ι → Finset V) (hvelocity : ∀ i p, p ∈ F i → vel p ∈ C i)
    (lst : X → Finset ι) (hknown : ∀ i p, p ∈ F i → i ∈ lst (obs p))
    {a b v : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hv : 0 ≤ v)
    (hcard : ∀ i, ((C i).card : ℝ) ≤ v)
    (K : ENNReal) (hlst : ∀ x, ((lst x).card : ENNReal) ≤ K) :
    (∑ i, μ (F i)) ≤ ENNReal.ofReal (a * v / b) * K * μ univ +
      K * (μ {p | g (obs p) < ENNReal.ofReal b} +
        μ {p | ENNReal.ofReal a < G (obs p, vel p)}) := by
  classical
  let Bad₁ : Set Ω := {p | g (obs p) < ENNReal.ofReal b}
  let Bad₂ : Set Ω := {p | ENNReal.ofReal a < G (obs p, vel p)}
  have hB₁ : MeasurableSet Bad₁ := measurableSet_lt (hg.comp hobs) measurable_const
  have hB₂ : MeasurableSet Bad₂ := measurableSet_lt measurable_const (hG.comp (hobs.prodMk hvel))
  let Good : ι → Set Ω := fun i => {p | p ∈ F i ∧
    G (obs p, vel p) ≤ ENNReal.ofReal a ∧ ENNReal.ofReal b ≤ g (obs p)}
  have hsum : (∑ i, μ (F i)) ≤
      (∑ i, μ (Good i)) + ((∑ i, μ (F i ∩ Bad₁)) + ∑ i, μ (F i ∩ Bad₂)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hsub : F i ⊆ Good i ∪ ((F i ∩ Bad₁) ∪ (F i ∩ Bad₂)) := by
      intro p hp
      by_cases h₁ : p ∈ Bad₁
      · exact Or.inr (Or.inl ⟨hp, h₁⟩)
      · by_cases h₂ : p ∈ Bad₂
        · exact Or.inr (Or.inr ⟨hp, h₂⟩)
        · exact Or.inl ⟨hp, le_of_not_gt h₂, le_of_not_gt h₁⟩
    exact (measure_mono hsub).trans
      ((measure_union_le _ _).trans (add_le_add_right (measure_union_le _ _) _))
  have hbad (S : Set Ω) (hS : MeasurableSet S) :
      (∑ i, μ (F i ∩ S)) ≤ K * μ S := by
    have hs := k4_remainder_pure_profile_normalization.sum_restrict_apply_le_of_lists
      μ F hF (fun p => lst (obs p)) K hknown (fun p => hlst (obs p)) S hS
    simpa only [Measure.restrict_apply hS, inter_comm] using hs
  have hgood := known_label_velocity_charge μ ν obs vel hobs hvel g hg hlaw G hG hjoint
    F hF C hvelocity lst hknown ha hb hv hcard K hlst
  apply hsum.trans
  exact (add_le_add hgood (add_le_add (hbad Bad₁ hB₁) (hbad Bad₂ hB₂))).trans_eq (by
    dsimp only [Bad₁, Bad₂]
    ring)

end Submission.Obl.k4_finite_positive_mixed_cover_realization
