-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.AngularPreparation, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/AngularPreparation.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/AngularPreparation.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/AngularPreparation.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/AngularPreparation.lean.
   Original comments and attributions are preserved below. -/
import Submission.Lib.K4Homogenization.DensityOperations
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.MeasurableLists

/-! Refinement losses are paid against the observation's local packet list,
independently of the total number of packets in the path. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Submission.Lib.K4Homogenization
open scoped ENNReal BigOperators

/-- A listed refinement costs `ε*D`, where `D` is the number of labels at
each observation, rather than the size of the full label type. -/
theorem listed_refinement_lowDensity_mass {X I : Type*} [MeasurableSpace X] [Fintype I]
    (μ : Measure X) (ε D : ENNReal) (f : X → ENNReal) (g : I → X → ENNReal)
    (hf : Measurable f) (hg : ∀ i, Measurable (g i)) (L : X → Finset I)
    (hcard : ∀ x, ((L x).card : ENNReal) ≤ D)
    (hsupport : ∀ᵐ x ∂μ, ∀ i, i ∉ L x → g i x = 0) :
    (∑ i, ∫⁻ x in lowDensity ε f (g i), g i x ∂μ) ≤ ε * D * ∫⁻ x, f x ∂μ := by
  classical
  let a : I → X → ENNReal := fun i => (lowDensity ε f (g i)).indicator (g i)
  have ha (i : I) : Measurable (a i) :=
    (hg i).indicator (measurableSet_lowDensity ε hf (hg i))
  have hbound : (fun x => ∑ i, a i x) ≤ᵐ[μ] fun x => (ε * D) * f x := by
    filter_upwards [hsupport] with x hx
    have hsum : (∑ i, a i x) = ∑ i ∈ L x, a i x := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      by_cases hbad : x ∈ lowDensity ε f (g i)
      · simp only [a, indicator_of_mem hbad, hx i hi]
      · simp only [a, indicator_of_notMem hbad]
    rw [hsum]
    calc
      _ ≤ ∑ _i ∈ L x, ε * f x := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hbad : x ∈ lowDensity ε f (g i)
        · simpa only [a, indicator_of_mem hbad] using (show g i x < ε * f x from hbad).le
        · simp only [a, indicator_of_notMem hbad, zero_le]
      _ = ((L x).card : ENNReal) * (ε * f x) := by simp
      _ ≤ D * (ε * f x) := mul_le_mul (hcard x) le_rfl zero_le zero_le
      _ = _ := by ring
  calc
    _ = ∑ i, ∫⁻ x, a i x ∂μ := Finset.sum_congr rfl (fun i _ =>
      (lintegral_indicator (measurableSet_lowDensity ε hf (hg i)) (g i)).symm)
    _ = ∫⁻ x, ∑ i, a i x ∂μ := (lintegral_finsetSum Finset.univ (fun i _ => ha i)).symm
    _ ≤ ∫⁻ x, (ε * D) * f x ∂μ := lintegral_mono_ae hbound
    _ = _ := lintegral_const_mul (ε * D) hf

/-- A joint ceiling relative to the SAME pure marginal gives an angular-bin
cap relative to the original total mass, before any normalization. -/
theorem angular_bin_mass_le_of_joint_domination {Ω X I : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I]
    (ν : Measure Ω) (ref : Measure X) (obs : Ω → X) (ang : Ω → I)
    (hobs : Measurable obs) (hang : Measurable ang) (f : X → ENNReal) (c : ENNReal)
    (hpure : ν.map obs = ref.withDensity f)
    (hjoint : ν.map (fun p => (obs p, ang p)) ≤ c • (ref.withDensity f).prod Measure.count)
    (i : I) : ν {p | ang p = i} ≤ c * ν univ := by
  have htotal : ref.withDensity f univ = ν univ := by
    rw [← hpure, Measure.map_apply hobs MeasurableSet.univ]
    simp
  calc
    _ = ν.map (fun p => (obs p, ang p)) (univ ×ˢ {i}) := by
      rw [Measure.map_apply (hobs.prodMk hang) (MeasurableSet.univ.prod (measurableSet_singleton i))]
      congr 1
      ext p
      simp
    _ ≤ (c • (ref.withDensity f).prod Measure.count) (univ ×ˢ {i}) := hjoint _
    _ = _ := by simp [Measure.smul_apply, Measure.prod_prod, htotal]

theorem angular_bin_mass_le_of_joint_density {Ω X I : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I]
    (ν : Measure Ω) (ref : Measure X) (obs : Ω → X) (ang : Ω → I)
    (hobs : Measurable obs) (hang : Measurable ang)
    (f : X → ENNReal) (hf : Measurable f) (G : X × I → ENNReal) (c : ENNReal)
    (hpure : ν.map obs = ref.withDensity f)
    (hjoint : ν.map (fun p => (obs p, ang p)) = (ref.prod Measure.count).withDensity G)
    (hceil : G ≤ᵐ[ref.prod Measure.count] fun p => c * f p.1) (i : I) :
    ν {p | ang p = i} ≤ c * ν univ := by
  apply angular_bin_mass_le_of_joint_domination ν ref obs ang hobs hang f c hpure _ i
  have hscale : (ref.prod (Measure.count : Measure I)).withDensity (fun p => c * f p.1) =
      c • (ref.prod Measure.count).withDensity (fun p => f p.1) := by
    simpa only [Pi.smul_def, smul_eq_mul] using
      withDensity_smul (μ := ref.prod (Measure.count : Measure I))
        (f := fun p : X × I => f p.1) c (hf.comp measurable_fst)
  rw [hjoint, prod_withDensity_left hf]
  exact (withDensity_mono hceil).trans_eq hscale

/-- An original event predicted by a measurable observation set has zero
observation density outside that set. No density representative is chosen anew. -/
theorem density_zero_off_prediction {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (ν : Measure Ω) (ref : Measure X) (obs : Ω → X) (hobs : Measurable obs)
    (S : Set Ω) (A : Set X) (hA : MeasurableSet A) (g : X → ENNReal) (hg : Measurable g)
    (hlaw : (ν.restrict S).map obs = ref.withDensity g) (hpred : S ⊆ obs ⁻¹' A) :
    ∀ᵐ x ∂ref, x ∉ A → g x = 0 := by
  have hzero : ref.withDensity g Aᶜ = 0 := by
    rw [← hlaw, Measure.map_apply hobs hA.compl,
      Measure.restrict_apply (hA.compl.preimage hobs)]
    exact measure_mono_null (fun x hx => False.elim (hx.1 (hpred hx.2)))
      (measure_empty : ν (∅ : Set Ω) = 0)
  have hn := (withDensity_apply_eq_zero hg).mp hzero
  apply ae_iff.mpr
  have hset : {x | ¬ (x ∉ A → g x = 0)} = {x | g x ≠ 0} ∩ Aᶜ := by
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff, mem_compl_iff]
    tauto
  rw [hset]
  exact hn

/-- Every original measurable-event restriction has a measurable observation
density, using Radon--Nikodym under the original reference measure. -/
theorem exists_restricted_observation_density {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (ν : Measure Ω) [IsFiniteMeasure ν] (ref : Measure X) [SigmaFinite ref]
    (obs : Ω → X) (hobs : Measurable obs) (f : X → ENNReal)
    (hpure : ν.map obs = ref.withDensity f) (S : Set Ω) :
    ∃ g : X → ENNReal, Measurable g ∧
      (ν.restrict S).map obs = ref.withDensity g ∧ g ≤ᵐ[ref] f := by
  let ξ := (ν.restrict S).map obs
  have hle : ξ ≤ ν.map obs := Measure.map_mono Measure.restrict_le_self hobs
  have hac : ξ ≪ ref := hle.absolutelyContinuous.trans (by
    rw [hpure]
    exact withDensity_absolutelyContinuous _ _)
  let g := ξ.rnDeriv ref
  have hg : Measurable g := Measure.measurable_rnDeriv _ _
  have hlaw : (ν.restrict S).map obs = ref.withDensity g :=
    (Measure.withDensity_rnDeriv_eq ξ ref hac).symm
  exact ⟨g, hg, hlaw, observation_restriction_density_le ν ref S obs hobs hg hpure hlaw⟩

/-- A ceiling checked at the actual retained incidences gives a globally
valid version of the restricted joint density. -/
theorem exists_restricted_joint_density_ceiling {Ω X I : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I]
    (ν : Measure Ω) [IsFiniteMeasure ν] (ref : Measure X) [SigmaFinite ref]
    (obs : Ω → X) (ang : Ω → I) (hobs : Measurable obs) (hang : Measurable ang)
    (f : X → ENNReal) (hf : Measurable f) (G : X × I → ENNReal) (hG : Measurable G)
    (c : ENNReal) (hjoint : ν.map (fun p => (obs p, ang p)) = (ref.prod Measure.count).withDensity G)
    (S : Set Ω) (hstate : ∀ p ∈ S, G (obs p, ang p) ≤ c * f (obs p)) :
    ∃ J : X × I → ENNReal, Measurable J ∧
      (ν.restrict S).map (fun p => (obs p, ang p)) = (ref.prod Measure.count).withDensity J ∧
      J ≤ᵐ[ref.prod Measure.count] fun p => c * f p.1 := by
  let o : Ω → X × I := fun p => (obs p, ang p)
  have ho : Measurable o := hobs.prodMk hang
  obtain ⟨J, hJ, hlaw, hle⟩ := exists_restricted_observation_density ν
    (ref.prod (Measure.count : Measure I)) o ho G hjoint S
  let A : Set (X × I) := {p | G p ≤ c * f p.1}
  have hA : MeasurableSet A := measurableSet_le hG (measurable_const.mul (hf.comp measurable_fst))
  have hzero := density_zero_off_prediction ν (ref.prod (Measure.count : Measure I))
    o ho S A hA J hJ hlaw hstate
  refine ⟨J, hJ, hlaw, ?_⟩
  filter_upwards [hle, hzero] with p hp hz
  by_cases hpa : p ∈ A
  · exact hp.trans hpa
  · rw [hz hpa]
    exact zero_le

/-- Actual original-law packet omissions pay only for labels on the terminal
observation's old list. The bound does not contain the total packet count. -/
theorem listed_observation_refinement_loss {Ω X I : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Fintype I]
    (ν : Measure Ω) (ref : Measure X) (obs : Ω → X) (hobs : Measurable obs)
    (E : I → Set Ω) (L : X → Finset I) (hL : ∀ i, MeasurableSet {x | i ∈ L x})
    (ε D : ENNReal) (hcard : ∀ x, ((L x).card : ENNReal) ≤ D)
    (f : X → ENNReal) (g : I → X → ENNReal) (hf : Measurable f) (hg : ∀ i, Measurable (g i))
    (hpure : ν.map obs = ref.withDensity f)
    (hlaw : ∀ i, (ν.restrict (E i)).map obs = ref.withDensity (g i))
    (hpred : ∀ i p, p ∈ E i → i ∈ L (obs p)) :
    (∑ i, ν.restrict (E i) {p | g i (obs p) < ε * f (obs p)}) ≤ ε * D * ν univ := by
  have hs : ∀ᵐ x ∂ref, ∀ i, i ∉ L x → g i x = 0 := ae_all_iff.mpr (fun i =>
    density_zero_off_prediction ν ref obs hobs (E i) {x | i ∈ L x} (hL i)
      (g i) (hg i) (hlaw i) (hpred i))
  have htotal : (∫⁻ x, f x ∂ref) = ν univ := by
    calc
      _ = ref.withDensity f univ := by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      _ = ν.map obs univ := congrArg (fun μ : Measure X => μ univ) hpure.symm
      _ = _ := by rw [Measure.map_apply hobs MeasurableSet.univ]; simp
  calc
    _ = ∑ i, ∫⁻ x in lowDensity ε f (g i), g i x ∂ref := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← withDensity_apply (g i) (measurableSet_lowDensity ε hf (hg i)),
        ← hlaw i, Measure.map_apply hobs (measurableSet_lowDensity ε hf (hg i))]
      rfl
    _ ≤ ε * D * ∫⁻ x, f x ∂ref := listed_refinement_lowDensity_mass ref ε D f g hf hg L hcard hs
    _ = _ := by rw [htotal]

/-- Paying a lower bound for the parent's pure density transfers the old
conditional angular ceiling to that parent's retained ORIGINAL law. -/
theorem angular_cap_after_pure_floor {Ω X I : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I]
    (ν : Measure Ω) (ref : Measure X) (obs : Ω → X) (ang : Ω → I)
    (hobs : Measurable obs) (hang : Measurable ang)
    (f g : X → ENNReal) (hg : Measurable g) (G : X × I → ENNReal)
    (c ε : ENNReal) (hε : ε ≠ 0) (hεtop : ε ≠ ∞)
    (hpure : ν.map obs = ref.withDensity g)
    (hjoint : ν.map (fun p => (obs p, ang p)) = (ref.prod Measure.count).withDensity G)
    (hceil : G ≤ᵐ[ref.prod Measure.count] fun p => c * f p.1)
    (A : Set X) (hA : MeasurableSet A) (hfloor : ∀ x ∈ A, ε * f x ≤ g x) (i : I) :
    (ν.restrict (obs ⁻¹' A)) {p | ang p = i} ≤
      (c * ε⁻¹) * (ν.restrict (obs ⁻¹' A)) univ := by
  let ν' := ν.restrict (obs ⁻¹' A)
  have hpure' : ν'.map obs = ref.withDensity (A.indicator g) := by
    dsimp [ν']
    rw [← Measure.restrict_map hobs hA, hpure, restrict_withDensity hA,
      ← withDensity_indicator hA]
  have hpre : (fun p => (obs p, ang p)) ⁻¹' (A ×ˢ (univ : Set I)) = obs ⁻¹' A := by
    ext p
    simp
  have hAI := hA.prod (MeasurableSet.univ : MeasurableSet (univ : Set I))
  have hjoint' : ν'.map (fun p => (obs p, ang p)) =
      (ref.prod Measure.count).withDensity ((A ×ˢ univ).indicator G) := by
    dsimp [ν']
    rw [← hpre, ← Measure.restrict_map (hobs.prodMk hang) hAI, hjoint,
      restrict_withDensity hAI, ← withDensity_indicator hAI]
  have hceil' : ((A ×ˢ univ).indicator G) ≤ᵐ[ref.prod Measure.count]
      fun p => (c * ε⁻¹) * (A.indicator g) p.1 := by
    filter_upwards [hceil] with p hp
    by_cases hpa : p.1 ∈ A
    · have hpAI : p ∈ A ×ˢ (univ : Set I) := ⟨hpa, mem_univ _⟩
      simp only [indicator_of_mem hpAI, indicator_of_mem hpa]
      have hbound : f p.1 ≤ ε⁻¹ * g p.1 := by
        have hm := mul_le_mul (le_refl ε⁻¹) (hfloor p.1 hpa) zero_le zero_le
        rw [← mul_assoc, ENNReal.inv_mul_cancel hε hεtop, one_mul] at hm
        exact hm
      calc
        _ ≤ c * f p.1 := hp
        _ ≤ c * (ε⁻¹ * g p.1) := mul_le_mul le_rfl hbound zero_le zero_le
        _ = _ := by ring
    · have hpAI : p ∉ A ×ˢ (univ : Set I) := fun hp => hpa hp.1
      simp only [indicator_of_notMem hpAI, indicator_of_notMem hpa, mul_zero, le_refl]
  exact angular_bin_mass_le_of_joint_density ν' ref obs ang hobs hang (A.indicator g)
    (hg.indicator hA) _ (c * ε⁻¹) hpure' hjoint' hceil' i

/-- Prepare one original-law parent family for every prescribed angular test
using the SAME pure-observation masks. Cost depends only on the local old list. -/
theorem prepare_listed_angular_family {Ω X P T I : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Fintype P]
    [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    (ν : Measure Ω) [IsFiniteMeasure ν] (ref : Measure X) [SigmaFinite ref]
    (obs : Ω → X) (hobs : Measurable obs) (E : P → Set Ω)
    (L : X → Finset P) (hL : ∀ b, MeasurableSet {x | b ∈ L x})
    (D : ENNReal) (hcard : ∀ x, ((L x).card : ENNReal) ≤ D)
    (f : X → ENNReal) (hf : Measurable f) (hpure : ν.map obs = ref.withDensity f)
    (hpred : ∀ b p, p ∈ E b → b ∈ L (obs p))
    (ang : T → Ω → I) (hang : ∀ t, Measurable (ang t))
    (G : T → X × I → ENNReal) (hG : ∀ t, Measurable (G t)) (c : T → ENNReal)
    (hjoint : ∀ t, ν.map (fun p => (obs p, ang t p)) = (ref.prod Measure.count).withDensity (G t))
    (hstate : ∀ t b p, p ∈ E b → G t (obs p, ang t p) ≤ c t * f (obs p))
    (ε : ENNReal) (hε : ε ≠ 0) (hεtop : ε ≠ ∞) :
    ∃ A : P → Set X, (∀ b, MeasurableSet (A b)) ∧
      (∑ b, ν.restrict (E b) {p | obs p ∉ A b}) ≤ ε * D * ν univ ∧
      ∀ t b i, ((ν.restrict (E b)).restrict (obs ⁻¹' A b)) {p | ang t p = i} ≤
        (c t * ε⁻¹) * ((ν.restrict (E b)).restrict (obs ⁻¹' A b)) univ := by
  classical
  choose g hg hlaw hle using (fun b => exists_restricted_observation_density ν ref obs hobs f hpure (E b))
  let A : P → Set X := fun b => {x | ε * f x ≤ g b x}
  have hA (b : P) : MeasurableSet (A b) := measurableSet_le (measurable_const.mul hf) (hg b)
  refine ⟨A, hA, ?_, ?_⟩
  · have hloss := listed_observation_refinement_loss ν ref obs hobs E L hL ε D hcard
      f g hf hg hpure hlaw hpred
    have heq (b : P) : {p | obs p ∉ A b} = {p | g b (obs p) < ε * f (obs p)} := by
      ext p
      simp only [A, mem_ofPred_eq, not_le]
    simpa only [heq] using hloss
  · intro t b i
    obtain ⟨J, hJ, hJlaw, hJceil⟩ := exists_restricted_joint_density_ceiling ν ref obs (ang t)
      hobs (hang t) f hf (G t) (hG t) (c t) (hjoint t) (E b) (hstate t b)
    exact angular_cap_after_pure_floor (ν.restrict (E b)) ref obs (ang t) hobs (hang t)
      f (g b) (hg b) J (c t) ε hε hεtop (hlaw b) hJlaw hJceil
      (A b) (hA b) (fun x hx => hx) i

/-- Standard Borel incidence families need no measurability assumption on the
supplied prediction lists. Their measurable replacements preserve the cap. -/
theorem prepare_arbitrary_listed_angular_family {Ω X P T I : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X] [Fintype P]
    [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    (ν : Measure Ω) [IsFiniteMeasure ν] (ref : Measure X) [SigmaFinite ref]
    (obs : Ω → X) (hobs : Measurable obs) (E : P → Set Ω) (hE : ∀ b, MeasurableSet (E b))
    (L : X → Finset P) (D : ℝ) (hcard : ∀ x, ((L x).card : ℝ) ≤ D)
    (f : X → ENNReal) (hf : Measurable f) (hpure : ν.map obs = ref.withDensity f)
    (hpred : ∀ b p, p ∈ E b → b ∈ L (obs p))
    (ang : T → Ω → I) (hang : ∀ t, Measurable (ang t))
    (G : T → X × I → ENNReal) (hG : ∀ t, Measurable (G t)) (c : T → ENNReal)
    (hjoint : ∀ t, ν.map (fun p => (obs p, ang t p)) = (ref.prod Measure.count).withDensity (G t))
    (hstate : ∀ t b p, p ∈ E b → G t (obs p, ang t p) ≤ c t * f (obs p))
    (ε : ENNReal) (hε : ε ≠ 0) (hεtop : ε ≠ ∞) :
    ∃ A : P → Set X, (∀ b, MeasurableSet (A b)) ∧
      (∑ b, ν.restrict (E b) {p | obs p ∉ A b}) ≤ ε * ENNReal.ofReal D * ν univ ∧
      ∀ t b i, ((ν.restrict (E b)).restrict (obs ⁻¹' A b)) {p | ang t p = i} ≤
        (c t * ε⁻¹) * ((ν.restrict (E b)).restrict (obs ⁻¹' A b)) univ := by
  obtain ⟨L', hL', hc, hp⟩ := measurable_event_prediction_list obs hobs E hE L D hcard hpred
  have hc' (x : X) : ((L' x).card : ENNReal) ≤ ENNReal.ofReal D := by
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal (hc x)
  exact prepare_listed_angular_family ν ref obs hobs E L' hL' (ENNReal.ofReal D) hc'
    f hf hpure hp ang hang G hG c hjoint hstate ε hε hεtop

/-- All parent masks are imposed once, before fixing the probability law used
by the entropy window. -/
def observationFamilyCut {Ω X P : Type*} (H : Set Ω) (E : P → Set Ω)
    (obs : Ω → X) (A : P → Set X) : Set Ω :=
  H \ ⋃ b, E b ∩ {p | obs p ∉ A b}

theorem measurableSet_observationFamilyCut {Ω X P : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable P]
    {H : Set Ω} {E : P → Set Ω} {obs : Ω → X} {A : P → Set X}
    (hH : MeasurableSet H) (hE : ∀ b, MeasurableSet (E b))
    (hobs : Measurable obs) (hA : ∀ b, MeasurableSet (A b)) :
    MeasurableSet (observationFamilyCut H E obs A) :=
  hH.diff (MeasurableSet.iUnion (fun b => (hE b).inter ((hA b).compl.preimage hobs)))

theorem observationFamilyCut_parent {Ω X P : Type*} {H : Set Ω} {E : P → Set Ω}
    {obs : Ω → X} {A : P → Set X} (b : P) :
    observationFamilyCut H E obs A ∩ E b ⊆ obs ⁻¹' A b := by
  intro p hp
  by_contra hn
  exact hp.1.2 (mem_iUnion.mpr ⟨b, hp.2, hn⟩)

theorem observationFamilyCut_omission_le {Ω X P : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Fintype P]
    (ν : Measure Ω) (H : Set Ω) (E : P → Set Ω) (obs : Ω → X) (A : P → Set X)
    (hobs : Measurable obs) (hA : ∀ b, MeasurableSet (A b)) :
    ν (H \ observationFamilyCut H E obs A) ≤
      ∑ b, ν.restrict (E b) {p | obs p ∉ A b} := by
  have hsub : H \ observationFamilyCut H E obs A ⊆ ⋃ b, E b ∩ {p | obs p ∉ A b} := by
    intro p hp
    by_contra hn
    exact hp.2 ⟨hp.1, hn⟩
  calc
    _ ≤ ν (⋃ b, E b ∩ {p | obs p ∉ A b}) := measure_mono hsub
    _ ≤ ∑ b, ν (E b ∩ {p | obs p ∉ A b}) := measure_iUnion_fintype_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      have hb : MeasurableSet {p | obs p ∉ A b} := (hA b).compl.preimage hobs
      rw [Measure.restrict_apply hb, inter_comm]

/-- The law after the global cut is dominated by the already fixed parent
reference. Future masks never change the reference appearing on the right. -/
theorem observationFamilyCut_parent_domination {Ω X P : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (ν : Measure Ω) (H : Set Ω) (E : P → Set Ω) (obs : Ω → X) (A : P → Set X)
    (hobs : Measurable obs) (hA : ∀ b, MeasurableSet (A b)) (b : P) :
    ν.restrict (observationFamilyCut H E obs A ∩ E b) ≤
      (ν.restrict (E b)).restrict (obs ⁻¹' A b) := by
  rw [Measure.restrict_restrict ((hA b).preimage hobs)]
  apply Measure.restrict_mono _ le_rfl
  intro p hp
  exact ⟨observationFamilyCut_parent b hp, hp.2⟩

/-- A lower mass ratio to a fixed reference pays for the normalization of a
current posterior. Neither reference is replaced by a retained marginal. -/
theorem conditional_cap_of_reference_floor {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) (hdom : μ ≤ ν) {θ c : ENNReal}
    (hθ : θ ≠ 0) (hθtop : θ ≠ ∞)
    (hμ : μ univ ≠ 0) (hμtop : μ univ ≠ ∞)
    (hfloor : θ * ν univ ≤ μ univ) (B : Set Ω) (hcap : ν B ≤ c * ν univ) :
    ProbabilityTheory.cond μ univ B ≤ c * θ⁻¹ := by
  have href : ν univ ≤ θ⁻¹ * μ univ := by
    have hh := mul_le_mul (le_refl θ⁻¹) hfloor zero_le zero_le
    rw [← mul_assoc, ENNReal.inv_mul_cancel hθ hθtop, one_mul] at hh
    exact hh
  have hm : μ B ≤ (c * θ⁻¹) * μ univ := by
    calc
      _ ≤ ν B := hdom B
      _ ≤ c * ν univ := hcap
      _ ≤ c * (θ⁻¹ * μ univ) := mul_le_mul le_rfl href zero_le zero_le
      _ = _ := by ring
  simp only [ProbabilityTheory.cond, Measure.restrict_univ, Measure.smul_apply, smul_eq_mul]
  calc
    _ ≤ (μ univ)⁻¹ * ((c * θ⁻¹) * μ univ) := mul_le_mul le_rfl hm zero_le zero_le
    _ = (c * θ⁻¹) * ((μ univ)⁻¹ * μ univ) := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel hμ hμtop, mul_one]

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
