-- Adapted from: here:o049
-- Original label-floor and support-transfer kernels by x0149; whole-cell certificates
-- joint refined-cell aggregation, and original-source law adapters by x0147, for o049 `k4_cap_class_terminal_charts`.
import Mathlib

/-!
# Refined-label floors, support transfer, and original-source certificates

Measure-theoretic kernels of the group-refinement step in the initial horizon bound
(paper Proposition 2.16, with the restriction estimate of Lemma 2.3):

* `refined_label_floor`: original label subdensities `g i` (unnormalized), approximations
  `h i`, and at each point a list of at most `R` labels carrying all the density. Where the
  total density is at least `ρ`, the labels whose approximate density is below `ε ρ / (2R)`
  carry at most `ε` times the total mass plus twice the joint `L¹` approximation error. The
  bound depends on the list size `R`, not on the number of labels.
* `support_transfer`: if each label's observation law is `λ.withDensity (ofReal ∘ g i)` and the
  label of almost every source point lies in the decoded list of its observation, then
  `λ`-a.e. every label with positive density lies in the list.

Adapted from: here:o049 (the same code, written by session x0149 for obligation o049).
-/

namespace Submission.Lib.K4RefinedLabelFloors

open MeasureTheory



/-- Pointwise form of the refined-label floor: on a fibre where only labels of a list of size
at most `R` carry density, the labels whose approximate density is below `ε ρ / (2R)` carry at
most `ε F + 2 ∑ |g - h|` once the total density `F` is at least `ρ`. -/
lemma refined_label_floor_pointwise {I : Type*} [Fintype I] (g h : I → ℝ) (hg0 : ∀ i, 0 ≤ g i)
    (Lx : Finset I) {R : ℝ} (hR : 0 < R) (hL : (Lx.card : ℝ) ≤ R)
    (hsupp : ∀ i, 0 < g i → i ∈ Lx) {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) :
    ∑ i, (if ρ ≤ ∑ j, g j ∧ h i < ε * ρ / (2 * R) then g i else 0) ≤
      ε * ∑ j, g j + 2 * ∑ i, |g i - h i| := by
  classical
  by_cases hF : ρ ≤ ∑ j, g j
  · -- split according to whether `g i` is below `ε ρ / R`
    have hsplit : ∀ i, (if ρ ≤ ∑ j, g j ∧ h i < ε * ρ / (2 * R) then g i else 0) ≤
        (if i ∈ Lx then min (g i) (ε * ρ / R) else 0) + 2 * |g i - h i| := by
      intro i
      by_cases hc : h i < ε * ρ / (2 * R)
      · rw [if_pos ⟨hF, hc⟩]
        by_cases hsmall : g i < ε * ρ / R
        · by_cases hpos : 0 < g i
          · rw [if_pos (hsupp i hpos), min_eq_left hsmall.le]
            have := abs_nonneg (g i - h i); linarith
          · have : g i = 0 := le_antisymm (not_lt.mp hpos) (hg0 i)
            rw [this]
            have h1 : (0 : ℝ) ≤ (if i ∈ Lx then min 0 (ε * ρ / R) else 0) := by
              split_ifs
              · exact le_min le_rfl (by positivity)
              · exact le_rfl
            have := abs_nonneg (0 - h i); linarith
        · -- `g i ≥ ε ρ / R` and `h i < ε ρ / (2R)`, so `g i ≤ 2 |g i - h i|`
          push Not at hsmall
          have h1 : g i ≤ 2 * (g i - h i) := by
            have : ε * ρ / (2 * R) = (ε * ρ / R) / 2 := by field_simp
            rw [this] at hc
            linarith
          have h2 : g i - h i ≤ |g i - h i| := le_abs_self _
          have h3 : (0 : ℝ) ≤ (if i ∈ Lx then min (g i) (ε * ρ / R) else 0) := by
            split_ifs
            · exact le_min (hg0 i) (by positivity)
            · exact le_rfl
          linarith
      · rw [if_neg (fun h' => hc h'.2)]
        have h3 : (0 : ℝ) ≤ (if i ∈ Lx then min (g i) (ε * ρ / R) else 0) := by
          split_ifs
          · exact le_min (hg0 i) (by positivity)
          · exact le_rfl
        have := abs_nonneg (g i - h i); linarith
    have hfirst : ∑ i, (if i ∈ Lx then min (g i) (ε * ρ / R) else 0) ≤ ε * ∑ j, g j := by
      rw [← Finset.sum_filter]
      calc ∑ i ∈ Finset.univ.filter (fun i => i ∈ Lx), min (g i) (ε * ρ / R)
          ≤ ∑ _i ∈ Finset.univ.filter (fun i => i ∈ Lx), ε * ρ / R :=
            Finset.sum_le_sum fun i _ => min_le_right _ _
        _ = ((Finset.univ.filter (fun i => i ∈ Lx)).card : ℝ) * (ε * ρ / R) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ R * (ε * ρ / R) := by
            gcongr
            calc ((Finset.univ.filter (fun i => i ∈ Lx)).card : ℝ) ≤ (Lx.card : ℝ) := by
                  exact_mod_cast Finset.card_le_card (fun i hi => (Finset.mem_filter.mp hi).2)
              _ ≤ R := hL
        _ = ε * ρ := by field_simp
        _ ≤ ε * ∑ j, g j := mul_le_mul_of_nonneg_left hF hε.le
    calc ∑ i, (if ρ ≤ ∑ j, g j ∧ h i < ε * ρ / (2 * R) then g i else 0)
        ≤ ∑ i, ((if i ∈ Lx then min (g i) (ε * ρ / R) else 0) + 2 * |g i - h i|) :=
          Finset.sum_le_sum fun i _ => hsplit i
      _ = ∑ i, (if i ∈ Lx then min (g i) (ε * ρ / R) else 0) + 2 * ∑ i, |g i - h i| := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ ε * ∑ j, g j + 2 * ∑ i, |g i - h i| := by linarith
  · have h0 : ∑ i, (if ρ ≤ ∑ j, g j ∧ h i < ε * ρ / (2 * R) then g i else 0) = 0 :=
      Finset.sum_eq_zero fun i _ => if_neg (fun h' => hF h'.1)
    rw [h0]
    have h1 : 0 ≤ ε * ∑ j, g j := mul_nonneg hε.le (Finset.sum_nonneg fun j _ => hg0 j)
    have h2 : 0 ≤ ∑ i, |g i - h i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith

/-- **Refined-label lower floor** (the group refinement step of the initial horizon bound,
paper Proposition 2.16, with the restriction estimate of Lemma 2.3): original label
subdensities `g i` (no normalization), approximations `h i`, and a list `L x` of at most `R`
labels carrying all density at `x`. The labels whose approximate density is below
`ε ρ / (2R)` where the total density is at least `ρ` carry at most `ε` times the total mass
plus twice the joint `L¹` approximation error. -/
theorem refined_label_floor {X I : Type*} [MeasurableSpace X] [Fintype I] (μ : Measure X)
    (g h : I → X → ℝ) (hg : ∀ i, Measurable (g i)) (hh : ∀ i, Measurable (h i))
    (hg0 : ∀ i x, 0 ≤ g i x) (L : X → Finset I) {R : ℝ} (hR : 0 < R)
    (hL : ∀ x, ((L x).card : ℝ) ≤ R) (hsupp : ∀ᵐ x ∂μ, ∀ i, 0 < g i x → i ∈ L x)
    {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) :
    ∑ i, (μ.withDensity (fun x => ENNReal.ofReal (g i x)))
        {x | ρ ≤ ∑ j, g j x ∧ h i x < ε * ρ / (2 * R)} ≤
      ENNReal.ofReal ε * ∫⁻ x, ENNReal.ofReal (∑ j, g j x) ∂μ +
        2 * ∑ i, ∫⁻ x, ENNReal.ofReal |g i x - h i x| ∂μ := by
  classical
  have hF : Measurable (fun x => ∑ j, g j x) := Finset.measurable_sum _ fun j _ => hg j
  have hmeas : ∀ i, MeasurableSet {x | ρ ≤ ∑ j, g j x ∧ h i x < ε * ρ / (2 * R)} := fun i =>
    (measurableSet_le measurable_const hF).inter (measurableSet_lt (hh i) measurable_const)
  -- rewrite each term as a lintegral of an indicator
  have hterm : ∀ i, (μ.withDensity (fun x => ENNReal.ofReal (g i x)))
      {x | ρ ≤ ∑ j, g j x ∧ h i x < ε * ρ / (2 * R)} =
      ∫⁻ x, ENNReal.ofReal (if ρ ≤ ∑ j, g j x ∧ h i x < ε * ρ / (2 * R) then g i x else 0) ∂μ := by
    intro i
    rw [withDensity_apply _ (hmeas i), ← lintegral_indicator (hmeas i)]
    congr 1
    funext x
    by_cases hx : ρ ≤ ∑ j, g j x ∧ h i x < ε * ρ / (2 * R)
    · rw [Set.indicator_of_mem (by exact hx), if_pos hx]
    · rw [Set.indicator_of_notMem (by exact hx), if_neg hx, ENNReal.ofReal_zero]
  simp_rw [hterm]
  have hmeasi : ∀ i, Measurable (fun x =>
      ENNReal.ofReal (if ρ ≤ ∑ j, g j x ∧ h i x < ε * ρ / (2 * R) then g i x else 0)) := by
    intro i
    apply ENNReal.measurable_ofReal.comp
    exact Measurable.ite (hmeas i) (hg i) measurable_const
  rw [← lintegral_finsetSum _ (fun i _ => hmeasi i)]
  have hmeasd : ∀ i, Measurable (fun x => ENNReal.ofReal |g i x - h i x|) := fun i =>
    ENNReal.measurable_ofReal.comp ((hg i).sub (hh i)).abs
  have hmF : Measurable (fun x => ENNReal.ofReal (∑ j, g j x)) := ENNReal.measurable_ofReal.comp hF
  have hmD : Measurable (fun x => ∑ i, ENNReal.ofReal |g i x - h i x|) :=
    Finset.measurable_sum _ fun i _ => hmeasd i
  calc ∫⁻ x, ∑ i, ENNReal.ofReal
        (if ρ ≤ ∑ j, g j x ∧ h i x < ε * ρ / (2 * R) then g i x else 0) ∂μ
      ≤ ∫⁻ x, (ENNReal.ofReal ε * ENNReal.ofReal (∑ j, g j x) +
          2 * ∑ i, ENNReal.ofReal |g i x - h i x|) ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [hsupp] with x hx
        have hpt := refined_label_floor_pointwise (fun i => g i x) (fun i => h i x)
          (fun i => hg0 i x) (L x) hR (hL x) hx hε hρ
        have hnn : ∀ i, 0 ≤ (if ρ ≤ ∑ j, g j x ∧ h i x < ε * ρ / (2 * R) then g i x else 0) := by
          intro i; split_ifs
          · exact hg0 i x
          · exact le_rfl
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hnn i),
          ← ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _),
          ← ENNReal.ofReal_mul hε.le,
          show (2 : ENNReal) = ENNReal.ofReal 2 by simp,
          ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_add (mul_nonneg hε.le (Finset.sum_nonneg fun j _ => hg0 j x))
            (mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => abs_nonneg _))]
        exact ENNReal.ofReal_le_ofReal hpt
    _ = ENNReal.ofReal ε * ∫⁻ x, ENNReal.ofReal (∑ j, g j x) ∂μ +
          2 * ∑ i, ∫⁻ x, ENNReal.ofReal |g i x - h i x| ∂μ := by
        rw [lintegral_add_left (hmF.const_mul _), lintegral_const_mul _ hmF,
          lintegral_const_mul _ hmD, lintegral_finsetSum _ (fun i _ => hmeasd i)]




/-- **Support transfer**: if the observation law of each label `i` is
`λ.withDensity (ofReal ∘ g i)` and the label of `μ`-almost every source point lies in the list
`L` of its observation, then `λ`-almost everywhere every label with positive density lies in
the list. Only the zero mass of each label outside its list is used. -/
theorem support_transfer {Z X I : Type*} [MeasurableSpace Z] [MeasurableSpace X] [Finite I]
    (μ : Measure Z) (lam : Measure X) (obs : Z → X) (hobs : Measurable obs) (code : Z → I)
    (_hcode : ∀ i, MeasurableSet {z | code z = i}) (L : X → Finset I)
    (hL : ∀ i, MeasurableSet {x | i ∈ L x}) (g : I → X → ℝ) (hg : ∀ i, Measurable (g i))
    (hlaw : ∀ i, (μ.restrict {z | code z = i}).map obs =
      lam.withDensity (fun x => ENNReal.ofReal (g i x)))
    (hsrc : ∀ᵐ z ∂μ, code z ∈ L (obs z)) :
    ∀ᵐ x ∂lam, ∀ i, 0 < g i x → i ∈ L x := by
  rw [ae_all_iff]
  intro i
  have hB : MeasurableSet {x | i ∉ L x} := (hL i).compl
  -- the label `i` has no mass outside its list
  have hzero : (lam.withDensity (fun x => ENNReal.ofReal (g i x))) {x | i ∉ L x} = 0 := by
    rw [← hlaw i, Measure.map_apply hobs hB, Measure.restrict_apply (hobs hB)]
    apply measure_mono_null _ (ae_iff.mp hsrc)
    intro z hz
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq] at hz ⊢
    rw [hz.2]
    exact hz.1
  rw [withDensity_apply _ hB] at hzero
  have hae : ∀ᵐ x ∂(lam.restrict {x | i ∉ L x}), ENNReal.ofReal (g i x) = 0 :=
    (lintegral_eq_zero_iff (ENNReal.measurable_ofReal.comp (hg i))).mp hzero
  rw [ae_restrict_iff' hB] at hae
  filter_upwards [hae] with x hx hpos
  by_contra hnot
  have := ENNReal.ofReal_eq_zero.mp (hx hnot)
  linarith


/- Original whole-cell certification proofs added by session x0147 for o049.
Adapted from: here:o049 -/

open Set


open Set MeasureTheory
open scoped ENNReal BigOperators

/-- A measurable-set mass discrepancy is bounded by the original joint L1
error, before any probability normalization. -/
theorem approximating_density_mass_le {X : Type*} [MeasurableSpace X]
    (lam : Measure X) (g h : X → ℝ) (hg : Measurable g)
    (hg0 : ∀ x, 0 ≤ g x) (S : Set X) (hS : MeasurableSet S) :
    (lam.withDensity (fun x => ENNReal.ofReal (h x))) S ≤
      (lam.withDensity (fun x => ENNReal.ofReal (g x))) S +
        ∫⁻ x, ENNReal.ofReal |g x - h x| ∂lam := by
  rw [withDensity_apply _ hS, withDensity_apply _ hS]
  calc
    (∫⁻ x in S, ENNReal.ofReal (h x) ∂lam) ≤
        ∫⁻ x in S, ENNReal.ofReal (g x) + ENNReal.ofReal |g x - h x| ∂lam := by
      apply lintegral_mono
      intro x
      change ENNReal.ofReal (h x) ≤ ENNReal.ofReal (g x) + ENNReal.ofReal |g x - h x|
      rw [← ENNReal.ofReal_add (hg0 x) (abs_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (by linarith [neg_abs_le (g x - h x)])
    _ = (∫⁻ x in S, ENNReal.ofReal (g x) ∂lam) +
        ∫⁻ x in S, ENNReal.ofReal |g x - h x| ∂lam :=
      lintegral_add_left (μ := lam.restrict S) (ENNReal.measurable_ofReal.comp hg) _
    _ ≤ (∫⁻ x in S, ENNReal.ofReal (g x) ∂lam) +
        ∫⁻ x, ENNReal.ofReal |g x - h x| ∂lam := by
      have he : (∫⁻ x in S, ENNReal.ofReal |g x - h x| ∂lam) ≤
          ∫⁻ x, ENNReal.ofReal |g x - h x| ∂lam :=
        lintegral_mono' Measure.restrict_le_self le_rfl
      exact add_le_add le_rfl he

/-- If the approximating law has at least twice the old mass on a set, that
old mass can be discarded at the cost of one joint L1 error. -/
theorem original_mass_le_error_of_double {X : Type*} [MeasurableSpace X]
    (lam : Measure X) (g h : X → ℝ) (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    (S : Set X) (hS : MeasurableSet S)
    (hfinite : (lam.withDensity (fun x => ENNReal.ofReal (g x))) S ≠ ⊤)
    (hdouble : 2 * (lam.withDensity (fun x => ENNReal.ofReal (g x))) S ≤
      (lam.withDensity (fun x => ENNReal.ofReal (h x))) S) :
    (lam.withDensity (fun x => ENNReal.ofReal (g x))) S ≤
      ∫⁻ x, ENNReal.ofReal |g x - h x| ∂lam := by
  have hbound := hdouble.trans (approximating_density_mass_le lam g h hg hg0 S hS)
  rw [two_mul] at hbound
  exact ENNReal.le_of_add_le_add_left hfinite hbound

/-- Finite disjoint original cells with a doubled approximating mass cost only
one global L1 error. No cellwise mass-preservation identity is required. -/
theorem bad_original_cells_mass_le_error {X I : Type*} [MeasurableSpace X]
    (lam : Measure X) (g h : X → ℝ) (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    (F : Finset I) (C : I → Set X) (hC : ∀ i ∈ F, MeasurableSet (C i))
    (hdisj : (↑F : Set I).PairwiseDisjoint C)
    (hfinite : (lam.withDensity (fun x => ENNReal.ofReal (g x))) (⋃ i ∈ F, C i) ≠ ⊤)
    (hdouble : ∀ i ∈ F, 2 * (lam.withDensity (fun x => ENNReal.ofReal (g x))) (C i) ≤
      (lam.withDensity (fun x => ENNReal.ofReal (h x))) (C i)) :
    (lam.withDensity (fun x => ENNReal.ofReal (g x))) (⋃ i ∈ F, C i) ≤
      ∫⁻ x, ENNReal.ofReal |g x - h x| ∂lam := by
  have hS : MeasurableSet (⋃ i ∈ F, C i) := MeasurableSet.biUnion F.countable_toSet hC
  apply original_mass_le_error_of_double lam g h hg hg0 _ hS hfinite
  rw [measure_biUnion_finset hdisj hC, measure_biUnion_finset hdisj hC, Finset.mul_sum]
  exact Finset.sum_le_sum hdouble

/-- A constant cell approximation above `rho` certifies twice the old mass
when that old whole-cell mass is below half the nominal density floor. -/
theorem doubled_cell_mass_of_constant_floor {X : Type*} [MeasurableSpace X]
    (lam : Measure X) (g h : X → ℝ) (C : Set X) (hC : MeasurableSet C)
    {ρ v : ℝ} (hρ : 0 ≤ ρ) (hv : 0 ≤ v)
    (hvolume : lam C = ENNReal.ofReal v)
    (hfloor : ∀ x ∈ C, ρ ≤ h x)
    (hold : (lam.withDensity (fun x => ENNReal.ofReal (g x))) C ≤
      ENNReal.ofReal (ρ * v / 2)) :
    2 * (lam.withDensity (fun x => ENNReal.ofReal (g x))) C ≤
      (lam.withDensity (fun x => ENNReal.ofReal (h x))) C := by
  calc
    _ ≤ 2 * ENNReal.ofReal (ρ * v / 2) := mul_le_mul' le_rfl hold
    _ = ENNReal.ofReal ρ * lam C := by
      rw [hvolume, ← ENNReal.ofReal_mul hρ]
      calc
        2 * ENNReal.ofReal (ρ * v / 2) = ENNReal.ofReal (2 * (ρ * v / 2)) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
        _ = ENNReal.ofReal (ρ * v) := by congr 1; ring
    _ ≤ _ := by
      rw [withDensity_apply _ hC, ← setLIntegral_const]
      apply setLIntegral_mono' hC
      intro x hx
      exact ENNReal.ofReal_le_ofReal (hfloor x hx)

/-- A finite cellwise-constant approximation produces certificates in the old
law. Discarding cells without their old floor loses at most the L1 error. -/
theorem exists_original_cell_certificates {X I : Type*} [MeasurableSpace X]
    (lam : Measure X) (g h : X → ℝ) (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    [IsFiniteMeasure (lam.withDensity (fun x => ENNReal.ofReal (g x)))]
    (F : Finset I) (C : I → Set X) (hC : ∀ i ∈ F, MeasurableSet (C i))
    (hdisj : (↑F : Set I).PairwiseDisjoint C) (a : I → ℝ)
    (hconstant : ∀ i ∈ F, ∀ x ∈ C i, h x = a i)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (v : I → ℝ) (hv : ∀ i ∈ F, 0 ≤ v i)
    (hvolume : ∀ i ∈ F, lam (C i) = ENNReal.ofReal (v i)) :
    ∃ G : Finset I, G ⊆ F ∧
      (∀ i ∈ G, ENNReal.ofReal (ρ * v i / 2) ≤
        (lam.withDensity (fun x => ENNReal.ofReal (g x))) (C i)) ∧
      (lam.withDensity (fun x => ENNReal.ofReal (g x)))
        {x | x ∈ ⋃ i ∈ F, C i ∧ ρ ≤ h x ∧ x ∉ ⋃ i ∈ G, C i} ≤
        ∫⁻ x, ENNReal.ofReal |g x - h x| ∂lam := by
  classical
  let old := lam.withDensity (fun x => ENNReal.ofReal (g x))
  let G := F.filter (fun i => ENNReal.ofReal (ρ * v i / 2) ≤ old (C i))
  let Bad := F.filter (fun i => ρ ≤ a i ∧ old (C i) < ENNReal.ofReal (ρ * v i / 2))
  refine ⟨G, Finset.filter_subset _ _, fun i hi => (Finset.mem_filter.mp hi).2, ?_⟩
  have hBad : ∀ i ∈ Bad, MeasurableSet (C i) :=
    fun i hi => hC i (Finset.mem_filter.mp hi).1
  have hBadDisj : (↑Bad : Set I).PairwiseDisjoint C := by
    intro i hi j hj hij
    exact hdisj (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1 hij
  have hdouble : ∀ i ∈ Bad, 2 * old (C i) ≤
      (lam.withDensity (fun x => ENNReal.ofReal (h x))) (C i) := by
    intro i hi
    have hiF := (Finset.mem_filter.mp hi).1
    have hiBad := (Finset.mem_filter.mp hi).2
    exact doubled_cell_mass_of_constant_floor lam g h (C i) (hC i hiF) hρ
      (hv i hiF) (hvolume i hiF)
      (fun x hx => (hconstant i hiF x hx).symm ▸ hiBad.1) hiBad.2.le
  apply (measure_mono (t := ⋃ i ∈ Bad, C i) ?_).trans
    (bad_original_cells_mass_le_error lam g h hg hg0 Bad C hBad hBadDisj
      (measure_ne_top old _) hdouble)
  intro x hx
  obtain ⟨i, hiF, hxi⟩ := Set.mem_iUnion₂.mp hx.1
  have hiG : i ∉ G := by
    intro hi
    exact hx.2.2 (Set.mem_iUnion₂.mpr ⟨i, hi, hxi⟩)
  have hsmall : old (C i) < ENNReal.ofReal (ρ * v i / 2) := by
    by_contra hn
    exact hiG (Finset.mem_filter.mpr ⟨hiF, le_of_not_gt hn⟩)
  have ha : ρ ≤ a i := (hconstant i hiF x hxi) ▸ hx.2.1
  exact Set.mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr ⟨hiF, ha, hsmall⟩, hxi⟩




open Set MeasureTheory
open scoped ENNReal BigOperators

/-- Joint flattening and a small compatible label list give original whole-cell
certificates. The additional cell certification costs only one more joint L1 error. -/
theorem refined_original_cell_floors {X I J : Type*} [MeasurableSpace X] [Fintype I]
    (lam : Measure X) (g h : I → X → ℝ) (hg : ∀ i, Measurable (g i))
    (hh : ∀ i, Measurable (h i)) (hg0 : ∀ i x, 0 ≤ g i x)
    (hfinite : ∀ i, IsFiniteMeasure (lam.withDensity (fun x => ENNReal.ofReal (g i x))))
    (L : X → Finset I) {R : ℝ} (hR : 0 < R) (hL : ∀ x, ((L x).card : ℝ) ≤ R)
    (hsupp : ∀ᵐ x ∂lam, ∀ i, 0 < g i x → i ∈ L x)
    (F : I → Finset J) (C : I → J → Set X)
    (hC : ∀ i j, j ∈ F i → MeasurableSet (C i j))
    (hdisj : ∀ i, (↑(F i) : Set J).PairwiseDisjoint (C i))
    (a v : I → J → ℝ) (hv : ∀ i j, j ∈ F i → 0 ≤ v i j)
    (hvolume : ∀ i j, j ∈ F i → lam (C i j) = ENNReal.ofReal (v i j))
    (hconstant : ∀ i j, j ∈ F i → ∀ x ∈ C i j, h i x = a i j)
    (hcover : ∀ i, (lam.withDensity (fun x => ENNReal.ofReal (g i x)))
      (⋃ j ∈ F i, C i j)ᶜ = 0)
    {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) :
    ∃ Good : I → Finset J,
      (∀ i, Good i ⊆ F i) ∧
      (∀ i j, j ∈ Good i → ENNReal.ofReal (ε * ρ * v i j / (4 * R)) ≤
        (lam.withDensity (fun x => ENNReal.ofReal (g i x))) (C i j)) ∧
      (∑ i, (lam.withDensity (fun x => ENNReal.ofReal (g i x)))
        {x | ρ ≤ ∑ j, g j x ∧ x ∉ ⋃ j ∈ Good i, C i j}) ≤
        ENNReal.ofReal ε * ∫⁻ x, ENNReal.ofReal (∑ j, g j x) ∂lam +
          3 * ∑ i, ∫⁻ x, ENNReal.ofReal |g i x - h i x| ∂lam := by
  classical
  let τ := ε * ρ / (2 * R)
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hcert (i : I) : ∃ G : Finset J, G ⊆ F i ∧
      (∀ j ∈ G, ENNReal.ofReal (τ * v i j / 2) ≤
        (lam.withDensity (fun x => ENNReal.ofReal (g i x))) (C i j)) ∧
      (lam.withDensity (fun x => ENNReal.ofReal (g i x)))
        {x | x ∈ ⋃ j ∈ F i, C i j ∧ τ ≤ h i x ∧ x ∉ ⋃ j ∈ G, C i j} ≤
        ∫⁻ x, ENNReal.ofReal |g i x - h i x| ∂lam := by
    letI := hfinite i
    exact exists_original_cell_certificates lam (g i) (h i) (hg i) (hg0 i)
      (F i) (C i) (hC i) (hdisj i) (a i) (hconstant i) hτ.le (v i) (hv i) (hvolume i)
  choose Good hGoodF hGoodFloor hGoodError using hcert
  refine ⟨Good, hGoodF, ?_, ?_⟩
  · intro i j hj
    convert hGoodFloor i j hj using 1
    congr 1
    dsimp [τ]
    field_simp
    ring
  have hone (i : I) :
      (lam.withDensity (fun x => ENNReal.ofReal (g i x)))
        {x | ρ ≤ ∑ j, g j x ∧ x ∉ ⋃ j ∈ Good i, C i j} ≤
      (lam.withDensity (fun x => ENNReal.ofReal (g i x)))
        {x | ρ ≤ ∑ j, g j x ∧ h i x < τ} +
      ∫⁻ x, ENNReal.ofReal |g i x - h i x| ∂lam := by
    let old := lam.withDensity (fun x => ENNReal.ofReal (g i x))
    have hsub : {x | ρ ≤ ∑ j, g j x ∧ x ∉ ⋃ j ∈ Good i, C i j} ⊆
        ({x | ρ ≤ ∑ j, g j x ∧ h i x < τ} ∪
          {x | x ∈ ⋃ j ∈ F i, C i j ∧ τ ≤ h i x ∧ x ∉ ⋃ j ∈ Good i, C i j}) ∪
          (⋃ j ∈ F i, C i j)ᶜ := by
      intro x hx
      by_cases hc : x ∈ ⋃ j ∈ F i, C i j
      · apply Or.inl
        by_cases hhτ : h i x < τ
        · exact Or.inl ⟨hx.1, hhτ⟩
        · exact Or.inr ⟨hc, le_of_not_gt hhτ, hx.2⟩
      · exact Or.inr hc
    calc
      _ ≤ old (({x | ρ ≤ ∑ j, g j x ∧ h i x < τ} ∪
          {x | x ∈ ⋃ j ∈ F i, C i j ∧ τ ≤ h i x ∧ x ∉ ⋃ j ∈ Good i, C i j}) ∪
          (⋃ j ∈ F i, C i j)ᶜ) := measure_mono hsub
      _ ≤ (old {x | ρ ≤ ∑ j, g j x ∧ h i x < τ} +
          old {x | x ∈ ⋃ j ∈ F i, C i j ∧ τ ≤ h i x ∧ x ∉ ⋃ j ∈ Good i, C i j}) +
          old (⋃ j ∈ F i, C i j)ᶜ :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ ≤ _ := by
        rw [show old (⋃ j ∈ F i, C i j)ᶜ = 0 from hcover i, add_zero]
        exact add_le_add le_rfl (hGoodError i)
  calc
    _ ≤ ∑ i, ((lam.withDensity (fun x => ENNReal.ofReal (g i x)))
        {x | ρ ≤ ∑ j, g j x ∧ h i x < τ} +
        ∫⁻ x, ENNReal.ofReal |g i x - h i x| ∂lam) := Finset.sum_le_sum (fun i _ => hone i)
    _ = (∑ i, (lam.withDensity (fun x => ENNReal.ofReal (g i x)))
        {x | ρ ≤ ∑ j, g j x ∧ h i x < τ}) +
        ∑ i, ∫⁻ x, ENNReal.ofReal |g i x - h i x| ∂lam := Finset.sum_add_distrib
    _ ≤ (ENNReal.ofReal ε * ∫⁻ x, ENNReal.ofReal (∑ j, g j x) ∂lam +
        2 * ∑ i, ∫⁻ x, ENNReal.ofReal |g i x - h i x| ∂lam) +
        ∑ i, ∫⁻ x, ENNReal.ofReal |g i x - h i x| ∂lam :=
      add_le_add (refined_label_floor lam g h hg hh hg0 L hR hL hsupp hε hρ) le_rfl
    _ = _ := by ring

/- Original source-law adapter by x0147, adapted from here:o049, commit b915088,
   Submission/Obl/k4_cap_class_terminal_charts/LabelLawFloors.lean. -/
open Set MeasureTheory
open scoped ENNReal BigOperators

/-- A label-dependent observed event has exactly its original source mass.
No conditional probability or posterior weight is introduced. -/
theorem finite_label_source_formula {Z X I : Type*}
    [MeasurableSpace Z] [MeasurableSpace X] [Fintype I]
    (μ : Measure Z) (lam : Measure X) (obs : Z → X) (hobs : Measurable obs)
    (code : Z → I) (hcode : ∀ i, MeasurableSet {z | code z = i})
    (g : I → X → ℝ)
    (hlaw : ∀ i, (μ.restrict {z | code z = i}).map obs =
      lam.withDensity (fun x => ENNReal.ofReal (g i x)))
    (U : I → Set X) (hU : ∀ i, MeasurableSet (U i)) :
    μ {z | obs z ∈ U (code z)} =
      ∑ i, (lam.withDensity (fun x => ENNReal.ofReal (g i x))) (U i) := by
  classical
  have hset : {z | obs z ∈ U (code z)} =
      ⋃ i ∈ (Finset.univ : Finset I), {z | code z = i} ∩ obs ⁻¹' U i := by
    ext z
    constructor
    · intro hz
      exact mem_iUnion.mpr ⟨code z, mem_iUnion.mpr ⟨Finset.mem_univ _, rfl, hz⟩⟩
    · intro hz
      obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      obtain ⟨_, hi, hz⟩ := mem_iUnion.mp hi
      change code z = i at hi
      change obs z ∈ U (code z)
      rw [hi]
      exact hz
  rw [hset, measure_biUnion_finset]
  · apply Finset.sum_congr rfl
    intro i _
    rw [← hlaw i, Measure.map_apply hobs (hU i),
      Measure.restrict_apply (hobs (hU i)), inter_comm]
  · intro i _ j _ hij
    change Disjoint ({z | code z = i} ∩ obs ⁻¹' U i)
      ({z | code z = j} ∩ obs ⁻¹' U j)
    apply disjoint_left.mpr
    intro z hi hj
    change code z = i ∧ obs z ∈ U i at hi
    change code z = j ∧ obs z ∈ U j at hj
    exact hij (hi.1.symm.trans hj.1)
  · intro i _
    exact (hcode i).inter (hobs (hU i))

/-- Summing the original label densities gives an exact coarse observation
law, including its total mass. -/
theorem finite_label_density_law {Z X I : Type*}
    [MeasurableSpace Z] [MeasurableSpace X] [Fintype I]
    (μ : Measure Z) (lam : Measure X) (obs : Z → X) (hobs : Measurable obs)
    (code : Z → I) (hcode : ∀ i, MeasurableSet {z | code z = i})
    (g : I → X → ℝ) (hg : ∀ i, Measurable (g i)) (hg0 : ∀ i x, 0 ≤ g i x)
    (hlaw : ∀ i, (μ.restrict {z | code z = i}).map obs =
      lam.withDensity (fun x => ENNReal.ofReal (g i x))) :
    μ.map obs = lam.withDensity (fun x => ENNReal.ofReal (∑ i, g i x)) := by
  ext U hU
  rw [Measure.map_apply hobs hU]
  change μ {z | obs z ∈ U} = _
  rw [finite_label_source_formula μ lam obs hobs code hcode g hlaw (fun _ => U) (fun _ => hU),
    withDensity_apply _ hU]
  have hsum : (fun x => ENNReal.ofReal (∑ i, g i x)) =
      fun x => ∑ i, ENNReal.ofReal (g i x) := by
    funext x
    exact ENNReal.ofReal_sum_of_nonneg (fun i _ => hg0 i x)
  rw [hsum, lintegral_finsetSum (μ := lam.restrict U)
    (f := fun i x => ENNReal.ofReal (g i x)) Finset.univ
    (fun i _ => ENNReal.measurable_ofReal.comp (hg i))]
  apply Finset.sum_congr rfl
  intro i _
  exact withDensity_apply _ hU

/-- A supplied coarse density and the sum of the label densities need agree
only almost everywhere. -/
theorem finite_label_density_ae {Z X I : Type*}
    [MeasurableSpace Z] [MeasurableSpace X] [Fintype I]
    (μ : Measure Z) (lam : Measure X) [SigmaFinite lam]
    (obs : Z → X) (hobs : Measurable obs)
    (code : Z → I) (hcode : ∀ i, MeasurableSet {z | code z = i})
    (g : I → X → ℝ) (hg : ∀ i, Measurable (g i)) (hg0 : ∀ i x, 0 ≤ g i x)
    (hlaw : ∀ i, (μ.restrict {z | code z = i}).map obs =
      lam.withDensity (fun x => ENNReal.ofReal (g i x)))
    (G : X → ℝ) (hG : Measurable G) (hG0 : ∀ x, 0 ≤ G x)
    (hfull : μ.map obs = lam.withDensity (fun x => ENNReal.ofReal (G x))) :
    ∀ᵐ x ∂lam, G x = ∑ i, g i x := by
  have hsum := finite_label_density_law μ lam obs hobs code hcode g hg hg0 hlaw
  have hm : Measurable (fun x => ∑ i, g i x) := Finset.measurable_sum _ (fun i _ => hg i)
  have heq := (withDensity_eq_iff_of_sigmaFinite
    (ENNReal.measurable_ofReal.comp hG).aemeasurable
    (ENNReal.measurable_ofReal.comp hm).aemeasurable).mp (hfull.symm.trans hsum)
  filter_upwards [heq] with x hx
  exact (ENNReal.ofReal_eq_ofReal_iff (hG0 x)
    (Finset.sum_nonneg (fun i _ => hg0 i x))).mp hx

/-- The same uniqueness statement for an extended-valued coarse density.
In particular, its possible infinite values cause no ambiguity in source
exceptional sets. -/
theorem finite_label_density_ennreal_ae {Z X I : Type*}
    [MeasurableSpace Z] [MeasurableSpace X] [Fintype I]
    (μ : Measure Z) (lam : Measure X) [SigmaFinite lam]
    (obs : Z → X) (hobs : Measurable obs)
    (code : Z → I) (hcode : ∀ i, MeasurableSet {z | code z = i})
    (g : I → X → ℝ) (hg : ∀ i, Measurable (g i)) (hg0 : ∀ i x, 0 ≤ g i x)
    (hlaw : ∀ i, (μ.restrict {z | code z = i}).map obs =
      lam.withDensity (fun x => ENNReal.ofReal (g i x)))
    (G : X → ENNReal) (hG : Measurable G)
    (hfull : μ.map obs = lam.withDensity G) :
    ∀ᵐ x ∂lam, G x = ENNReal.ofReal (∑ i, g i x) := by
  have hsum := finite_label_density_law μ lam obs hobs code hcode g hg hg0 hlaw
  have hm : Measurable (fun x => ∑ i, g i x) := Finset.measurable_sum _ (fun i _ => hg i)
  exact (withDensity_eq_iff_of_sigmaFinite hG.aemeasurable
    (ENNReal.measurable_ofReal.comp hm).aemeasurable).mp (hfull.symm.trans hsum)

/-- The refined-label lower-floor estimate as an exceptional set of the
original source law. The supplied coarse density may be any measurable
representative, and the error has no factor counting the labels. -/
theorem refined_label_source_floor {Z X I : Type*}
    [MeasurableSpace Z] [MeasurableSpace X] [Fintype I]
    (μ : Measure Z) (lam : Measure X) [SigmaFinite lam]
    (obs : Z → X) (hobs : Measurable obs)
    (code : Z → I) (hcode : ∀ i, MeasurableSet {z | code z = i})
    (g h : I → X → ℝ) (hg : ∀ i, Measurable (g i)) (hh : ∀ i, Measurable (h i))
    (hg0 : ∀ i x, 0 ≤ g i x)
    (hlaw : ∀ i, (μ.restrict {z | code z = i}).map obs =
      lam.withDensity (fun x => ENNReal.ofReal (g i x)))
    (G : X → ℝ) (hG : Measurable G) (hG0 : ∀ x, 0 ≤ G x)
    (hfull : μ.map obs = lam.withDensity (fun x => ENNReal.ofReal (G x)))
    (L : X → Finset I) (hmL : ∀ i, MeasurableSet {x | i ∈ L x})
    {R : ℝ} (hR : 0 < R) (hL : ∀ x, ((L x).card : ℝ) ≤ R)
    (hcompat : ∀ᵐ z ∂μ, code z ∈ L (obs z))
    {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) :
    μ {z | ρ ≤ G (obs z) ∧ h (code z) (obs z) < ε * ρ / (2 * R)} ≤
      ENNReal.ofReal ε * μ univ +
        2 * ∑ i, ∫⁻ x, ENNReal.ofReal |g i x - h i x| ∂lam := by
  have hsupp := support_transfer μ lam obs hobs code hcode L hmL g hg hlaw hcompat
  have hsumAE := finite_label_density_ae μ lam obs hobs code hcode g hg hg0 hlaw G hG hG0 hfull
  have hbad : ∀ i, MeasurableSet {x | ρ ≤ G x ∧ h i x < ε * ρ / (2 * R)} :=
    fun i => (measurableSet_le measurable_const hG).inter
      (measurableSet_lt (hh i) measurable_const)
  have hsame (i : I) :
      (lam.withDensity (fun x => ENNReal.ofReal (g i x)))
        {x | ρ ≤ G x ∧ h i x < ε * ρ / (2 * R)} =
      (lam.withDensity (fun x => ENNReal.ofReal (g i x)))
        {x | ρ ≤ ∑ j, g j x ∧ h i x < ε * ρ / (2 * R)} := by
    apply measure_congr
    filter_upwards [(withDensity_absolutelyContinuous lam
      (fun x => ENNReal.ofReal (g i x))).ae_eq hsumAE] with x hx
    simp only [hx]
  have hmass : ∫⁻ x, ENNReal.ofReal (∑ i, g i x) ∂lam = μ univ := by
    have hsum := finite_label_density_law μ lam obs hobs code hcode g hg hg0 hlaw
    calc
      _ = (lam.withDensity (fun x => ENNReal.ofReal (∑ i, g i x))) univ := by
        rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      _ = (μ.map obs) univ := congrArg (fun m : Measure X => m univ) hsum.symm
      _ = μ univ := by rw [Measure.map_apply hobs MeasurableSet.univ, preimage_univ]
  change μ {z | obs z ∈ {x | ρ ≤ G x ∧ h (code z) x < ε * ρ / (2 * R)}} ≤ _
  rw [finite_label_source_formula μ lam obs hobs code hcode g hlaw
    (fun i => {x | ρ ≤ G x ∧ h i x < ε * ρ / (2 * R)}) hbad]
  simp_rw [hsame]
  simpa only [hmass] using refined_label_floor lam g h hg hh hg0 L hR hL hsupp hε hρ

/-- Original-source floor transfer using the extended-valued coarse density
in the frozen problem, without changing its representative. -/
theorem refined_label_source_floor_ennreal {Z X I : Type*}
    [MeasurableSpace Z] [MeasurableSpace X] [Fintype I]
    (μ : Measure Z) (lam : Measure X) [SigmaFinite lam]
    (obs : Z → X) (hobs : Measurable obs)
    (code : Z → I) (hcode : ∀ i, MeasurableSet {z | code z = i})
    (g h : I → X → ℝ) (hg : ∀ i, Measurable (g i)) (hh : ∀ i, Measurable (h i))
    (hg0 : ∀ i x, 0 ≤ g i x)
    (hlaw : ∀ i, (μ.restrict {z | code z = i}).map obs =
      lam.withDensity (fun x => ENNReal.ofReal (g i x)))
    (G : X → ENNReal) (hG : Measurable G)
    (hfull : μ.map obs = lam.withDensity G)
    (L : X → Finset I) (hmL : ∀ i, MeasurableSet {x | i ∈ L x})
    {R : ℝ} (hR : 0 < R) (hL : ∀ x, ((L x).card : ℝ) ≤ R)
    (hcompat : ∀ᵐ z ∂μ, code z ∈ L (obs z))
    {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) :
    μ {z | ENNReal.ofReal ρ ≤ G (obs z) ∧
      h (code z) (obs z) < ε * ρ / (2 * R)} ≤
      ENNReal.ofReal ε * μ univ +
        2 * ∑ i, ∫⁻ x, ENNReal.ofReal |g i x - h i x| ∂lam := by
  have hm : Measurable (fun x => ∑ i, g i x) := Finset.measurable_sum _ (fun i _ => hg i)
  have hsumAE := finite_label_density_ennreal_ae μ lam obs hobs code hcode g hg hg0 hlaw G hG hfull
  have hobsAE : ∀ᵐ x ∂μ.map obs, G x = ENNReal.ofReal (∑ i, g i x) := by
    rw [hfull]
    exact (withDensity_absolutelyContinuous lam G).ae_eq hsumAE
  have hsourceAE : ∀ᵐ z ∂μ, G (obs z) = ENNReal.ofReal (∑ i, g i (obs z)) :=
    (ae_map_iff hobs.aemeasurable
      (measurableSet_eq_fun hG (ENNReal.measurable_ofReal.comp hm))).mp hobsAE
  have hset : μ {z | ENNReal.ofReal ρ ≤ G (obs z) ∧
      h (code z) (obs z) < ε * ρ / (2 * R)} =
      μ {z | ρ ≤ ∑ i, g i (obs z) ∧ h (code z) (obs z) < ε * ρ / (2 * R)} := by
    apply measure_congr
    filter_upwards [hsourceAE] with z hz
    have hnn : 0 ≤ ∑ i, g i (obs z) := Finset.sum_nonneg (fun i _ => hg0 i (obs z))
    simp only [hz, ENNReal.ofReal_le_ofReal_iff hnn]
  rw [hset]
  exact refined_label_source_floor μ lam obs hobs code hcode g h hg hh hg0 hlaw
    (fun x => ∑ i, g i x) hm (fun x => Finset.sum_nonneg (fun i _ => hg0 i x))
    (finite_label_density_law μ lam obs hobs code hcode g hg hg0 hlaw)
    L hmL hR hL hcompat hε hρ

/- Original source-law adapter by x0147, adapted from here:o049, commit b915088,
   Submission/Obl/k4_cap_class_terminal_charts/RefinedSourceCells.lean. -/
open Set MeasureTheory
open scoped ENNReal BigOperators

/-- Good refined observation cells certify their original labelled source
mass. All exceptions are measured in the original source law. -/
theorem refined_original_source_cells {Z X I J : Type*}
    [MeasurableSpace Z] [MeasurableSpace X] [Fintype I]
    (μ : Measure Z) [IsFiniteMeasure μ] (lam : Measure X) [SigmaFinite lam]
    (obs : Z → X) (hobs : Measurable obs)
    (code : Z → I) (hcode : ∀ i, MeasurableSet {z | code z = i})
    (g h : I → X → ℝ) (hg : ∀ i, Measurable (g i)) (hh : ∀ i, Measurable (h i))
    (hg0 : ∀ i x, 0 ≤ g i x)
    (hlaw : ∀ i, (μ.restrict {z | code z = i}).map obs =
      lam.withDensity (fun x => ENNReal.ofReal (g i x)))
    (G : X → ENNReal) (hG : Measurable G) (hfull : μ.map obs = lam.withDensity G)
    (L : X → Finset I) (hmL : ∀ i, MeasurableSet {x | i ∈ L x})
    {R : ℝ} (hR : 0 < R) (hL : ∀ x, ((L x).card : ℝ) ≤ R)
    (hcompat : ∀ᵐ z ∂μ, code z ∈ L (obs z))
    (F : I → Finset J) (C : I → J → Set X)
    (hC : ∀ i j, j ∈ F i → MeasurableSet (C i j))
    (hdisj : ∀ i, (↑(F i) : Set J).PairwiseDisjoint (C i))
    (a v : I → J → ℝ) (hv : ∀ i j, j ∈ F i → 0 ≤ v i j)
    (hvolume : ∀ i j, j ∈ F i → lam (C i j) = ENNReal.ofReal (v i j))
    (hconstant : ∀ i j, j ∈ F i → ∀ x ∈ C i j, h i x = a i j)
    (hcover : ∀ i, (lam.withDensity (fun x => ENNReal.ofReal (g i x)))
      (⋃ j ∈ F i, C i j)ᶜ = 0)
    {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) :
    ∃ Good : I → Finset J,
      (∀ i, Good i ⊆ F i) ∧
      (∀ i j, j ∈ Good i → ENNReal.ofReal (ε * ρ * v i j / (4 * R)) ≤
        μ {z | code z = i ∧ obs z ∈ C i j}) ∧
      μ {z | ENNReal.ofReal ρ ≤ G (obs z) ∧ obs z ∉ ⋃ j ∈ Good (code z), C (code z) j} ≤
        ENNReal.ofReal ε * μ univ +
          3 * ∑ i, ∫⁻ x, ENNReal.ofReal |g i x - h i x| ∂lam := by
  have hfinite (i : I) : IsFiniteMeasure (lam.withDensity (fun x => ENNReal.ofReal (g i x))) := by
    rw [← hlaw i]
    infer_instance
  have hsupp := support_transfer μ lam obs hobs code hcode L hmL g hg hlaw hcompat
  obtain ⟨Good, hGood, hfloor, herr⟩ := refined_original_cell_floors
    lam g h hg hh hg0 hfinite L hR hL hsupp F C hC hdisj a v hv hvolume hconstant hcover hε hρ
  refine ⟨Good, hGood, ?_, ?_⟩
  · intro i j hj
    have heq : (lam.withDensity (fun x => ENNReal.ofReal (g i x))) (C i j) =
        μ {z | code z = i ∧ obs z ∈ C i j} := by
      rw [← hlaw i, Measure.map_apply hobs (hC i j (hGood i hj)),
        Measure.restrict_apply (hobs (hC i j (hGood i hj)))]
      congr 1
      ext z
      change (obs z ∈ C i j ∧ code z = i) ↔ (code z = i ∧ obs z ∈ C i j)
      exact and_comm
    rw [← heq]
    exact hfloor i j hj
  · have hsumAE := finite_label_density_ennreal_ae μ lam obs hobs code hcode g hg hg0 hlaw G hG hfull
    have hbad (i : I) : MeasurableSet {x | ENNReal.ofReal ρ ≤ G x ∧ x ∉ ⋃ j ∈ Good i, C i j} := by
      have hgood : MeasurableSet (⋃ j ∈ Good i, C i j) :=
        MeasurableSet.biUnion (Good i).countable_toSet (fun j hj => hC i j (hGood i hj))
      exact (measurableSet_le measurable_const hG).inter hgood.compl
    have hsame (i : I) :
        (lam.withDensity (fun x => ENNReal.ofReal (g i x)))
          {x | ENNReal.ofReal ρ ≤ G x ∧ x ∉ ⋃ j ∈ Good i, C i j} =
        (lam.withDensity (fun x => ENNReal.ofReal (g i x)))
          {x | ρ ≤ ∑ j, g j x ∧ x ∉ ⋃ j ∈ Good i, C i j} := by
      apply measure_congr
      filter_upwards [(withDensity_absolutelyContinuous lam
        (fun x => ENNReal.ofReal (g i x))).ae_eq hsumAE] with x hx
      have hnn : 0 ≤ ∑ i, g i x := Finset.sum_nonneg (fun i _ => hg0 i x)
      simp only [hx, ENNReal.ofReal_le_ofReal_iff hnn]
    have hmass : ∫⁻ x, ENNReal.ofReal (∑ i, g i x) ∂lam = μ univ := by
      have hsum := finite_label_density_law μ lam obs hobs code hcode g hg hg0 hlaw
      calc
        _ = (lam.withDensity (fun x => ENNReal.ofReal (∑ i, g i x))) univ := by
          rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
        _ = (μ.map obs) univ := congrArg (fun m : Measure X => m univ) hsum.symm
        _ = μ univ := by rw [Measure.map_apply hobs MeasurableSet.univ, preimage_univ]
    change μ {z | obs z ∈ {x | ENNReal.ofReal ρ ≤ G x ∧
      x ∉ ⋃ j ∈ Good (code z), C (code z) j}} ≤ _
    rw [finite_label_source_formula μ lam obs hobs code hcode g hlaw
      (fun i => {x | ENNReal.ofReal ρ ≤ G x ∧ x ∉ ⋃ j ∈ Good i, C i j}) hbad]
    simp_rw [hsame]
    simpa only [hmass] using herr

end Submission.Lib.K4RefinedLabelFloors
