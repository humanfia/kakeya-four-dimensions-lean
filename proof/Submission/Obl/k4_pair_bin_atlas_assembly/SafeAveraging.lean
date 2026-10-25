import Mathlib

namespace Submission.Obl.k4_pair_bin_atlas_assembly

open Set MeasureTheory
open scoped ENNReal

theorem measurableSet_bad_list {Θ X ι : Type*}
    [MeasurableSpace Θ] [MeasurableSpace X] [Fintype ι]
    (H : Set X) (hH : MeasurableSet H)
    (lst : X → Finset ι) (hlst : ∀ i, MeasurableSet {x | i ∈ lst x})
    (bad : ι → Set (Θ × X)) (hbad : ∀ i, MeasurableSet (bad i)) :
    MeasurableSet {p : Θ × X | p.2 ∈ H ∧ ∃ i ∈ lst p.2, p ∈ bad i} := by
  have heq : {p : Θ × X | p.2 ∈ H ∧ ∃ i ∈ lst p.2, p ∈ bad i} =
      (Prod.snd ⁻¹' H) ∩ ⋃ i, (Prod.snd ⁻¹' {x | i ∈ lst x}) ∩ bad i := by
    ext p
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_iUnion]
  rw [heq]
  exact (hH.preimage measurable_snd).inter
    (MeasurableSet.iUnion fun i => (hlst i |>.preimage measurable_snd).inter (hbad i))

/-- A union over the observation list costs its cardinality, rather than the
number of possible witnesses in the whole family. -/
theorem parameter_bad_list_le {Θ X ι : Type*}
    [MeasurableSpace Θ] [MeasurableSpace X] [Fintype ι]
    (π : Measure Θ) (μ : Measure X) [SFinite π] [SFinite μ]
    (H : Set X) (hH : MeasurableSet H)
    (lst : X → Finset ι) (hlst : ∀ i, MeasurableSet {x | i ∈ lst x})
    (bad : ι → Set (Θ × X)) (hbad : ∀ i, MeasurableSet (bad i))
    (K : ℕ) (η : ℝ≥0∞) (hK : ∀ x ∈ H, (lst x).card ≤ K)
    (hfiber : ∀ x ∈ H, ∀ i ∈ lst x,
      π ((fun θ => (θ, x)) ⁻¹' bad i) ≤ η) :
    (π.prod μ) {p | p.2 ∈ H ∧ ∃ i ∈ lst p.2, p ∈ bad i} ≤
      (K : ℝ≥0∞) * η * μ H := by
  classical
  let E : Set (Θ × X) := {p | p.2 ∈ H ∧ ∃ i ∈ lst p.2, p ∈ bad i}
  have hE : MeasurableSet E := measurableSet_bad_list H hH lst hlst bad hbad
  have hpoint (x : X) : π ((fun θ => (θ, x)) ⁻¹' E) ≤
      H.indicator (fun _ => (K : ℝ≥0∞) * η) x := by
    by_cases hx : x ∈ H
    · rw [indicator_of_mem hx]
      have heq : (fun θ => (θ, x)) ⁻¹' E =
          ⋃ i ∈ lst x, (fun θ => (θ, x)) ⁻¹' bad i := by
        ext θ
        simp only [E, mem_preimage, mem_ofPred_eq, mem_iUnion, hx, true_and]
        simp only [exists_prop]
      rw [heq]
      calc
        _ ≤ ∑ i ∈ lst x, π ((fun θ => (θ, x)) ⁻¹' bad i) :=
          measure_biUnion_finset_le _ _
        _ ≤ ∑ _i ∈ lst x, η := Finset.sum_le_sum fun i hi => hfiber x hx i hi
        _ = ((lst x).card : ℝ≥0∞) * η := by simp
        _ ≤ (K : ℝ≥0∞) * η := by
          gcongr
          exact_mod_cast hK x hx
    · rw [indicator_of_notMem hx]
      have hempty : (fun θ => (θ, x)) ⁻¹' E = ∅ := by
        ext θ
        simp only [mem_preimage, E, mem_ofPred_eq, hx, false_and, mem_empty_iff_false]
      rw [hempty, measure_empty]
  calc
    _ = ∫⁻ x, π ((fun θ => (θ, x)) ⁻¹' E) ∂μ := Measure.prod_apply_symm hE
    _ ≤ ∫⁻ x, H.indicator (fun _ => (K : ℝ≥0∞) * η) x ∂μ := lintegral_mono hpoint
    _ = _ := by rw [lintegral_indicator hH]; simp

/-- One admissible parameter retains the averaged successful mass, up to the
integrated bad-list error. The original law stays unnormalized. -/
theorem exists_parameter_good_mass {Θ X : Type*}
    [MeasurableSpace Θ] [MeasurableSpace X]
    (π : Measure Θ) (μ : Measure X) [IsProbabilityMeasure π] [SFinite μ]
    (H : Set X) (hH : MeasurableSet H) (hfinite : μ H ≠ ∞)
    (E : Set (Θ × X)) (hE : MeasurableSet E)
    (hsub : E ⊆ univ ×ˢ H) (e : ℝ≥0∞) (he : (π.prod μ) E ≤ e)
    (U : Set Θ) (hU : π Uᶜ = 0) :
    ∃ θ ∈ U, μ H ≤ μ (H \ Prod.mk θ ⁻¹' E) + e := by
  let G : Set (Θ × X) := (univ ×ˢ H) \ E
  have hG : MeasurableSet G := (MeasurableSet.univ.prod hH).diff hE
  have hGfinite : (π.prod μ) G ≠ ∞ := by
    apply ne_of_lt
    calc
      _ ≤ (π.prod μ) (univ ×ˢ H) := measure_mono sdiff_subset
      _ = μ H := by simp
      _ < ∞ := lt_top_iff_ne_top.mpr hfinite
  have hmass : μ H ≤ (π.prod μ) G + e := by
    calc
      _ = (π.prod μ) (univ ×ˢ H) := by simp
      _ = (π.prod μ) G + (π.prod μ) E :=
        (by simpa only [G, inter_eq_right.mpr hsub] using
          (measure_sdiff_add_inter (μ := π.prod μ) (univ ×ˢ H) hE).symm)
      _ ≤ _ := add_le_add le_rfl he
  have hintegral : (∫⁻ θ, μ (Prod.mk θ ⁻¹' G) ∂π) < ∞ := by
    rw [← Measure.prod_apply hG]
    exact lt_top_iff_ne_top.mpr hGfinite
  obtain ⟨θ, hθ, hθmass⟩ := exists_notMem_null_lintegral_le (ne_of_lt hintegral) hU
  refine ⟨θ, by simpa using hθ, ?_⟩
  have hsection : Prod.mk θ ⁻¹' G = H \ Prod.mk θ ⁻¹' E := by
    ext x
    simp only [G, mem_preimage, mem_sdiff, mem_prod, mem_univ, true_and]
  rw [hsection] at hθmass
  exact hmass.trans (add_le_add ((Measure.prod_apply hG).trans_le hθmass) le_rfl)

/-- Finite original weighted laws commute with averaging the common anchor. -/
theorem lintegral_weighted_sections {Θ X ι : Type*}
    [MeasurableSpace Θ] [MeasurableSpace X] [Fintype ι]
    (π : Measure Θ) (μ : ι → Measure X) [∀ i, SFinite (μ i)]
    (G : ι → Set (Θ × X)) (hG : ∀ i, MeasurableSet (G i))
    (w : ι → ℝ≥0∞) :
    (∫⁻ θ, ∑ i, w i * μ i (Prod.mk θ ⁻¹' G i) ∂π) =
      ∑ i, w i * (π.prod (μ i)) (G i) := by
  classical
  rw [lintegral_finsetSum Finset.univ (fun i _ =>
    (measurable_measure_prodMk_left (hG i)).const_mul (w i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [lintegral_const_mul _ (measurable_measure_prodMk_left (hG i)),
    ← Measure.prod_apply (hG i)]

/-- Freeze one common parameter for a finite family of original laws. -/
theorem exists_parameter_good_weighted_mass {Θ X ι : Type*}
    [MeasurableSpace Θ] [MeasurableSpace X] [Fintype ι]
    (π : Measure Θ) [IsProbabilityMeasure π]
    (μ : ι → Measure X) [∀ i, SFinite (μ i)]
    (H : ι → Set X) (hH : ∀ i, MeasurableSet (H i))
    (hfinite : ∀ i, μ i (H i) ≠ ∞)
    (w : ι → ℝ≥0∞) (hw : ∀ i, w i ≠ ∞)
    (E : ι → Set (Θ × X)) (hE : ∀ i, MeasurableSet (E i))
    (hsub : ∀ i, E i ⊆ univ ×ˢ H i)
    (e : ℝ≥0∞) (he : (∑ i, w i * (π.prod (μ i)) (E i)) ≤ e)
    (U : Set Θ) (hU : π Uᶜ = 0) :
    ∃ θ ∈ U, (∑ i, w i * μ i (H i)) ≤
      (∑ i, w i * μ i (H i \ Prod.mk θ ⁻¹' E i)) + e := by
  classical
  let G : ι → Set (Θ × X) := fun i => (univ ×ˢ H i) \ E i
  have hG (i : ι) : MeasurableSet (G i) :=
    (MeasurableSet.univ.prod (hH i)).diff (hE i)
  have hpoint (θ : Θ) : (∑ i, w i * μ i (Prod.mk θ ⁻¹' G i)) ≤
      ∑ i, w i * μ i (H i) := by
    apply Finset.sum_le_sum
    intro i _
    gcongr
    exact fun _ hx => hx.1.2
  have htotal : (∑ i, w i * μ i (H i)) ≠ ∞ :=
    ENNReal.sum_ne_top.mpr fun i _ => ENNReal.mul_ne_top (hw i) (hfinite i)
  have hint : (∫⁻ θ, ∑ i, w i * μ i (Prod.mk θ ⁻¹' G i) ∂π) ≠ ∞ := by
    apply ne_of_lt
    calc
      _ ≤ ∫⁻ _θ, (∑ i, w i * μ i (H i)) ∂π := lintegral_mono hpoint
      _ = ∑ i, w i * μ i (H i) := by simp
      _ < ∞ := lt_top_iff_ne_top.mpr htotal
  obtain ⟨θ, hθ, hm⟩ := exists_notMem_null_lintegral_le hint hU
  refine ⟨θ, by simpa using hθ, ?_⟩
  have hmass : (∑ i, w i * μ i (H i)) ≤
      (∑ i, w i * (π.prod (μ i)) (G i)) + e := by
    calc
      _ = ∑ i, w i * ((π.prod (μ i)) (G i) + (π.prod (μ i)) (E i)) := by
        apply Finset.sum_congr rfl
        intro i _
        congr 1
        simpa only [G, inter_eq_right.mpr (hsub i), Measure.prod_prod,
          measure_univ, one_mul] using
          (measure_sdiff_add_inter (μ := π.prod (μ i)) (univ ×ˢ H i) (hE i)).symm
      _ = (∑ i, w i * (π.prod (μ i)) (G i)) +
          ∑ i, w i * (π.prod (μ i)) (E i) := by
        simp_rw [mul_add, Finset.sum_add_distrib]
      _ ≤ _ := add_le_add le_rfl he
  have heq (i : ι) : Prod.mk θ ⁻¹' G i = H i \ Prod.mk θ ⁻¹' E i := by
    ext x
    simp only [G, mem_preimage, mem_sdiff, mem_prod, mem_univ, true_and]
  rw [lintegral_weighted_sections π μ G hG w] at hm
  simp_rw [heq] at hm
  exact hmass.trans (add_le_add hm le_rfl)

end Submission.Obl.k4_pair_bin_atlas_assembly
