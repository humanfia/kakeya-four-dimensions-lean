import Submission.Obl.k4_pair_bin_atlas_assembly.AnchorParameters
import Submission.Obl.k4_pair_bin_atlas_assembly.SafeAveraging

namespace Submission.Obl.k4_pair_bin_atlas_assembly

open Set MeasureTheory
open scoped ENNReal

/-- One anchor and detour work simultaneously for the finite original family,
after an error charged to the existing observation lists. -/
theorem exists_list_safe_anchor {X ι : Type*}
    [MeasurableSpace X] [Fintype ι]
    (μ : ι → Measure X) [∀ i, SFinite (μ i)]
    (H : ι → Set X) (hH : ∀ i, MeasurableSet (H i))
    (hfinite : ∀ i, μ i (H i) ≠ ∞)
    (w : ι → ℝ≥0∞) (hw : ∀ i, w i ≠ ∞)
    (P : ι → MvPolynomial (Fin 3) ℝ)
    (z : ι → X → EuclideanSpace ℝ (Fin 3)) (hz : ∀ i, Measurable (z i))
    (lst : ι → X → Finset ι)
    (hlst : ∀ i j, MeasurableSet {x | j ∈ lst i x})
    (K : ℕ) (hK : ∀ i, ∀ x ∈ H i, (lst i x).card ≤ K)
    (ρ lower : ℝ) (η : ℝ≥0∞)
    (hprob : ∀ i, ∀ x ∈ H i, ∀ j ∈ lst i x,
      lower ≤ |MvPolynomial.eval (fun n => z i x n) (P j)| →
      anchorLaw {θ | ¬ SafeFor ρ (P i) (P j) (z i x) θ.1 θ.2} ≤ η) :
    ∃ θ ∈ anchorDomain, ∃ G : ι → Set X,
      (∀ i, MeasurableSet (G i)) ∧ (∀ i, G i ⊆ H i) ∧
      (∀ i, ∀ x ∈ G i, ∀ j ∈ lst i x,
        lower ≤ |MvPolynomial.eval (fun n => z i x n) (P j)| →
        SafeFor ρ (P i) (P j) (z i x) θ.1 θ.2) ∧
      (∑ i, w i * μ i (H i)) ≤ (∑ i, w i * μ i (G i)) +
        (K : ℝ≥0∞) * η * (∑ i, w i * μ i (H i)) := by
  classical
  haveI := anchorLaw_probability
  let L : ι → X → Finset ι := fun i x => (lst i x).filter
    (fun j => lower ≤ |MvPolynomial.eval (fun n => z i x n) (P j)|)
  have hL (i j : ι) : MeasurableSet {x | j ∈ L i x} := by
    have hc : Continuous (fun v : EuclideanSpace ℝ (Fin 3) =>
        |MvPolynomial.eval (fun n => v n) (P j)|) :=
      ((MvPolynomial.continuous_eval (P j)).comp (by fun_prop)).abs
    have heq : {x | j ∈ L i x} = {x | j ∈ lst i x} ∩
        {x | lower ≤ |MvPolynomial.eval (fun n => z i x n) (P j)|} := by
      ext x
      simp only [L, Finset.mem_filter, mem_ofPred_eq, mem_inter_iff]
    rw [heq]
    exact (hlst i j).inter (measurableSet_le measurable_const (hc.measurable.comp (hz i)))
  let bad : ι → ι → Set (AnchorParameter × X) := fun i j =>
    {p | ¬ SafeFor ρ (P i) (P j) (z i p.2) p.1.1 p.1.2}
  have hbad (i j : ι) : MeasurableSet (bad i j) := by
    have hsnd : Measurable (Prod.snd : AnchorParameter × X → X) := measurable_snd
    have hfst : Measurable (Prod.fst : AnchorParameter × X → AnchorParameter) := measurable_fst
    have hf : Measurable (fun p : AnchorParameter × X => (z i p.2, p.1)) :=
      ((hz i).comp hsnd).prodMk hfst
    change MeasurableSet ((fun p : AnchorParameter × X => (z i p.2, p.1)) ⁻¹'
      {p : EuclideanSpace ℝ (Fin 3) × AnchorParameter |
        ¬ SafeFor ρ (P i) (P j) p.1 p.2.1 p.2.2})
    exact (measurableSet_unsafe ρ (P i) (P j)).preimage hf
  let E : ι → Set (AnchorParameter × X) := fun i =>
    {p | p.2 ∈ H i ∧ ∃ j ∈ L i p.2, p ∈ bad i j}
  have hE (i : ι) : MeasurableSet (E i) :=
    measurableSet_bad_list (H i) (hH i) (L i) (hL i) (bad i) (hbad i)
  have hEsub (i : ι) : E i ⊆ univ ×ˢ H i := fun _ hp => ⟨mem_univ _, hp.1⟩
  have hEvol (i : ι) : (anchorLaw.prod (μ i)) (E i) ≤
      (K : ℝ≥0∞) * η * μ i (H i) := by
    apply parameter_bad_list_le anchorLaw (μ i) (H i) (hH i) (L i) (hL i)
      (bad i) (hbad i) K η
    · intro x hx
      exact (Finset.card_filter_le _ _).trans (hK i x hx)
    · intro x hx j hj
      obtain ⟨hjlst, hjval⟩ := Finset.mem_filter.mp hj
      exact hprob i x hx j hjlst hjval
  have he : (∑ i, w i * (anchorLaw.prod (μ i)) (E i)) ≤
      (K : ℝ≥0∞) * η * (∑ i, w i * μ i (H i)) := by
    calc
      _ ≤ ∑ i, w i * ((K : ℝ≥0∞) * η * μ i (H i)) := by
        apply Finset.sum_le_sum
        intro i _
        gcongr
        exact hEvol i
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ac_rfl
  obtain ⟨θ, hθ, hm⟩ := exists_parameter_good_weighted_mass anchorLaw μ H hH hfinite
    w hw E hE hEsub _ he anchorDomain anchorLaw_outside
  let G : ι → Set X := fun i => H i \ Prod.mk θ ⁻¹' E i
  refine ⟨θ, hθ, G, ?_, (fun i => sdiff_subset), ?_, hm⟩
  · intro i
    exact (hH i).diff ((hE i).preimage measurable_prodMk_left)
  · intro i x hx j hj hjval
    by_contra hunsafe
    apply hx.2
    exact ⟨hx.1, j, Finset.mem_filter.mpr ⟨hj, hjval⟩, hunsafe⟩

end Submission.Obl.k4_pair_bin_atlas_assembly
