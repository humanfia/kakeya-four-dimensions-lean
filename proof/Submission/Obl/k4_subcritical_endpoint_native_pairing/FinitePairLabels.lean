/- Adapted from this LOT tree, obligation o218, session x0764, commit e1e41f8e737fdc1974cfdf32d18bbf69838b3ce8,
   Submission/Obl/k4_horizontal_endpoint_wide_return/FinitePairLabels.lean.
   Original source attributions are retained below. -/
import Submission.Obl.k4_critical_conditional_row_preparation.Pruning

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing

open Set MeasureTheory

/-- A finite cover which is unique almost everywhere has measurable labels
with EXACTLY the original fiber laws. Closed time-block endpoints cost no mass. -/
theorem exists_measurable_pair_labels {Ω ι : Type*} [MeasurableSpace Ω]
    [MeasurableSpace ι] [Fintype ι] [Nonempty ι]
    (μ : Measure Ω) (E : ι → Set Ω) (hE : ∀ i, MeasurableSet (E i))
    (hunique : ∀ᵐ p ∂μ, ∀ i j, p ∈ E i → p ∈ E j → i = j)
    (hcover : ∀ᵐ p ∂μ, ∃ i, p ∈ E i) :
    ∃ f : Ω → ι, Measurable f ∧
      (∀ᵐ p ∂μ, ∀ i, f p = i ↔ p ∈ E i) ∧
      ∀ i, μ.restrict {p | f p = i} = μ.restrict (E i) := by
  classical
  let G : Set Ω := {p | ∀ i j, p ∈ E i → p ∈ E j → i = j}
  have hG : MeasurableSet G := by
    dsimp only [G]
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro j
    by_cases hij : i = j
    · simp only [hij, implies_true, ofPred_true, MeasurableSet.univ]
    · have heq : {p | p ∈ E i → p ∈ E j → i = j} = (E i ∩ E j)ᶜ := by
        ext p
        simp only [mem_ofPred_eq, mem_compl_iff, mem_inter_iff]
        tauto
      rw [heq]
      exact ((hE i).inter (hE j)).compl
  let E' : ι → Set Ω := fun i => E i ∩ G
  have hE' : ∀ i, MeasurableSet (E' i) := fun i => (hE i).inter hG
  have hdisj : Pairwise (fun i j => Disjoint (E' i) (E' j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro p hpi hpj
    exact hij (hpi.2 i j hpi.1 hpj.1)
  let i₀ : ι := Classical.choice inferInstance
  let f : Ω → ι := fun p =>
    (Submission.Obl.k4_critical_conditional_row_preparation.coverLabel E' p).getD i₀
  have hmap : Measurable[⊤] (fun i : Option ι => i.getD i₀) := measurable_from_top
  have hf : Measurable f := hmap.comp
    (Submission.Obl.k4_critical_conditional_row_preparation.measurable_coverLabel E' hE' hdisj)
  have hae : ∀ᵐ p ∂μ, ∀ i, f p = i ↔ p ∈ E i := by
    filter_upwards [hunique, hcover] with p hp hc
    obtain ⟨i, hi⟩ := hc
    have hsome := (Submission.Obl.k4_critical_conditional_row_preparation.coverLabel_eq_some
      E' hdisj p i).mpr ⟨hi, hp⟩
    have hfi : f p = i := by simp only [f, hsome, Option.getD_some]
    intro j
    rw [hfi]
    exact ⟨fun hij => hij ▸ hi, fun hj => hp i j hi hj⟩
  refine ⟨f, hf, hae, ?_⟩
  intro i
  apply Measure.restrict_congr_set
  filter_upwards [hae] with p hp
  exact propext (hp i)

end Submission.Obl.k4_subcritical_endpoint_native_pairing
